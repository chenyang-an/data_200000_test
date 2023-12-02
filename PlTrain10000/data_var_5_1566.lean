variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261032670792808793580038285055 : ((p4 → p2) → ((p4 → ((p3 → (p3 → (False ∧ (p4 ∨ (p4 → p1))))) → (p3 → p2))) → (((False ∨ ((False ∧ p5) → p2)) → p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ ((False ∧ p5) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218492057910690958081679069289 : (((p1 ∨ False) → (p3 ∧ p4)) → ((((p4 → False) ∧ p5) ∨ True) ∨ (((False → True) → (False → p4)) → (((p3 ∨ (p1 → True)) ∧ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42847213814125928017165460566 : (((p2 → ((p3 → ((p5 ∨ (False → p5)) → ((p3 → (True ∧ p2)) → ((False ∨ True) ∧ (p1 → ((p2 ∧ p3) ∧ p4)))))) ∨ True)) ∨ p2) ∨ p5) := by
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
theorem thm_5_vars_179413921267190651023570500341 : ((p4 ∨ (((p3 ∧ p3) ∨ (False ∨ (((p2 → True) ∧ p1) → p2))) ∨ p4)) ∨ (True ∨ (p3 ∨ (True ∧ (False ∧ ((p5 ∧ p4) → (p5 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356491749608322769797622084938 : (p5 → ((((False ∧ ((p1 ∧ False) ∨ (p4 ∧ p2))) ∨ True) ∨ False) ∧ (p2 → ((p5 ∨ ((p1 → (True ∧ p4)) ∧ p4)) ∨ ((p4 ∨ p1) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261194110405327783148073784756 : ((p4 → p5) → (((True → (p1 ∨ (((p5 ∨ p2) ∨ p1) ∧ ((p3 ∨ p3) ∨ True)))) ∨ (((p2 → p5) ∧ p5) ∧ ((False ∧ p4) ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41236153035752057038476656514 : ((((False ∨ (((((p4 ∧ ((p4 ∧ ((p1 → p1) → p4)) ∨ p1)) ∨ False) ∨ p3) ∨ p1) ∨ p2)) ∧ (p3 ∧ ((p5 ∨ p4) → p4))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165585943146199123151347637531 : (((p2 ∨ (False ∧ (p5 ∨ (p2 ∧ (p4 ∧ p4))))) ∨ ((p2 → (False → (p4 ∧ True))) ∧ True)) ∨ ((True ∨ ((True ∧ False) ∧ (False → True))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71721706940255651446095038052 : (((p3 ∧ ((((((((True ∧ p1) ∧ p3) → True) → (p3 ∧ p5)) ∨ p3) ∧ (((p1 ∨ (p4 → p1)) ∧ p2) ∨ p2)) ∨ p4) → False)) ∧ p2) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((((((True ∧ p1) ∧ p3) → True) → (p3 ∧ p5)) ∨ p3) ∧ (((p1 ∨ (p4 → p1)) ∧ p2) ∨ p2)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126022871436288950322812440475 : (((p1 → p3) → ((True ∨ False) → (((((p1 ∧ (True ∧ (p2 ∨ (p4 ∧ p5)))) ∨ p4) ∧ (p1 → p4)) → (p3 → True)) ∨ False))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157047932573667456500247670189 : (((p1 ∧ ((True ∧ (p1 ∨ ((p5 → True) ∨ (p3 ∨ p1)))) → (True → ((p2 → p5) → p3)))) ∨ True) ∨ ((p3 → ((p5 ∧ p2) ∨ p5)) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615789121661990331643719525079 : ((((((p2 ∧ (p3 ∨ (p5 ∧ ((p2 ∧ (False → (False ∨ p1))) ∧ p1)))) ∧ True) ∨ ((p1 ∨ True) ∧ ((p5 ∨ (p3 → p2)) → p4))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_339983441912451571686208702059 : (p1 → (p1 → ((((p4 → ((p1 ∧ (p2 ∨ ((p3 ∧ p3) ∨ (p1 ∨ p2)))) ∧ (p1 ∧ p5))) → p4) ∨ (p4 → p1)) → ((p5 ∧ p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691249251145913002370909201176 : (((((((p4 ∧ p2) ∨ p4) ∧ p4) ∨ (((p3 ∨ ((True ∧ p1) → p3)) ∨ p4) → False)) → (p3 → (p4 ∧ ((True → p3) → (p4 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358583864652155346604941426852 : (p5 → (p3 → ((p2 ∨ (((p2 ∧ (p1 → p5)) → ((p1 ∧ (p2 ∨ (True ∧ ((p1 ∨ (p2 ∨ p1)) ∧ False)))) ∧ (p3 ∧ p4))) ∨ p3)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761883280052570623022356830143 : (((p3 ∧ ((((False → p5) ∧ ((p1 ∨ (((False ∧ (p3 → p3)) ∧ ((False ∨ p1) → p4)) ∨ p1)) → p3)) ∨ ((p3 ∧ True) ∧ p5)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210663646899813074054860940456 : ((((p2 → p3) ∨ p2) → True) ∧ ((((p1 ∧ ((p5 ∨ False) ∧ ((p5 → p2) ∨ p2))) ∧ p3) ∨ True) ∨ (p4 ∧ (p2 ∨ ((p1 ∨ p1) ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117234240759947156327905007398 : ((True ∧ (p2 ∧ (p1 ∧ (((p1 ∨ True) ∨ (True ∧ ((False → ((False → p2) ∨ True)) ∨ p3))) ∧ ((p3 ∨ (True ∧ p1)) ∨ True))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707308315737311431224561494399 : ((((((False ∨ (p3 ∧ p5)) ∨ p1) ∨ (p2 → p1)) ∨ ((False ∧ p2) → ((False → p5) ∨ (p1 → ((p5 → ((p1 ∧ True) → p5)) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174933512611061405563358860948 : (((p1 → p3) → ((((((p4 → p2) ∧ False) → p2) → (True → p5)) ∨ p5) ∨ p1)) → ((False ∨ p3) → ((False ∧ ((p3 ∧ False) ∧ False)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128490857604563068269893553275 : ((p5 → ((p5 → ((((p4 ∧ (p2 ∧ p1)) ∨ p4) → False) ∨ p2)) ∧ (p1 ∧ (p1 → (((p1 ∧ p4) → (p1 ∨ p1)) ∨ p1))))) → (p5 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184254633984552952207211156675 : ((((p5 → (p1 ∧ (True ∧ ((p2 ∧ p4) → p3)))) → p3) → p1) ∨ ((p4 → (((p5 ∨ False) ∧ p4) ∨ (p3 ∨ (p5 ∧ True)))) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768755077240875508376569338502 : (((p5 ∧ ((((p5 ∧ p2) → ((p1 ∨ p3) ∨ p3)) ∨ p5) ∨ ((False ∨ p1) → ((p1 → ((p5 ∧ p4) ∧ p3)) ∨ ((p3 ∧ False) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134871758125189989118418569870 : (((p1 → ((p3 → False) ∨ ((p5 ∨ ((((p4 → p1) ∧ True) ∨ (p1 → p3)) → p4)) ∨ ((p1 → p3) → p3)))) → p4) ∨ (p1 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48961699437246921591136476924 : ((((((False → ((p2 ∨ False) → (p1 ∧ False))) → (p4 → ((((p2 ∨ p1) ∨ True) ∧ p4) → p5))) ∧ False) ∨ True) ∨ (False ∧ (p3 ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134366130359404480758027206998 : (((p1 ∨ (False ∨ (((p5 → ((p3 → p5) → (p4 → (p1 ∧ (p5 ∧ (False ∧ (True ∧ p5))))))) ∧ False) ∧ True))) ∨ False) ∨ (True ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42054167927404210217911751822 : ((((p2 ∨ False) ∨ ((p5 ∨ p2) → (((((p1 ∧ p5) ∧ (False ∨ False)) ∨ p2) ∨ (p5 → ((p4 → p4) → (p1 → p3)))) ∨ p1))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180998143964808438718791973250 : (((p5 ∧ True) ∨ (p5 ∨ (((p3 ∧ (True → False)) ∨ p4) → (False ∧ True)))) → ((p4 → False) ∨ (p5 ∧ ((p2 ∧ ((p2 ∧ False) ∧ p5)) → p2)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h22
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h23 : ((p3 ∧ (True → False)) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h24 := h21 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427742046749159828379554695968 : ((((((((True → (False → (p1 → p4))) → ((p5 → p5) ∧ ((p1 → p2) ∨ (p2 ∧ True)))) ∨ p2) ∨ (True → p4)) ∨ p1) ∨ (True ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56179787086832633460278891240 : (((p3 ∧ ((p2 ∧ p4) ∨ p2)) ∨ ((((False → (p1 ∨ p3)) ∨ (True → p4)) → ((p1 → (((p3 ∧ p4) ∧ p2) → p4)) ∧ p4)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304155039587777786178156921083 : (p1 ∨ ((((p3 ∨ True) ∧ ((p1 ∧ (True ∧ (((p2 ∨ (((p3 ∧ False) ∧ p3) → (p3 ∧ (p3 → p1)))) ∨ True) → False))) ∧ p4)) ∧ p4) → p2)) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : ((p2 ∨ (((p3 ∧ False) ∧ p3) → (p3 ∧ (p3 → p1)))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : ((p2 ∨ (((p3 ∧ False) ∧ p3) → (p3 ∧ (p3 → p1)))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244279349226610556134974330353 : ((False ∧ True) ∨ ((p2 ∨ (False → p4)) ∧ (p5 ∨ ((((False ∨ p3) ∧ True) ∧ p2) ∨ (p5 → ((False → (p5 ∨ p3)) → ((False ∧ p5) ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323817498443974239061799420946 : (p5 ∨ (((p1 → ((p5 ∧ (p3 ∨ (p5 → (p5 ∧ (True ∨ p2))))) → (False ∨ (False ∨ p4)))) ∧ p1) → (p5 ∨ (True → ((p5 → False) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299168819749444203226776766980 : (False ∨ ((((((((False ∧ p4) → ((False → p1) ∧ p5)) ∧ (p1 ∨ p2)) ∧ False) ∧ ((p4 ∧ ((False ∨ p2) → p5)) → p4)) → False) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47122264658876576042223450836 : (((((((True ∧ p3) → p4) ∨ ((((p3 ∧ (p2 → (p5 ∧ p2))) ∨ p2) → p3) → True)) ∧ p2) → (p3 ∨ (False ∧ p4))) ∨ (True ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206327495525729656916983210751 : ((p1 ∨ (p4 ∨ (p3 ∨ (p5 ∨ False)))) ∨ ((p3 ∧ ((p4 ∨ False) ∨ (((False → ((((p2 ∨ p4) ∨ p1) → True) ∧ p5)) → p1) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143054500813120691921409700200 : ((False → ((False → (p1 ∨ ((p3 ∨ (False ∨ True)) ∧ (p4 ∧ (((p4 ∨ p1) ∨ p2) → (False → p1)))))) ∨ (False ∧ p1))) → ((p5 → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63892934929143876052043284053 : ((False ∨ (((((((False ∨ p4) → (p5 → True)) ∨ ((((False → False) → p2) ∨ (p5 ∨ p1)) ∨ True)) → p2) ∧ False) ∨ (True ∨ True)) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_2698575740656212887371778870 : (((p1 ∨ p1) ∧ (p5 → (True ∧ p2))) → ((((False → p2) ∧ p2) → ((((True → p3) → False) → (True ∧ (True ∨ p4))) → p3)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116990006559474968503791307835 : (((True ∨ True) → (((p5 → p3) → p4) → (p5 ∧ (((False → (p2 ∨ (((False ∧ (p2 ∨ p2)) ∨ True) ∧ p2))) ∨ p2) → p4)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205865664796136034285965870787 : (((p5 → p3) → (p5 ∨ (False ∨ p1))) ∨ (p3 → (((((False ∨ p2) ∧ p1) → p2) ∨ True) ∨ (((p3 ∧ p5) → p3) ∧ (True ∧ (p2 → p5)))))) := by
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
theorem thm_5_vars_695099171179249016675564077351 : (((((((p1 ∨ (p4 ∧ p3)) ∧ (p5 ∧ (False ∨ (p2 ∨ p4)))) ∨ p1) ∨ p1) → ((p3 ∧ (p5 → (False ∨ (p2 ∧ p1)))) ∨ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247286085770844293376437890115 : ((False ∨ False) ∨ ((((p4 → ((True ∧ ((p1 ∨ True) ∨ p5)) → ((True ∨ (p1 → (False → p5))) → False))) ∧ (p4 ∧ p3)) ∨ (p2 → p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68744072629548561422220761978 : ((p4 → ((((p3 ∨ p4) → ((p3 → (False ∧ p5)) → (False ∧ (p5 ∨ (p3 ∨ p2))))) ∧ p4) ∨ ((False → (p1 ∧ (p2 ∨ p2))) ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_805550890494250217727132505727 : (((p3 → (p5 ∨ ((False ∨ ((p5 ∧ ((((((False ∨ p2) ∧ ((True ∧ p1) ∨ p3)) ∨ p5) ∨ p5) ∧ (p3 ∨ p3)) ∨ False)) → p1)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234700152723842132056313848885 : ((p4 → (False ∨ False)) → (p3 ∨ (((((((False ∧ p3) ∨ (p4 ∨ p1)) ∨ p2) ∧ p5) ∧ (p5 ∨ p4)) ∨ (p5 → ((p4 ∨ False) ∨ True))) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150699953246271438569866597704 : (((((((((p5 ∧ p3) → (True ∨ (p2 ∨ (p4 ∧ p4)))) ∧ (p2 → p5)) ∨ p2) ∨ True) ∧ p1) ∧ True) ∨ p3) → ((p5 ∨ (p1 ∨ p4)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
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
theorem thm_5_vars_3030801281154589843209949003 : ((p4 ∧ (p5 ∨ True)) → ((p2 ∨ p4) ∧ ((p5 → p2) ∨ ((p3 → (p1 ∧ (False ∧ ((p5 ∨ True) ∨ (p2 ∨ p1))))) → (p1 ∨ True))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157405997850103299420395942869 : (((((((p5 → p5) ∧ p2) → False) → ((False ∨ p2) ∨ False)) ∧ (p3 → (p5 → p4))) ∧ (p2 → True)) ∨ ((p5 ∨ (True ∨ (p1 ∨ p2))) ∨ p2)) := by
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
theorem thm_5_vars_66035891113317873838930319725 : ((p5 ∨ ((p1 ∧ ((((p4 ∨ (p4 ∧ (True ∨ p1))) ∧ ((p5 → (((p4 ∧ False) ∨ True) ∧ (p4 ∧ p1))) ∧ p3)) → p3) → p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68860527970698670237257365625 : ((p4 → ((True → False) → (p5 ∨ (False ∧ ((((p2 ∨ (p5 ∨ ((p2 ∨ p4) → p1))) ∧ p1) ∨ p5) → (p2 → ((p3 ∨ p4) ∨ p3))))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168751938823399056608657084472 : ((False ∨ (p1 ∧ (((p3 ∨ ((p5 → (p2 ∧ True)) ∨ (p1 ∧ True))) → (False → p4)) ∨ p5))) → ((False ∧ (p3 → (False ∨ (p5 ∨ p4)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114810408751534666541130721953 : ((((False → (True ∨ p1)) → (((p3 → p4) → True) → ((p2 ∧ p5) ∧ False))) ∧ (p4 ∧ (((p4 ∨ p5) → True) ∨ (p2 ∨ p1)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902574847926446889008153912657 : (((((((p1 → True) → p4) → (False ∧ p1)) ∧ (p1 ∨ ((((True ∨ p4) → True) ∧ p3) → (False → p4)))) ∧ ((p3 ∧ p3) ∧ (True ∧ p4))) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : ((p1 → True) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h22 := h4 h20
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111145769249915856242390644593 : ((((p1 → (p4 ∧ ((p2 ∨ True) ∧ p3))) ∧ (((((p1 ∧ ((p5 ∨ p4) ∧ (True → p3))) → p5) → True) → p3) ∧ p3)) ∧ p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50594519568127740754821858922 : ((((((p3 → p1) → p4) ∨ (p3 ∨ (p2 ∨ ((p5 → ((True → p3) ∧ p5)) → p3)))) ∧ (p3 ∧ p1)) → (((p4 → p2) → p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146933489061664002292857271267 : ((((((p4 → ((p5 ∨ p1) → (p4 ∨ p4))) ∧ ((p4 ∧ p5) ∨ ((p4 ∨ p3) → p4))) ∧ p3) ∨ p2) ∧ p1) ∨ (True ∧ ((False → p5) ∨ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300105405871587211787251661728 : (False ∨ (((((p1 ∨ ((p1 ∧ p1) ∧ False)) ∨ (False ∨ (p3 ∨ p5))) → p1) ∨ ((p4 ∧ p4) → (((p2 ∧ False) ∨ p2) ∨ False))) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112408657498302851612659654544 : ((((p3 ∧ ((((True ∨ p5) ∨ (False → (((((p1 → p5) ∨ False) ∧ (p2 → p4)) → p1) → p3))) ∨ p2) ∨ p1)) ∧ p4) → p5) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48990114786222267056522810849 : (((((p4 ∨ True) → ((p2 → (p4 ∧ ((True → ((p1 → p2) → p4)) ∧ ((p3 ∨ p1) ∨ p1)))) ∧ p3)) ∨ p2) ∨ ((False ∧ p1) → p2)) ∨ False) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198201681318769609121158202356 : (((p3 → True) → ((p2 → False) ∧ (False ∧ False))) ∨ (((p3 ∧ p3) ∨ (p5 ∨ (((p1 → (p3 ∨ (p3 ∨ p4))) → p3) ∧ p1))) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57989336653005665799783349003 : (((p5 → (True ∧ p1)) → (((p1 ∨ (((True ∨ True) ∧ ((p5 → ((((p5 ∨ p2) ∨ p5) → True) → True)) ∧ p3)) ∨ p1)) ∧ p2) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42302707850318849392194740711 : (((p2 ∧ (((p4 ∧ p4) ∨ ((p1 ∧ (((p3 → p3) → False) ∧ ((p2 ∧ True) ∧ (p5 → False)))) ∨ (p2 → p5))) → (p3 → False))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323896819076958053399702298108 : (p5 ∨ (((p4 ∧ (False ∧ ((p5 ∨ True) ∧ (p2 ∧ (True ∧ False))))) ∧ (True ∧ (p1 ∧ p2))) ∨ ((False ∨ False) → (((p1 → p1) ∨ p3) → p3)))) := by
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
    cases h1
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112840007284264331933178998946 : ((((p4 ∨ (True → (p3 ∧ p5))) → ((False ∧ (p4 → (p5 → ((p2 ∧ (p5 ∧ (p2 → p5))) ∧ p1)))) ∨ (p5 ∧ p1))) → p4) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112382184148718600011508797240 : ((((((p5 → True) → (((p5 ∨ p2) ∨ (p2 ∧ (p2 ∧ False))) ∧ (p3 → p1))) ∨ ((p2 → (p3 → p2)) → p1)) ∧ p5) → False) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57287566040853269579699087547 : ((((p1 → True) → False) ∨ ((((((False ∧ (False ∧ p2)) ∨ (p3 ∨ (p4 ∧ (p2 ∧ p2)))) ∨ (False ∧ False)) → p1) ∨ (p5 ∨ p5)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48962507453882132286919345808 : (((((False ∧ ((((p2 ∨ ((p5 → (p3 → True)) ∨ p5)) → p5) ∧ (p1 ∨ p3)) ∧ (p1 → False))) ∧ p2) ∨ p2) ∨ ((p1 → p3) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117511507727138985318632114971 : ((p2 ∧ (((p5 ∧ (p3 ∨ (((((p2 → False) ∧ p5) → (((False ∧ p4) ∨ (False ∨ False)) → p5)) ∧ True) ∨ p1))) → p3) ∨ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601534857097822418232105366219 : ((((p3 ∧ ((((p3 → (p4 ∨ ((False → (p2 ∨ p3)) → p2))) → ((p4 ∧ (p3 ∨ p3)) ∨ False)) ∨ True) ∨ ((p3 → p1) ∨ False))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49212780471409441738983922588 : ((((p2 ∧ p4) ∧ ((((p1 ∨ p2) → (((((p5 → p2) ∨ (p5 ∧ False)) → p2) ∧ p5) ∨ p2)) ∧ p5) ∧ False)) ∨ (p4 ∧ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316499527767172035528537377024 : (p3 ∨ (p2 ∨ ((((p1 ∨ (p2 ∨ p5)) ∨ p4) → ((p2 → (p4 ∨ ((True ∨ p2) ∨ ((p1 → p5) ∧ False)))) ∨ (True ∨ False))) ∨ (True → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_217715985709661400026473180810 : (((False ∧ (False → p5)) → p3) → (p1 → ((((((p5 → (p3 ∨ p4)) → p4) ∨ ((False → (True → (p1 ∨ p3))) ∧ p3)) ∨ True) ∧ p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607855947650143504191805487863 : (((((p5 ∨ ((p5 → False) ∨ (p2 ∧ ((((False → True) ∨ (p2 ∧ (((p3 ∨ (p4 ∧ False)) → p4) → p2))) → p2) ∧ p5)))) ∧ p2) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_229532876260885813162108817233 : ((p2 → (p5 ∨ p1)) ∨ ((p2 ∨ ((p4 ∨ (True → (((p5 ∧ p4) ∨ ((p3 ∨ True) ∨ False)) ∨ (p3 ∧ (p4 ∧ p4))))) ∨ p3)) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_546908054601490964742455938542 : (((False ∨ ((((p2 ∧ (((((p4 → (p2 ∨ p3)) ∨ False) ∧ (p1 ∨ False)) → (((p2 ∨ p1) ∨ p4) → p1)) ∨ p4)) → p4) ∨ p5) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147262456081534550398397876292 : ((((((((p5 → p3) ∧ ((p2 → p1) ∧ ((p5 ∨ p2) ∨ p4))) ∨ (p5 ∧ p3)) ∨ p3) ∨ p1) ∨ p5) ∨ p4) ∨ (((p4 → p1) ∧ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58491701453891221781393185820 : (((p4 ∨ p2) ∧ (((True ∨ (((((p4 ∧ (p3 ∨ p4)) ∧ True) ∧ p4) → False) ∧ p1)) → (p4 ∧ True)) ∧ (True ∨ (p1 → (p1 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157282055875419863158683099647 : ((((p2 ∨ p2) ∧ ((((p1 → (p4 ∨ (p1 ∨ p3))) ∨ False) ∧ ((True ∧ p1) → False)) ∧ p3)) → p5) ∨ (((p4 ∧ (p2 ∨ p1)) ∧ p1) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105974473010107840315874704455 : (((p4 → (((p3 ∧ ((False ∨ (p3 ∨ (p4 → False))) ∧ False)) ∨ False) ∧ p2)) ∨ (False ∨ ((True → (p4 → p3)) → (p3 → p3)))) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49286752070844130990887885558 : (((p5 ∧ ((((((True ∨ p1) → p4) ∧ (p2 ∨ (p1 → p1))) ∨ (False ∨ p4)) ∨ ((False ∧ p4) ∨ p2)) → False)) ∨ (True ∨ (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261198136726138200991906230674 : ((p4 → p5) → (((((((p1 ∧ (p5 → ((((p2 ∨ False) ∧ (p1 ∧ p1)) → True) ∧ p3))) ∨ (False → p3)) ∧ True) ∧ p1) ∨ True) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p1 ∧ (p5 → ((((p2 ∨ False) ∧ (p1 ∧ p1)) → True) ∧ p3))) ∨ (False → p3)) ∧ True) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135805818982518408948584166018 : (((p4 ∨ ((p1 → ((False ∧ (p5 → (p5 ∨ True))) ∨ False)) ∨ (p3 → p3))) → ((p5 ∧ (p1 ∧ (p5 ∨ p5))) ∨ p4)) ∨ (p4 → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180629792031022784597274003075 : (((((p2 ∨ (False ∧ False)) ∧ p5) ∧ p4) ∨ (p5 ∧ (True ∧ (p4 → p3)))) → ((p3 ∨ False) → (((p3 → p4) ∨ ((False → p4) ∧ True)) ∨ p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730847544100988343505923235376 : ((((p5 ∧ (p2 ∨ p5)) → ((((((p5 → True) ∨ (((p5 → ((p2 ∧ p1) ∧ (True → False))) → p5) ∧ p5)) ∧ p3) ∧ p1) → False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762400336615066511163518845065 : (((p3 ∧ (((p4 → p2) ∧ ((((((True → p5) ∧ True) ∨ p1) ∨ p5) → (p2 ∧ (p3 → p4))) ∨ (p3 ∨ False))) → (p1 ∨ (p5 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673956766961749591404084327292 : ((((True ∧ ((True ∨ (p4 ∨ (p4 ∨ (p2 ∧ (p1 → (((True → True) ∨ p1) ∨ p3)))))) ∨ (p4 ∨ (p2 ∧ p2)))) → (p3 ∨ (False → p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171934747316935856648375566658 : ((((False → ((p4 ∧ ((False ∧ True) ∨ p2)) → (p2 → False))) ∨ p4) ∧ (p5 ∨ p5)) ∨ (((((p3 ∧ p2) ∨ p5) ∨ p1) ∨ True) ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158071709632912191801635824793 : ((((((p2 ∧ p4) ∨ False) → p4) → False) → (((False ∧ p3) ∨ (p5 ∧ p5)) ∧ (p1 ∨ (p1 ∧ True)))) ∨ (p3 ∧ (p4 → ((p2 ∧ False) → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ p4) ∨ False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((p2 ∧ p4) ∨ False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h9
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643197006572880138998888331391 : ((((p3 ∧ ((((p1 → ((p4 ∨ p2) → p5)) ∧ p3) → (((((p3 ∧ True) ∨ p2) → p5) ∨ True) ∧ p5)) ∨ (p4 → (p3 → False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60676439301227483622757546594 : ((True ∧ ((p3 ∧ (p4 ∧ (((True → p5) ∨ ((p1 ∨ False) → False)) ∧ (p5 ∧ True)))) ∧ ((p2 → ((p3 ∨ (p3 ∨ p3)) ∧ p1)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48632232002616081614296881974 : (((((True → (False ∨ (p3 → p3))) ∧ (False ∧ ((p2 ∨ ((p5 ∨ True) ∨ p2)) → True))) ∨ ((p5 → p3) → p3)) ∧ (False ∧ (p1 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40884388205765279741795862822 : ((((((((p3 → (True ∨ p2)) ∧ p2) → True) → (p1 → (True ∧ p3))) → ((p1 ∧ (p3 ∨ p3)) ∨ (True ∧ p3))) ∧ (p4 ∧ False)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748289673351964058789555997181 : ((((p2 → False) → (False ∧ ((p1 ∧ ((((((p5 → (p5 ∨ False)) ∧ p5) ∨ p3) → p1) ∨ (True ∨ (False ∨ p1))) ∧ p3)) ∨ (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105484854689964932211856474655 : ((((p3 ∧ (p4 → p2)) ∨ (p2 ∨ (p3 → ((p2 → (True → (p4 → (p5 → p1)))) ∨ p4)))) ∨ (((False ∧ p3) ∨ p3) ∨ True)) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40669689730176630724129213069 : (((((True ∧ (False ∧ ((((False ∨ p4) ∧ (p3 ∧ (p1 → p4))) ∧ ((p5 ∧ p1) → True)) ∧ (p4 ∧ p1)))) → (p2 ∧ p3)) → p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178761018228441957162482698403 : ((((p2 → p3) ∨ p4) ∧ ((p3 → p2) ∨ ((p5 ∧ p4) ∧ (False ∧ p2)))) ∨ ((False → (p4 ∧ (True → (((True ∧ p1) ∧ False) ∧ p5)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136348951449161896280200055933 : (((True → ((p2 ∧ p5) ∨ p3)) ∧ ((False ∨ (((False → p5) ∧ ((False ∨ (p3 → (True → p2))) ∨ p4)) ∨ False)) → p1)) ∨ (p3 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254727504989454189989162679883 : ((p3 ∧ p3) → ((False ∨ p3) ∧ (p4 → ((True ∧ (((((p5 ∧ (((p2 → p5) ∨ p4) ∧ (p5 ∨ True))) ∧ p3) ∧ p3) ∧ p5) ∧ p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63070617214026101384904926041 : ((p5 ∧ ((((p4 ∧ ((p4 ∨ p4) ∧ (((False ∧ p4) ∨ (((((p4 ∨ p1) ∧ p2) → p5) ∧ p3) → True)) → p4))) ∨ p2) ∧ p3) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



