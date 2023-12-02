variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327477526435457724933389265653 : (True → ((((True → False) ∧ ((p5 → True) ∧ p3)) ∧ (False → ((True ∨ (p4 ∨ ((p5 ∨ (p1 ∧ False)) ∧ ((True ∨ p1) → p4)))) → p2))) → p1)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217451361012281216142516273489 : (((p4 → (False → p4)) ∨ False) → ((((p3 → ((p5 ∨ ((p2 → p2) ∧ True)) → False)) ∧ ((p1 → p2) → False)) ∨ True) ∧ (True ∨ (False ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171147888974009227291309403673 : ((p1 → ((p4 ∨ (((((p4 ∨ p3) ∧ p3) ∧ p4) ∧ True) ∨ (False → True))) ∨ p3)) ∧ ((p2 ∨ p1) → (False → ((p1 → p5) → (p3 ∧ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57848236183112391588746011586 : (((True ∨ (p3 ∧ p2)) → ((((((p5 → p3) → True) → p1) ∨ (p1 ∨ (p2 ∧ (p4 → (p5 ∨ p3))))) → (p2 ∨ (p1 ∨ p3))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147773551644126602176948261323 : ((((True ∨ True) ∨ (((((True ∨ (p5 ∨ p2)) ∧ (True ∧ True)) ∧ p3) ∨ p5) ∧ ((p3 → p2) → p3))) → p2) ∨ (p5 → ((p1 ∧ p2) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356520959596205723019547269492 : (p5 → (((p1 → (p3 → (p1 ∧ (True ∨ (p1 → True))))) ∧ p2) ∨ ((((p1 → p1) → (p4 → ((p1 → p2) ∧ False))) ∧ (True → True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56058800023715040340512613013 : (((((p4 → p5) ∨ p3) → p1) ∨ (p4 ∨ ((((p1 ∧ False) ∨ True) ∧ (((p5 → True) ∧ p5) ∧ ((False → p5) ∧ p4))) ∨ (p3 ∨ True)))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658426630407450825461817947440 : ((((p1 ∨ ((((p4 ∧ p1) ∨ True) ∧ ((False ∧ p2) ∨ ((((p3 ∧ (False → p1)) ∨ p3) ∨ False) ∧ (p5 ∧ p3)))) ∧ False)) ∨ (p2 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_138327383269612618028527669640 : ((p3 → (p1 ∨ (p2 ∨ (((p4 ∨ (p4 ∨ (p4 ∨ p5))) ∧ (False → (p2 ∨ False))) → (((p3 → p4) ∧ p2) ∨ True))))) ∨ (p2 ∧ (p2 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67931564882548948734368597141 : ((p2 → ((((((p2 → p1) ∧ True) ∨ p3) ∧ p1) ∧ False) ∨ (((((p4 ∨ False) → (p4 ∧ p4)) → p3) ∧ p3) ∨ ((False → True) ∧ True)))) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227770145539202291804713895032 : ((p1 ∧ (True → p4)) ∨ (p4 → (((((p5 ∧ ((((p1 ∨ (p5 → (False ∨ p2))) ∧ p2) ∧ True) ∨ (p5 → p2))) ∨ p4) ∨ p2) ∧ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61591342137303276378914609076 : ((p1 ∧ ((p3 → (p3 ∨ p4)) ∧ ((p1 ∧ (p4 ∨ ((p4 ∨ (p3 ∨ False)) → p2))) → ((p4 ∨ (p1 → ((p1 ∧ p2) → p5))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114426278083703439537632743599 : (((p2 ∧ (((((((p3 ∨ (p5 → p4)) ∧ (p1 → p4)) ∨ p4) ∧ p1) ∨ True) ∨ p2) ∨ p2)) ∨ (p2 → ((True ∨ False) ∧ p1))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773420656688990302025371718457 : (((False ∨ (((((True → False) ∨ p4) ∨ ((p2 ∧ (((p1 ∧ ((False ∧ p5) ∨ True)) → False) ∧ ((p5 ∨ False) ∨ True))) → p5)) ∧ p1) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264279747203333131294931254648 : (True ∧ ((p5 ∧ (((True → p1) ∨ p5) ∨ p5)) ∨ ((((False ∧ p4) ∨ False) → True) → ((p3 → False) ∨ ((p3 ∧ False) → (True → (p2 ∧ p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68206838397257659997740542248 : ((p3 → ((p5 ∨ (False ∧ (((p4 ∧ ((p1 ∧ (((False → p4) → p1) → ((p4 → p5) ∧ False))) ∨ (p2 → p4))) ∧ p5) ∨ p1))) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197273538883288403452801016257 : ((((p4 → (p1 ∧ p2)) ∧ (p3 → True)) → False) ∨ ((((((p1 ∨ (p5 ∧ p1)) ∧ True) → True) ∧ (p4 ∨ (True ∨ p4))) ∨ False) ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347483092382076147618142744614 : (p3 → (((p2 ∨ (False ∧ p2)) ∨ (p2 ∧ p1)) ∨ ((((((p3 ∧ (((p4 → p4) ∨ p4) → p5)) ∧ p3) ∧ (p2 ∧ p5)) ∧ True) ∧ p1) → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h8.left
  let h14 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329558520490605229431071100435 : (True → ((p1 ∨ p1) ∨ (((p5 ∧ (p2 ∨ p5)) ∨ True) ∨ ((p4 ∧ p2) ∨ ((False ∨ ((p3 ∧ ((p5 ∨ (True ∧ True)) ∧ True)) → p3)) ∧ False))))) := by
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
theorem thm_5_vars_205288756215576531162838802295 : (((p2 ∧ (p2 ∧ p1)) ∨ (True ∧ p5)) ∨ (((True ∧ p5) → p3) → (p5 ∨ (False → (((p5 → (((p1 ∧ p1) ∧ p1) → p1)) → False) → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807193074409550284919286167106 : (((p4 → ((True → ((((p1 → (p3 ∨ p5)) ∨ ((p3 → p2) → True)) ∧ (p3 ∧ p5)) ∧ p5)) ∨ ((p1 → ((p1 ∨ False) → True)) → True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230838238762502786318312854648 : (((p1 ∧ True) ∨ p2) → (((p2 ∨ p2) ∧ ((p5 → ((p1 → (p5 ∨ p3)) → p2)) → (((p5 ∧ True) ∨ (True ∨ False)) ∨ p4))) ∨ (p4 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43180399276479624911723576878 : (((((p3 → p2) ∧ ((((((True ∧ p5) ∧ p2) ∨ (p2 ∨ (True ∧ p2))) ∨ ((p1 ∧ True) ∧ (False ∧ p5))) ∨ False) → True)) ∧ True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688370374530385075831317799329 : ((((False ∧ ((p2 ∨ ((p3 ∧ False) ∧ (((p2 ∧ True) ∨ p3) ∧ p3))) ∨ (False → p2))) ∧ (p5 → (((p4 → p1) ∨ False) ∨ (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329184058472025821313449904493 : (True → ((False → ((p2 ∧ p1) ∧ p5)) → (p2 → (((((((p1 → p1) ∧ (p5 → ((p5 ∧ p4) ∧ p3))) ∧ True) ∧ True) → p5) ∨ p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246524375889239587755505528471 : ((p5 ∧ p1) ∨ ((p3 → (p1 ∨ (p3 ∨ True))) ∧ (False ∨ (p1 ∨ (False → ((p2 ∨ (False ∨ (((p2 ∧ p3) → (p1 ∧ p2)) ∧ False))) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305697649199354469449518075497 : (p1 ∨ (((((((p1 ∨ p3) ∨ False) ∧ True) ∧ p3) ∧ False) ∨ p2) → ((p1 ∨ (((p4 ∧ (p3 → p3)) ∧ (p3 ∨ p1)) ∨ (p2 ∧ True))) ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h4
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167467735842456829406274233418 : (((p3 → (((((p3 ∨ p2) → ((False ∧ p1) ∧ p5)) ∧ (False ∨ p2)) ∨ False) ∨ p5)) → p1) → ((p4 ∨ ((p1 ∧ p5) ∧ (p5 ∧ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179849894723546342478153212732 : (((p3 ∨ (p1 → (((p4 ∧ p1) ∧ (p4 ∧ (False → p4))) ∧ p2))) ∧ p4) → ((p4 → (p2 ∧ p5)) ∨ ((True → ((p1 ∨ p1) ∧ p1)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83321456507407628861763420742 : ((((((p1 ∨ (p1 ∨ False)) ∧ p4) ∨ p5) → (False → (p3 → (p4 → (p4 ∧ (False ∨ p4)))))) ∧ (((p1 → p1) ∨ p5) → (p1 ∧ False))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 → p1) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140244305710306993520746639573 : (((p2 → ((((p1 → p4) ∧ ((p5 → True) ∨ (p1 ∧ (p5 → p3)))) ∧ p1) → ((True ∨ p3) ∧ p1))) → (False ∨ p4)) → ((p1 ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((((p1 → p4) ∧ ((p5 → True) ∨ (p1 ∧ (p5 → p3)))) ∧ p1) → ((True ∨ p3) ∧ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157505417684948794343395343292 : ((((p4 → p2) → ((False ∨ ((True ∨ p1) ∧ False)) ∧ ((p4 ∨ (False → p1)) ∨ p1))) ∨ (False ∨ False)) ∨ ((False → p4) ∨ (p1 → (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204703287624817441382730919419 : (((p4 ∨ (p2 ∧ (p5 → True))) ∨ p3) ∨ ((p2 → (p2 ∨ ((p2 ∧ p2) ∧ (p1 ∧ ((True → p1) ∨ p2))))) → ((p3 → (p1 → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254332132290984559716316825817 : ((p2 ∧ p4) → ((((True → (p4 ∧ p4)) ∧ p3) ∧ ((((p2 ∨ ((p5 → (False ∨ p5)) → (p3 ∧ p4))) ∧ p3) → p4) → (True → p5))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217494494931704855993128866298 : ((((True ∨ p5) ∧ p5) → p2) → ((p5 ∨ (p1 ∨ (False ∧ (p1 → p3)))) ∨ (((False → False) ∨ ((p1 ∧ p3) → (True ∨ p2))) ∨ (p2 ∧ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54466853931559539573710569597 : ((((((True ∨ p5) ∧ p3) ∧ p5) ∧ (p5 → True)) ∨ ((((((p2 ∨ p4) ∨ p2) ∨ (True ∧ (p3 ∨ p1))) ∨ True) ∨ (False ∧ p4)) ∨ False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_115016187545963212372764843908 : (((p1 ∧ ((p1 ∧ (False → (p3 → ((False ∧ p1) ∨ p4)))) → p1)) ∧ (((True → (p2 ∨ False)) ∧ False) ∨ ((p3 ∧ p2) ∧ False))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40539345932938895496940569813 : ((((p3 ∨ (True → ((p4 → (((False ∨ ((False ∧ p3) ∧ ((p2 ∨ True) ∨ (p2 → False)))) ∨ (p5 ∧ p2)) ∨ p4)) → p3))) ∨ True) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718565666036997059422372590688 : (((((p3 → (p3 → p1)) → False) ∨ ((p3 ∧ True) → (False ∨ (((p2 ∨ True) → True) → (True → ((p2 ∨ (p1 ∨ p2)) → (p3 ∧ True))))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116457744544248011110307427071 : (((True ∧ p4) ∧ (((False ∧ p4) ∧ (p3 ∧ p3)) ∨ ((p5 → (p3 ∨ ((p3 ∨ p1) → (p3 → True)))) → ((p2 → True) ∧ p3)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777202910812969135972368037853 : (((p1 ∨ ((True → (((p5 → False) ∧ ((((p5 → ((p4 ∨ p5) → p4)) ∨ True) ∧ False) → p4)) → (p1 → p4))) ∧ (p5 ∧ (p5 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148265283526688753872246460423 : (((True → ((p1 → ((((p4 ∧ (p4 ∨ p1)) ∧ (False ∧ True)) ∨ p2) ∧ p3)) ∧ p4)) ∨ (p1 → (p1 ∨ False))) ∨ ((p3 ∧ (False → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306263379792950518774969998784 : (p1 ∨ ((False → (p3 ∧ True)) → (((False ∨ False) ∧ (p4 ∧ ((p5 ∨ False) → True))) ∨ ((p3 ∨ (p2 → (False ∧ True))) → (p1 ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303480525412466375213623050367 : (p1 ∨ (((((p1 ∨ (p1 → (p3 ∨ p5))) → (p1 → (p5 → p1))) ∨ (p5 → p3)) → (((p2 → True) → False) → (p5 ∧ (p5 ∨ p4)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h12
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h18 := h2 h16
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49889412178955271964328573076 : (((((p2 ∨ ((p3 ∨ False) ∧ (p2 → p1))) → ((((True ∨ True) ∨ True) ∧ p2) ∧ (p2 ∨ p5))) ∨ p1) ∧ (((False → False) ∧ True) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57133486017287209127553562152 : ((((p1 → True) ∧ p3) ∨ ((((((((p3 ∨ p2) ∨ p4) ∧ p2) ∧ True) ∨ (p5 ∨ p4)) ∨ (p3 ∧ p2)) ∨ ((p1 ∨ True) ∨ False)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656310332350029531997652431364 : ((((((((p3 ∨ True) → p4) ∨ ((True ∧ p1) ∨ p5)) ∨ (p2 ∨ p4)) ∨ (p2 ∧ ((p3 ∧ (p4 ∧ False)) → (p1 ∨ False)))) ∨ (False ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145297667923956391838404499580 : ((((p3 ∧ (p1 ∨ (p2 ∧ p1))) ∨ False) ∨ ((p1 ∨ (p3 ∧ False)) → (((True ∨ p2) ∧ p2) ∨ (False → p1)))) ∧ (((True ∨ False) ∨ p1) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148550589958103563934574628922 : ((((p3 → (((p1 ∧ p4) ∨ (False ∧ p4)) → p2)) ∨ p1) ∧ (p2 → (True → ((p1 ∧ (True ∧ p3)) ∨ p1)))) ∨ (True ∨ (True → (p5 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185943352881184039884320424926 : ((((p4 → False) ∧ (p3 ∧ (((p5 ∨ p3) → False) → p4))) ∧ p2) → ((p1 → (p1 ∨ (p3 ∧ p5))) ∧ (p4 → ((p4 ∧ (p2 ∧ p1)) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- One of the premise coincides with the conclusion.
  exact h17
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
  have h28 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h24, we can now drive its conclusion.
  let h29 := h24 h28
  -- False on the left can always be used.
  apply False.elim h29
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h33.left
  let h35 := h33.right
  -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
  have h36 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h32, we can now drive its conclusion.
  let h37 := h32 h36
  -- False on the left can always be used.
  apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260287309161506394660187224851 : ((p2 → p4) → (((((True → (p3 ∧ (p3 ∨ (p4 → ((p2 ∨ True) ∧ (p1 ∨ (p4 → False))))))) ∨ (False → True)) ∨ (p5 ∨ p5)) → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True → (p3 ∧ (p3 ∨ (p4 → ((p2 ∨ True) ∧ (p1 ∨ (p4 → False))))))) ∨ (False → True)) ∨ (p5 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136645317806511551884444257218 : ((((p3 ∨ p1) → p2) → (((((p4 ∨ p5) ∨ True) ∧ (p4 → p2)) ∨ True) ∧ (p1 → (p5 ∨ ((p1 → p1) ∧ True))))) ∨ (p2 → (p1 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792906733708677906689887668530 : (((True → ((False ∧ p1) ∧ ((p3 → (p3 ∧ True)) → (p4 ∧ (((((p2 → p4) ∧ True) ∨ p4) ∧ (p1 ∨ (False ∨ (p2 → p3)))) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736169193074326897909194233272 : ((((False → False) ∧ (p5 ∧ (p4 → ((((p3 ∨ (p1 ∧ (((p3 ∧ True) → p3) → (p3 → p3)))) ∨ (False ∧ p4)) ∧ p4) ∨ (p4 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314948107081858147127827261842 : (p3 ∨ ((((p4 → ((p2 → p4) ∧ p5)) ∧ (True ∨ p4)) → p5) → (((p5 ∨ True) ∧ (p1 → p3)) ∨ (((p4 → p1) → (p4 → p1)) ∨ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245249226633454284152274348500 : ((p2 ∧ p1) ∨ (((p1 ∨ (p5 ∨ p3)) ∨ True) ∨ ((p5 → (((p4 ∨ p2) ∨ (p3 ∨ p1)) ∧ ((p5 → p3) ∨ p2))) → ((p3 ∨ p3) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313061888533171254693965356055 : (p3 ∨ (((False ∨ ((p2 ∨ p4) → ((p4 ∨ (((p2 → (p4 → (True → False))) ∧ True) ∨ (p1 ∧ p4))) ∨ (p1 ∨ (p4 → p4))))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37406006026264634643760937285 : (((((((((((p4 ∧ p2) → p2) ∧ (True ∨ (p3 ∧ (p3 ∨ (True → p4))))) ∨ p4) ∧ p1) → p4) ∧ p1) ∨ (p2 → True)) ∨ p1) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54432447864245343328126267096 : (((((p4 → p4) → (p5 ∧ (p5 ∨ p1))) ∨ p1) ∨ ((((p3 ∧ True) → p4) ∧ ((p5 → (p4 → (p2 ∧ (p1 → True)))) ∨ True)) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610623398527200296723158627975 : (((((((p1 ∨ ((p1 → (p5 → p4)) → (False → ((((True ∨ p5) → True) ∧ p5) ∨ (p2 ∧ p3))))) ∨ False) → (p2 → p2)) → p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139579139104524990762408797497 : ((((((p5 ∨ True) ∨ ((((((p2 ∨ p5) ∧ p1) ∨ p1) ∨ p2) ∨ p2) ∧ p3)) ∨ p4) → (p1 ∧ (False ∧ p1))) → p4) → ((p2 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38198257173342253900899503020 : ((((((p1 → False) → (p1 → (((False ∧ p1) ∨ p4) → ((p5 → (True ∧ p3)) → (p2 → p4))))) ∨ True) → ((p4 → p3) → False)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179486833045982596751280172545 : ((True → ((p5 → False) ∨ ((p1 ∧ (False ∨ p1)) ∧ (p5 ∧ (True → p4))))) ∨ ((p2 → ((p3 ∨ (((False → False) ∨ p1) ∨ False)) ∨ p2)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256409206833296509017597697042 : ((False ∨ p3) → (((p4 → p4) ∧ ((p3 → True) → (((((False → ((p2 ∧ (p2 → p3)) ∨ p1)) ∧ False) ∧ False) ∧ True) ∧ True))) → (p1 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h19 := h14 h17
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622989464508250745871471195123 : ((((p5 ∧ ((False ∧ True) ∧ ((True ∧ p2) ∧ (((True ∧ p3) ∧ (p2 → p5)) → (False ∧ (((p2 ∨ True) ∨ p1) ∨ (True → p1))))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60003083497489254872942055192 : (((False ∨ p5) → ((((((p4 → False) ∨ ((((True → False) ∧ (p5 → ((False → False) → p3))) → p1) ∨ False)) ∨ p3) → True) ∧ p1) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9864276696263651523022150066 : (((False ∧ (((((p5 ∧ p3) ∧ p1) ∨ (p4 ∧ ((p5 ∨ p4) → ((True ∨ p4) ∨ (p1 ∨ False))))) ∨ p1) → ((False → p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717122604351343996344384017977 : ((((False ∨ (p1 ∧ (p3 ∧ True))) ∧ ((p1 ∧ p5) ∧ (p2 ∨ (((p5 ∧ (p2 → (((p4 → p5) → True) ∨ (p1 → p3)))) → True) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342007077574765870061661530790 : (p2 → ((True ∧ (((p4 → (True ∨ p1)) ∧ p3) ∨ ((True → ((p2 → (False ∧ p4)) → p3)) → ((p3 ∧ p5) ∨ False)))) ∨ (True ∧ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226739839497126043994606781297 : (((p1 ∧ p5) → p3) ∨ ((p2 ∨ ((p1 ∨ ((((True ∧ p2) ∨ p1) ∨ p5) ∨ (p4 ∧ (p2 ∨ p3)))) ∨ (True → True))) ∨ (p4 ∧ (p2 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184805604723991281462054305891 : (((p5 ∨ ((p4 ∧ p2) ∧ p1)) ∨ (((p5 ∧ p1) ∨ p4) ∨ p4)) ∨ ((p3 ∧ False) → (True → ((p5 → True) ∧ ((True → True) ∧ (p5 → p4)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645870463330736676199345026121 : ((((True → ((True → ((((p5 → (False ∧ p1)) ∧ ((((False ∧ p5) ∧ p4) ∧ (p1 ∧ p1)) ∧ p1)) ∧ p4) → (p3 → p2))) ∧ p2)) → p2) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172731818882132270098591964473 : (((p2 → p4) ∨ (((p2 → p2) → (True ∨ p5)) ∧ (p4 ∧ (False ∨ (p2 → False))))) ∨ ((False ∨ (((p2 ∨ p3) ∧ p4) ∨ (p5 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55780167190291510142505843115 : ((((p3 → False) ∧ (p4 → p5)) ∧ ((p5 ∧ p4) → ((False ∧ ((p1 ∧ (p1 → ((p3 → (p5 ∧ False)) → (p5 ∨ True)))) → p2)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643540063994497387806958501464 : ((((p4 ∧ (((p3 ∨ p2) ∧ p5) → ((((p3 ∧ True) → ((False ∨ ((((p2 → p4) → p3) → p3) ∧ p3)) ∨ p4)) → p3) ∨ p1))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1822074355750432120089915004 : ((p4 → ((p5 ∧ (False → ((p2 → p4) ∧ p3))) ∨ ((p4 → ((p2 → (True ∨ False)) → (p2 ∧ p3))) → p5))) ∨ ((p3 → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59088746723557469793609949687 : (((p5 ∧ p3) ∨ ((((p1 ∨ p3) → p2) ∧ p5) → (((p2 ∧ ((p5 ∧ p1) ∨ (((p4 ∨ (p3 → p5)) ∨ p3) ∨ p5))) ∨ True) ∨ p3))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354097126369219324449410772842 : (p4 → (p5 → (((p3 ∨ (p5 → p3)) ∨ (((False ∨ (((p3 ∨ p2) → True) → p1)) ∨ p3) ∧ (True → p1))) ∨ (((p3 ∧ p2) ∨ p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168397230784998883534180369188 : (((p4 → p3) ∨ ((p3 ∨ ((False ∧ False) → (p3 ∧ True))) ∨ (((False ∧ p5) → p4) → p3))) → (((True → (p5 → p4)) → (p4 ∨ p4)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216949046455887422762208578586 : (((p1 → (p2 ∧ p3)) ∧ p1) → (p5 → ((True → (p1 ∧ ((p3 → ((p1 ∧ p4) → (((p3 ∧ True) ∧ p1) → p2))) ∧ (False ∧ p1)))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352092904594076711712318473009 : (p4 → (((p5 ∧ ((p4 ∧ p2) → p1)) ∧ p5) ∨ ((p1 → p2) ∨ (((p1 → False) ∨ (p4 ∨ (p5 ∨ (p3 ∨ p2)))) ∧ ((p3 ∨ True) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311077244505609846257231962647 : (p2 ∨ ((p3 ∨ p1) ∨ ((True ∧ (p2 ∨ (((False ∨ False) ∧ p1) ∧ (((p4 ∧ p3) ∨ (((p4 ∨ (False ∧ p2)) → p2) → p1)) ∧ p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301066827959872289012119044955 : (False ∨ ((p2 ∨ (True → (p4 ∨ ((True ∨ (p3 ∨ p1)) ∧ p4)))) ∨ (p2 → (p3 → (p2 → ((True ∨ ((p2 → p2) ∧ False)) → (p4 ∨ p2))))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713329047759937314504696036664 : ((((True → ((p2 ∧ (p1 → False)) ∧ p5)) ∨ (p3 ∨ ((False ∨ (p5 → (True ∧ True))) ∧ (p2 ∨ ((p3 ∧ p4) ∨ ((True → False) → p2)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39529434397523804589561105911 : (((False ∨ ((True ∨ ((((p2 → True) ∨ (p5 ∧ p2)) → p2) ∧ p4)) ∧ ((p4 ∨ (p2 ∧ (False ∨ ((p2 ∨ True) ∨ False)))) ∧ p4))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49637251846790025704387797290 : (((((p1 → (True ∧ p2)) ∨ p5) ∧ ((p4 ∧ (p4 ∨ (p2 ∨ p1))) → ((((False ∧ p2) → True) ∨ False) → p4))) → (p5 → (p1 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225293681926032592640409706974 : (((False ∨ False) ∧ p2) ∨ ((((((p4 ∧ (p2 → ((False ∧ (p5 → p4)) ∨ p2))) ∨ (p4 ∨ (p5 ∧ False))) → False) ∧ p2) ∨ (p1 → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59246388178203210375705031445 : (((p2 ∨ p3) ∨ ((p3 ∧ (p1 ∨ p4)) ∨ ((False ∧ (((p1 → p1) ∨ (True ∧ False)) ∨ (p1 → (p3 → (p2 ∧ p5))))) ∨ (p5 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112855825087950432757386376294 : (((((p4 → p4) ∧ p2) ∨ (p3 → (((p3 ∨ p2) ∨ ((False ∧ (p5 ∨ False)) ∧ p4)) ∨ (p3 ∨ ((p1 ∨ False) → p2))))) → p5) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227674501385973799361533358307 : ((False ∧ (p3 → p4)) ∨ (True → ((((((p3 ∨ (p4 → (p1 ∧ p1))) → p5) ∨ False) ∨ p2) ∨ ((True ∧ (p2 → p1)) ∨ p5)) ∨ (False → p4)))) := by
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
theorem thm_5_vars_116999576736235003212810676254 : (((True ∨ p5) → ((p5 ∨ True) → ((p4 ∧ (((((False → False) → p4) ∨ (p4 ∨ True)) ∨ (p1 ∧ p1)) → (False ∨ p2))) ∧ p5))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147659297815203888123084727373 : (((((((True ∨ (False ∧ (p5 ∨ (p3 ∧ (p2 ∧ p2))))) ∨ (p1 → p2)) ∨ p1) → p3) ∨ (p5 ∧ p3)) → p2) ∨ (True ∨ (p4 → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133608295359863777475564970078 : ((((((p2 → p1) ∨ ((((False → p4) ∧ (p3 ∧ p2)) ∨ (p5 ∧ True)) → (p4 ∧ (p1 ∨ p3)))) → True) → False) ∧ p3) ∨ ((True ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80097449922468323508368552604 : ((((((p1 ∧ (p4 ∧ ((True ∨ p5) ∨ ((False ∧ p4) → (False ∧ True))))) ∧ p3) ∨ (p4 ∧ ((p4 ∧ p5) ∧ True))) ∨ True) → (p4 ∧ p3)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ (p4 ∧ ((True ∨ p5) ∨ ((False ∧ p4) → (False ∧ True))))) ∧ p3) ∨ (p4 ∧ ((p4 ∧ p5) ∧ True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330620404416299438717723990431 : (True → (True → ((((((((p5 ∨ p4) → (p2 ∨ p5)) ∧ p3) ∧ p5) ∨ p3) ∨ p1) ∧ p5) ∨ (((p3 ∧ p2) ∧ False) ∨ (p4 → (p1 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157498913294216965666530248536 : ((((True ∧ False) ∧ ((((p2 → p4) ∨ (True ∧ p1)) ∧ (p3 ∨ (p5 ∧ p2))) → False)) ∨ (True ∧ False)) ∨ ((p1 ∨ p4) ∨ (p4 ∨ (p3 → True)))) := by
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
theorem thm_5_vars_62607103669927685087873931704 : ((p4 ∧ (((((p4 ∧ p2) ∨ (p1 → ((((p3 ∧ False) → False) ∨ (False → p1)) → p2))) ∨ (True → ((False ∨ False) → p3))) ∧ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616024428656019169891308958222 : ((((((p4 ∨ (False ∧ p3)) ∨ (p4 ∧ (((False ∨ p4) ∧ p3) → (p1 ∨ p5)))) → ((True ∧ ((True → p3) ∨ (False ∧ False))) → p3)) ∨ p1) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h9 := h5 h8
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111819621547628383921376197026 : ((((((True ∧ (p3 ∨ (p2 ∨ (p3 → ((True ∨ ((p1 ∨ True) ∧ p1)) ∨ True))))) → False) ∧ p4) ∧ ((p5 → False) ∨ False)) ∨ True) ∨ (False → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313177555364509506639738630495 : (p3 ∨ (((False ∨ (p3 ∧ ((p1 → True) → (p2 ∧ p2)))) ∨ (((p2 ∨ p4) ∧ (((p1 ∨ True) ∧ p3) → False)) ∨ (True ∧ (False → True)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



