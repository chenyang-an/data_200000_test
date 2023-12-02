variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778463450901951031817039784134 : (((p1 ∨ (p4 ∧ (((((p2 ∧ ((p3 → p3) → p4)) ∧ ((((p3 ∨ p4) ∧ False) ∨ p2) → p4)) ∨ (p4 ∨ False)) → p1) ∨ (p1 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304072437177430607515879247310 : (p1 ∨ ((p2 ∨ (p4 ∨ (p4 → (False ∧ ((p1 → (True → ((p1 ∨ p2) ∨ (((p3 ∧ True) ∨ False) ∨ p2)))) ∧ ((False ∧ p5) ∨ False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118853035227304082104756452775 : ((True → ((False ∨ ((((p4 → p4) → ((p5 ∨ p2) → p4)) → p5) ∨ False)) ∨ (((p5 → (p2 ∧ False)) ∧ p3) → (p3 ∨ p5)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165837165709366479027303930018 : ((((p5 ∨ True) ∧ p5) ∨ ((p2 → p4) → ((p2 ∧ (p5 → (True → False))) → (False ∨ p1)))) ∨ ((((p2 ∧ p5) ∨ p5) ∨ (False → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251341491964199566488688700850 : ((p2 → p3) ∨ (p5 ∨ (((p4 ∨ ((p5 ∨ (((p5 ∧ (p1 → p2)) → (False → p4)) ∧ p4)) ∧ p2)) → False) ∨ ((False ∨ (True → p5)) → p5)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50726106568116770936781664259 : ((((p5 ∨ p1) → (p1 → ((p1 ∨ (p4 ∨ (p3 → p2))) ∨ ((p2 ∨ False) → ((True ∨ p4) ∨ p1))))) → ((p4 ∨ (True ∧ p4)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324973665358065553012756304900 : (p5 ∨ ((p1 → False) ∨ (((((False ∨ (False ∧ True)) ∨ ((p4 ∨ ((((p3 → True) → p4) → False) → p5)) ∨ False)) ∨ p3) ∧ (True → p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47246605479593020635666143273 : (((((p3 ∧ True) ∧ ((p4 ∧ p4) → False)) ∧ (((p4 ∨ p2) → (p4 ∨ ((p5 → True) ∧ (False ∨ (p4 ∧ p2))))) → p2)) ∨ (True ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338372917559656311294111712226 : (p1 → ((p2 ∧ ((p4 ∧ p3) ∨ p5)) ∨ (True ∧ (p5 → (p1 ∧ ((p4 ∧ (p2 ∨ (True ∧ (True ∨ p2)))) ∨ (((True ∨ p2) ∧ p5) ∧ p5))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67989556909736556525399703966 : ((p2 → ((p1 → p4) ∧ ((p1 ∧ ((p5 ∧ (((p5 ∧ p3) ∨ (True ∨ ((p4 ∧ p3) ∧ False))) → (p2 → (p3 ∧ p1)))) ∧ p2)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201179408845179848911141306359 : ((p1 → ((p3 ∧ ((p1 ∨ True) ∧ p1)) → p2)) → (((p2 ∧ (p1 ∨ ((True ∧ False) ∨ (p2 ∧ p1)))) ∧ p2) ∨ (((p2 → True) → p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345649701354544804125234515112 : (p3 → ((p4 ∧ ((((p1 → p4) → ((p1 ∧ p5) ∨ p5)) ∨ True) → (((p1 ∧ p2) ∨ (False ∧ (p3 → p3))) ∧ ((p2 ∧ p4) → p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231480871245195861717698952696 : (((p3 → p1) ∨ p4) → (((p4 → ((False ∨ ((((False → (p4 ∧ p4)) ∧ p1) → p2) ∧ True)) → ((p1 ∨ p5) → False))) ∨ p4) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156883234864477353580209962400 : (((((p4 → (((((p4 ∨ False) ∨ (False ∧ True)) ∧ (p3 → p2)) ∧ p4) ∨ p3)) ∨ p4) ∨ p4) ∨ True) ∨ (p5 → ((p3 ∨ (False → p1)) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721433201127530772709168820746 : ((((p1 ∧ ((p1 ∨ True) → p2)) → (p3 → ((False ∨ True) → (p1 → ((p2 ∨ (p3 ∨ (p3 → ((p2 ∨ p5) → (True → True))))) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622321019565531505539888191631 : ((((p3 ∧ ((((p4 ∧ ((False ∧ p1) → (p4 ∧ (((p1 → p2) ∧ ((False ∨ p1) ∧ p3)) ∧ p1)))) → p1) ∨ (p5 ∧ True)) → False)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60181190745024819973574193283 : (((p5 ∨ p1) → (p2 ∨ ((p1 ∧ p1) → ((((p4 → (True ∨ (p4 → False))) ∨ ((p1 → (False → True)) ∨ p4)) ∧ False) ∧ (p4 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43526172237788356055073495900 : ((((True → (False → (((p1 ∧ p2) ∨ ((((True ∨ (p4 ∧ p2)) ∨ ((False ∧ p2) ∨ p4)) ∧ False) ∨ p4)) ∧ (True ∧ p1)))) ∨ p2) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217185237928606730565980770028 : ((((True ∨ p4) → p3) ∨ p3) → (p5 ∨ (True ∧ (True → (((((False ∨ ((False ∨ p4) → p2)) ∧ p4) ∨ p1) ∧ p4) ∨ (p3 → (False → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150438903586315812364061114245 : (((((((True → p5) ∨ (((p5 → p1) ∨ (True ∧ (p4 ∧ p5))) ∧ True)) ∨ (p1 ∧ False)) ∨ p1) → False) ∧ p1) → (p2 ∧ (p4 ∨ (p2 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((True → p5) ∨ (((p5 → p1) ∨ (True ∧ (p4 ∧ p5))) ∧ True)) ∨ (p1 ∧ False)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58315779507737675159153521192 : (((False ∨ True) ∧ ((((((False → ((False ∨ p1) ∧ p2)) ∧ (p5 ∨ p2)) ∧ ((p1 → p4) → p1)) ∧ (p4 ∧ p2)) ∨ (True ∨ p5)) ∨ False)) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746226446310029471693577306895 : ((((p1 ∨ p4) → (((p3 → (p1 ∨ ((p5 ∧ True) ∨ p4))) → ((p4 ∨ p1) → ((((True ∧ p5) ∧ p2) ∨ p5) ∨ p3))) ∨ (p1 ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624305852690187872611495940754 : ((((p3 ∨ (((((p4 ∧ ((True ∨ False) ∨ (True ∧ p1))) → p4) ∨ p2) → (p4 ∨ (p4 ∧ p3))) ∨ (False ∧ ((p2 ∨ p5) → p4)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_797243098316767892365325295840 : (((p1 → (((((p2 → (False ∨ False)) → ((p4 ∨ (((p5 ∨ p4) ∨ True) ∨ False)) ∨ (True ∧ ((p1 → p2) ∧ p5)))) → p4) ∨ p5) ∨ p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349055615839434326182132373833 : (p3 → (p5 ∨ (((p2 ∨ p5) ∨ ((False ∧ (p5 ∨ p3)) → p4)) ∧ ((p3 ∧ ((p2 ∨ p5) ∧ p1)) ∨ ((p1 ∨ ((True ∧ p3) → p3)) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256744825899357518388898327097 : ((p1 ∨ p1) → (p3 ∨ (((((p5 ∨ (False → p1)) → (p2 → ((p5 ∨ False) ∧ (p5 ∧ p4)))) → p5) ∨ False) ∨ (((p2 ∨ False) → p2) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64640903264302601309911353796 : ((p1 ∨ (p3 ∧ (p3 → ((p2 ∧ ((p2 ∨ (p2 → ((p5 ∨ p3) ∧ p2))) → ((p5 → p1) ∧ p3))) ∧ ((p5 ∧ p3) ∧ (p4 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171422381541055683249710890306 : ((((False ∨ True) ∧ (((p1 ∧ ((p5 ∧ p3) ∧ (p2 ∨ p2))) ∨ False) ∧ p2)) ∧ True) ∨ ((((p2 ∨ False) ∧ p5) ∨ (True ∨ (False → True))) ∨ p5)) := by
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
theorem thm_5_vars_341032731357129297173351356486 : (p2 → ((p5 ∧ ((p4 → (p5 ∧ p4)) ∧ ((p2 ∨ (((p3 ∧ p5) ∨ True) ∨ True)) ∧ (p3 ∧ (((True ∨ (p4 ∧ p3)) ∧ p4) ∧ p3))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356273066131448050043377009900 : (p5 → ((p2 ∨ (True ∧ (((((p1 → p5) ∧ (p3 ∨ p4)) ∨ p4) ∨ p5) ∧ (False ∧ p3)))) ∨ (((p1 → p3) → p4) ∨ ((True → p5) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152654465559226662967249249188 : (((p1 → True) ∧ ((p5 ∨ p5) → ((p5 → (p5 → ((((p1 → (p4 ∨ p2)) → p1) ∨ p4) ∨ p5))) → False))) → (False ∨ ((p5 ∧ p3) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p5 → (p5 → ((((p1 → (p4 ∨ p2)) → p1) ∨ p4) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h9
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177447102751216206069899246218 : ((True → (p1 → ((True → ((p1 ∧ (False ∧ p4)) ∧ p2)) → (False → True)))) ∧ (((p5 ∧ ((((p3 ∧ p1) → p2) → p4) ∨ p3)) ∨ True) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229503942657874148350557255038 : ((p2 → (False ∨ False)) ∨ ((((p1 ∨ p5) ∨ ((p2 ∨ p4) ∨ ((((p2 ∨ p5) ∧ False) ∨ ((p4 → True) ∧ True)) ∨ False))) ∨ p3) ∨ (p5 → p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209173742703845529780695822302 : ((p3 ∨ (p4 → ((p4 ∨ True) ∧ p3))) → (((p2 ∧ ((p5 ∨ True) → (p1 ∨ False))) ∨ (False → p2)) ∨ (p4 → (p1 → (p4 → (True ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322370906690340542212376064258 : (p5 ∨ (((((p4 ∧ p5) ∧ ((((False → (False → p4)) → (True → p2)) → False) ∨ (p4 ∧ p3))) ∧ p1) ∨ ((False → (p3 ∧ True)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251537805285385660551545853517 : ((p3 → False) ∨ ((((((((True ∨ True) ∧ False) ∨ (p4 ∨ p2)) ∨ p5) ∧ ((p3 ∧ p1) ∧ p1)) → p1) → (((True ∨ p2) → p5) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113785741381520420856544118697 : ((((p4 → (p5 ∧ False)) → (p5 ∨ (((True → p1) ∧ (p4 ∨ p1)) ∧ (((p3 → (p3 → p5)) ∨ p3) ∧ p5)))) → (p3 → False)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58732743790607692341481207115 : (((p3 → p3) ∧ ((p1 → (False ∨ ((p5 → (p5 ∧ ((p4 → ((((p1 ∨ p4) ∨ (p1 → p5)) ∨ p4) ∨ p5)) ∧ p5))) → p2))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135320792110875440496437445814 : (((((((False ∨ p5) ∨ p1) ∧ ((p3 → p4) → p5)) ∧ (p3 ∨ p5)) ∨ (p3 → (True ∨ p4))) ∧ (True ∧ (p4 → p3))) ∨ (False → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119424218255477442174305957970 : ((p4 → ((((p5 ∨ (False → (p5 ∧ (p5 → (False → p2))))) ∧ (True → (p5 → (True ∧ p2)))) → (False ∨ p5)) ∨ (p3 ∧ p3))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620316801217733643283561899703 : (((((p1 ∨ False) ∨ ((p3 ∧ p2) ∨ ((p4 → ((False → p3) ∧ ((p3 → p1) ∨ False))) → (p5 ∨ (((False ∨ p5) → True) ∨ False))))) ∨ p3) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197122067572765821914985184185 : (((p2 ∨ (False ∧ (p2 ∨ (p3 ∧ False)))) ∨ p1) ∨ (False → (p5 ∨ (((((((p2 → p3) → (False ∨ True)) ∨ False) ∧ p1) → p3) ∧ p2) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52201873087169417009501840037 : ((((True → (p4 → False)) → (((p5 ∧ p5) ∧ (p4 → True)) ∧ (p2 ∧ (p3 ∧ False)))) → ((True ∧ (p4 → p2)) ∨ (p3 ∧ (p5 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328992671539616109322206988050 : (True → (((p1 ∨ (p1 → p3)) → (p1 ∨ p4)) ∨ (True ∧ (p4 → ((((p5 → False) → p5) ∨ p1) ∨ (False ∨ (p5 ∨ (p1 ∨ (p5 → True))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178199866317646127058643278732 : (((True ∨ (p5 → (((p3 ∧ ((True ∧ p2) ∨ p4)) ∨ p5) ∧ p5))) → False) ∨ (p4 ∨ (((p5 ∧ (True ∧ (p3 ∧ (True ∨ p3)))) ∨ p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398690153608570103414577235912 : ((((True → (False ∧ ((p2 ∨ ((p3 ∨ (((p2 ∨ (((p1 ∧ p1) ∨ True) ∧ p4)) ∨ False) → ((p3 ∨ p3) ∨ p2))) → p5)) ∨ p2))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_218978929821571449223621781222 : ((p4 ∧ ((True ∨ p1) → p3)) → ((((p4 ∨ (True ∨ p4)) ∨ p5) → (p2 ∨ (((True → p3) ∧ p2) → ((p1 ∨ False) ∧ (p4 ∧ p5))))) ∨ p4)) := by
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
theorem thm_5_vars_44948256521419788476660878115 : ((((p1 ∨ True) ∧ (((True ∨ (((((((p4 ∧ p3) ∧ (True → p4)) ∨ p5) → p2) → p5) ∧ True) → (False → p2))) ∧ True) ∨ p1)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246498416187615936145279252384 : ((p5 ∧ p1) ∨ (((p3 ∨ (p5 → p3)) → ((False ∨ p3) ∨ (False ∨ ((False ∧ (p4 ∨ p3)) → (p2 → ((p3 → (True ∧ p4)) ∧ p2)))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266132151681545929085849980402 : (True ∧ (p3 → ((p3 ∧ (((p1 ∧ (p2 ∧ (p1 → ((False ∧ (p2 ∧ p3)) ∨ (p4 ∨ (p2 → p1)))))) ∧ p2) ∨ (p5 ∨ p5))) ∨ (p4 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214195953329950520216959925324 : ((((p5 ∨ True) → p5) → False) ∨ ((False ∨ p3) ∨ (((p3 → p1) ∧ (((False ∧ (p1 ∨ ((p2 ∨ True) ∨ p3))) ∧ True) ∨ (p3 → False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92298658882097770581058772342 : (((True ∨ False) → ((p1 ∨ ((p2 → p5) ∧ (p4 ∧ ((p3 → p2) ∨ p4)))) ∧ (((p1 → (False ∨ True)) → (p1 ∨ p4)) ∧ (False ∧ True)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147395187990916446772777688727 : (((((p3 ∨ p4) → ((p5 ∨ p4) ∧ (True ∨ p4))) → ((True ∨ False) → ((p2 ∧ (False → True)) → p4))) ∨ p3) ∨ ((p1 ∧ (p1 → p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50473976219016265491089614315 : (((p1 → (((p5 ∨ (((p3 ∧ p2) ∨ p4) ∧ ((p3 ∨ p4) ∧ (p1 ∨ (p3 ∧ p2))))) ∧ p4) ∨ p1)) ∨ (p4 ∧ (p3 → (p2 ∨ p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58056900171095403917156471059 : (((False ∧ p2) ∧ ((True → (((((False ∧ True) ∧ False) ∧ (p3 → (((True ∧ p5) ∧ p1) ∨ p4))) ∨ (False ∨ (False ∨ p5))) ∧ p5)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200450591209512442853469219207 : (((False → False) ∨ (p5 → ((p3 ∧ True) ∨ p3))) → (p4 ∨ ((p1 ∧ p4) ∨ ((p1 → True) ∨ ((p2 → ((p2 → p2) ∨ (p4 ∧ p4))) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147911806027470110666950765989 : ((((((((p2 → (False → p3)) → True) ∨ True) ∧ (p1 ∧ (p5 ∧ p5))) ∧ p4) ∨ (p5 ∧ p1)) ∧ (p5 ∨ p5)) ∨ (p2 → (True → (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316895588580130781586732093160 : (p3 ∨ (p1 → (False ∨ (p1 → (((p3 ∨ p5) ∨ ((p3 → ((p4 ∨ p2) ∧ (p4 ∧ False))) → p5)) ∨ ((p4 ∨ p2) ∨ ((False ∨ p3) ∨ True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227101437031815540706046634133 : (((p4 ∨ True) → p5) ∨ ((p2 ∧ ((False ∨ (p5 → p2)) ∧ (p2 ∧ p3))) ∨ (p1 → (p2 → ((True ∧ ((p4 → True) ∧ (True ∧ p5))) → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349560058054657607131779873593 : (p4 → ((((((((p2 ∧ p1) → (p4 ∧ True)) → p1) ∧ (((False → (True ∨ False)) → p1) ∨ (True ∧ p2))) ∨ p4) ∧ (False ∧ True)) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187849790850309564403016893359 : ((p5 → ((False → (p2 ∧ p1)) ∨ (p3 ∨ (p5 ∧ (p3 → p1))))) → (p1 ∨ (p4 ∨ ((True → False) → ((False → ((p4 ∧ p1) → False)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38603444440753212654840118535 : (((((p1 ∧ (((p3 → False) ∧ p3) → p2)) → p5) ∧ ((p5 ∨ ((p4 → ((False ∧ p4) → False)) → (p1 ∨ (True → p1)))) ∨ p2)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41008466349332709318079275889 : (((((True ∨ (((((p2 → (p1 ∧ (p3 ∧ (p1 ∨ True)))) ∧ (p4 → p4)) ∧ (p2 ∨ p2)) ∧ True) ∨ p5)) ∧ p3) → (p5 ∧ p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803965623044326693394112639313 : (((p3 → (((p5 ∧ ((p5 → (p2 → (p4 → p1))) ∧ (False ∨ p2))) ∨ ((p2 ∧ True) ∨ (p4 → (p2 ∨ p2)))) ∧ ((p4 → p5) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629694359973692422562652056698 : ((((((True → (False ∨ (((p5 ∧ ((p3 → p3) ∧ ((False ∨ True) → p1))) ∨ p2) ∧ p1))) ∨ (((False ∧ p4) ∨ p1) → True)) ∨ p2) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56982006406645269602316049925 : (((p4 ∨ (p4 ∨ p5)) ∧ ((p3 ∨ (False ∧ p5)) → (((p4 → False) ∧ p5) ∧ ((p2 ∨ ((((p3 → True) → p4) ∨ p3) ∧ p5)) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37871368346055975542473061932 : ((((p5 → ((p2 → p5) ∨ (((((p3 ∨ (p2 ∨ True)) → p4) ∨ p1) ∨ ((p3 → ((True → p2) ∧ p5)) ∨ p5)) ∧ p5))) → p1) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46991892222275864071478502851 : (((((p5 ∨ ((p4 → ((p3 → p2) ∧ p3)) ∧ (p2 → p3))) ∨ ((p2 → p1) ∨ ((True → (False → True)) ∧ p2))) → p3) ∨ (p3 → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136492122872578135890861624697 : ((((p4 ∧ True) → p5) ∧ (False ∨ (True → ((False ∧ True) ∨ (((p5 ∨ True) → (p3 ∨ (p2 ∨ False))) ∨ (p3 ∧ True)))))) ∨ ((p3 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50355469796904061709475027897 : ((((((True ∧ p4) ∨ p4) ∧ p1) → ((((((True ∧ p5) ∧ False) ∧ p5) ∨ (p2 ∧ True)) ∨ p1) ∨ p5)) ∨ (((p1 ∨ p4) → False) ∧ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56137604131441869556162996015 : ((((p4 ∧ p2) → (p2 → p5)) ∨ ((p5 → False) ∨ ((p3 → (p3 → ((False ∧ p3) ∨ ((p1 ∧ p2) ∧ p3)))) ∨ (True ∨ (p3 ∧ True))))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53247792170970926084629386001 : ((((p4 ∧ p5) ∧ ((p2 ∨ (p4 ∨ ((p4 → p3) ∧ p3))) ∨ p4)) ∨ (((False → True) ∨ (((p2 ∨ p3) ∧ p1) ∧ p5)) ∨ (p5 ∨ p1))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51111630164210860052567736903 : (((((p5 ∧ (((p4 ∨ (False ∨ ((p1 ∧ (p3 ∨ p2)) ∨ p4))) ∨ True) ∧ True)) ∧ p5) ∨ True) ∨ (p5 → ((p5 → (p2 → p2)) ∨ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803349439371758992313726697768 : (((p3 → (((False ∨ p5) ∨ (((((p1 → p1) ∧ ((p2 ∧ (p5 ∧ p1)) ∨ p3)) → (p4 ∧ p1)) ∨ ((p4 ∨ p1) ∨ False)) ∨ p3)) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111193150081068567293827259524 : (((((True ∨ p5) → p3) ∧ ((((False ∧ (p4 ∨ (p5 ∧ (False → p3)))) → (p2 → ((p1 ∧ p4) → p2))) → p1) ∨ p1)) ∧ p2) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58319331899003012679627321501 : (((False ∨ True) ∧ (p1 ∧ ((p3 → (False ∧ p5)) ∧ (p1 ∨ ((p2 ∧ p1) ∧ (True → ((p2 → (((p1 → p2) ∨ p5) → False)) ∧ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302800701611983968004272304728 : (False ∨ (p5 ∨ (((p1 → (((p2 ∨ (True → p5)) ∨ p5) ∧ ((p2 ∨ (((p3 ∧ (p3 ∨ True)) ∨ True) ∧ p5)) ∨ p2))) ∨ (p5 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62991311391596977916648988545 : ((p4 ∧ (True → (((p2 ∧ ((True → ((False ∨ (p5 → p5)) → p2)) → ((p4 ∧ p3) → (p5 ∧ ((p2 → p1) ∧ p3))))) ∧ p2) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695355178777415196027609191129 : (((((p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) → False) → ((p3 ∨ (((p1 ∨ p5) ∨ p1) ∨ p5)) → (p3 ∧ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h8 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h9
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h10 := h1 h8
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h12 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h13 := h1 h12
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h15 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h15
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- False on the left can always be used.
      apply False.elim h20
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h21 =>
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h26 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h27
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h28 := h1 h26
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h30 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h31 := h1 h30
          -- False on the left can always be used.
          apply False.elim h31
      case inr h32 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h33 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h34
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h35 := h1 h33
        -- False on the left can always be used.
        apply False.elim h35
    case inr h36 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h37 : (p5 ∨ (p4 → ((p5 → (((True ∨ True) → p3) ∨ False)) ∨ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h38 := h1 h37
      -- False on the left can always be used.
      apply False.elim h38
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150231910890849361177313264457 : ((p2 → (p5 → (((((True ∨ (((True → p3) → (p5 ∧ p4)) ∨ p2)) → (p2 ∨ p1)) ∧ True) → p5) → p1))) ∨ ((p3 ∧ (p3 → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44173505980121402473105025502 : (((((False → False) → ((False ∧ False) ∧ ((p3 ∨ p1) ∧ (False ∧ (((p5 ∨ True) ∨ (False ∧ p4)) ∨ p3))))) → (p1 → (p5 ∧ True))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184239821870942625706428221732 : (((((p4 → (((p5 ∨ p3) ∧ p2) → p1)) → p3) → p3) → False) ∨ ((((False → False) ∨ ((True ∨ (p2 ∨ True)) → p3)) → True) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234064081280612700749460733591 : ((True → (True ∧ False)) → (((p2 ∧ (True → ((p5 ∨ True) ∧ (p5 ∨ p4)))) ∨ ((True → (True → ((p2 ∨ False) ∧ p2))) ∧ (p5 → p5))) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226802548843574569938859182346 : (((p3 ∧ p2) → p4) ∨ (((p1 ∨ (p1 → p2)) → ((p4 ∨ False) → (p5 → (p1 ∧ (False ∨ p3))))) ∨ (True ∨ ((p3 ∧ p1) ∧ (p4 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50450876954020444406005580246 : (((p2 ∨ (True → (p1 ∧ (((((p3 ∧ p3) → ((True ∨ (p5 ∧ p3)) → True)) → p1) ∨ p3) ∧ p4)))) ∨ ((p4 → False) → (p2 ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61779117405874728826358939659 : ((p2 ∧ (((p3 ∧ (p1 ∨ True)) ∧ (p2 → ((((True → (p3 ∧ p4)) ∨ p4) ∧ ((p5 ∨ p2) ∨ (p4 ∨ (p2 → p4)))) → False))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56522288052738282231747970909 : (((p5 ∧ (True ∨ (p1 ∨ p4))) → ((p1 ∨ (True → (False ∨ (((True → p1) ∧ p2) → ((p3 ∧ (p4 ∧ (False ∧ p2))) ∨ True))))) ∨ p2)) ∨ p4) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248462377223341785964052287623 : ((p2 ∨ p5) ∨ ((p1 ∧ ((((p2 ∧ p4) ∨ False) ∨ p1) ∨ (False ∨ (p5 ∨ p1)))) ∨ ((p5 ∨ False) ∨ ((False → ((p5 ∧ p3) ∧ p1)) ∨ p4)))) := by
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
theorem thm_5_vars_517571773661085167062842111532 : ((((p1 ∧ True) → ((True ∧ ((((True → True) → True) ∧ ((False → (p2 → p3)) → p4)) ∨ (p2 ∧ ((p3 → p3) ∨ False)))) ∨ (p5 ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214157576241664721289207296495 : ((((p1 ∧ p3) → p4) → p1) ∨ ((p3 ∧ (False ∧ p5)) ∨ (((True ∨ (p3 → p4)) ∨ (((p5 ∧ p3) → p2) ∧ p5)) ∨ (p2 ∧ (p3 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156297448978972889614032922161 : ((p5 ∨ ((((p5 → ((p5 → ((p4 ∨ p5) ∨ p1)) ∧ True)) ∧ p2) ∧ (p3 → (p5 ∧ p2))) ∨ True)) ∧ ((p2 ∨ (p5 ∧ p2)) ∨ (True ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234402694934886092731991997654 : ((p1 → (p3 → p1)) → (((p2 ∨ (p5 → False)) ∧ p4) ∨ (False → (((p1 → (p3 ∨ (False ∧ (p2 ∨ True)))) ∧ p4) → ((p1 ∧ p2) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253925081653580201904649268051 : ((p1 ∧ p4) → ((((p2 ∧ (p5 ∧ ((p2 ∧ (p1 ∧ p4)) → (p2 → p1)))) ∧ p5) ∨ (p1 ∧ p2)) ∨ ((p2 → (p5 ∨ (p1 → p1))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683003095424998507180520623642 : (((((p4 ∨ p1) → (p2 ∧ (((p3 ∧ p1) → (((p3 → p3) ∧ p5) ∨ p5)) → (p1 ∧ True)))) ∧ (((p5 ∨ p5) → (p3 ∧ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40371199577732237457257199514 : (((((p3 ∨ (p3 ∨ ((p4 → p4) ∧ (True → ((((p5 ∧ False) ∧ p4) → p4) ∧ ((p3 → (p2 → False)) ∨ p2)))))) → False) ∨ p4) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40448564469195204130049688161 : ((((((True ∨ (p5 ∨ p1)) → (p1 → p4)) ∨ ((p4 ∧ (((p3 → False) ∨ (((True → False) → p3) ∧ p2)) ∨ p2)) → p1)) ∨ True) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122846648625532053839842130506 : (((((p3 → (p1 → False)) ∧ (p1 ∧ (True ∧ (True ∨ (False ∨ (p5 → p2)))))) ∧ ((True ∨ p1) ∧ p5)) ∧ ((p1 ∨ p3) ∧ p2)) → (p4 ∨ p5)) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h5.left
      let h29 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h3.left
        let h32 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h3.left
        let h37 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54167410900045744742764465303 : (((((((p4 ∨ p4) → p1) ∨ False) ∨ True) ∧ p2) ∧ ((((False → (True → p3)) ∨ p2) → p3) → ((p4 → ((p2 ∨ True) ∨ p1)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230896237382464988808117749523 : (((p2 ∧ p2) ∨ p4) → (((False ∧ (p2 ∧ p5)) ∧ (False → (p3 → p3))) ∨ (p1 ∨ (p4 ∨ (p1 ∨ (p2 ∨ (p1 ∧ (True → (p1 ∨ p4))))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172648050440282271515349234176 : (((p2 ∨ p5) ∧ ((((True ∧ p5) ∨ (p5 → p4)) ∨ ((p2 ∧ p3) ∨ True)) ∧ p2)) ∨ (((True ∨ (True ∧ p5)) → p3) → ((True ∧ True) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



