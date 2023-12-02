variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158873581891342630820600329298 : ((False ∨ ((p3 ∧ (p3 → (p1 → p4))) ∨ ((((p2 ∧ (p5 ∨ (False ∨ p2))) → p2) → p5) ∨ True))) ∨ ((p5 ∧ True) → (True → (p2 → p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42902443448286476617951236790 : (((p3 → ((((p3 ∨ p1) → p3) ∨ p1) → (p4 ∨ ((p4 ∧ (False ∨ (((p5 → True) ∧ (p4 → True)) ∨ p4))) ∨ (p5 → True))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172860390986828516470075081747 : ((False ∧ (p3 ∨ ((p4 ∨ ((False → p3) ∧ (p4 ∨ p4))) ∨ (p1 ∨ (p1 → True))))) ∨ (False → ((True ∨ ((p3 ∨ False) → (p3 ∨ True))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262307964656736005878103171120 : (True ∧ (((((p5 → p5) ∨ p4) ∨ (((p2 ∨ (p5 ∧ False)) → p4) ∨ p1)) → (((False ∧ (p5 ∧ p4)) → (True ∨ p2)) → (p5 → p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198539436930755953013403228201 : ((False ∨ (p1 ∧ (True ∧ ((False ∧ False) ∨ p1)))) ∨ ((p4 ∨ (True ∨ (p5 ∧ (False ∧ (p5 ∧ True))))) ∧ ((p2 ∧ p1) ∨ ((False → p4) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198406116326916762682293179916 : ((p4 ∧ ((((False ∨ p5) ∧ p5) ∧ p4) ∨ True)) ∨ (p4 ∨ (p2 → ((p1 ∧ p1) → (p2 ∧ ((p2 ∧ (((p1 ∨ p3) ∧ p1) ∧ p4)) ∨ p2)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56381689658955134214534735732 : (((((True ∨ p5) ∨ p3) → True) → ((((p5 ∧ (p1 ∨ (p3 → p5))) → (p3 ∧ ((p2 ∧ True) ∧ ((p1 → p1) ∨ p3)))) ∨ False) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114599979688206777297767355365 : (((p2 ∧ (((False ∧ p1) ∧ (False ∨ p3)) → ((False ∧ p1) → (False ∧ (True ∨ p3))))) ∧ ((p4 → True) → ((p1 ∧ False) ∨ p4))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63175123171081619243008457589 : ((p5 ∧ (((((p4 ∧ False) → (False ∨ (p2 → ((p4 → (p1 ∨ (p4 → True))) → p3)))) ∧ p4) → (False ∨ (p3 ∨ p1))) → (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725661085608443185835050442984 : (((((p5 ∧ p5) ∧ True) ∨ (p1 ∨ (((p2 ∨ ((p2 ∨ ((((p4 ∧ (True ∧ p2)) ∧ p4) ∨ p4) ∨ p2)) → p2)) ∧ (p5 ∧ False)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78406709430642760950981905577 : ((((p1 → (((((True → (((p3 ∨ p1) ∧ False) → p2)) → False) ∨ (p3 → p5)) ∧ (False ∨ (p3 ∨ p5))) → True)) ∧ p2) ∧ (p1 → p3)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2712434485650240280438472259 : ((True → (p2 ∧ ((p3 ∨ p5) ∧ False))) → ((False ∧ (p2 → ((((p3 → (True ∧ False)) ∧ True) ∧ p2) → (p5 ∧ True)))) ∧ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146485924314126960388656224422 : ((p4 ∨ (((((True → False) ∧ p2) ∧ ((p5 ∨ ((p5 → p2) → ((p1 ∨ p4) ∨ p3))) ∧ p4)) → p1) ∨ p1)) ∧ ((p4 → (False ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258961544877289342734782504933 : ((True → p3) → ((((p5 ∧ (p4 → p1)) → (p1 → ((False ∨ (True → True)) → (p2 ∧ (False ∧ p2))))) ∧ (p5 ∧ True)) ∨ (True ∨ (p1 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612097310570117161426185922331 : ((((((p4 → (((((True ∨ (False ∨ (p1 ∨ False))) ∨ p2) ∨ p3) → p4) ∧ ((p4 → p2) → p5))) → (p5 → p3)) ∧ (p3 ∧ p5)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_65164635668309276171652660801 : ((p3 ∨ ((((p2 ∧ (p3 ∧ (((p3 ∧ ((p5 ∨ True) → p3)) → p1) → (p4 ∧ ((p5 ∧ False) ∧ p5))))) ∧ (p3 ∨ p2)) → p1) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213303055740355595189324065063 : (((True ∧ (True ∨ p2)) ∧ p5) ∨ ((p4 → False) ∨ (((((True ∨ p4) ∧ ((p5 → (p4 ∨ (True ∧ p4))) ∨ (True ∧ True))) → p5) ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112898788664777796285361249708 : ((((p4 → False) ∧ (p3 ∨ ((False ∨ ((p4 ∨ p4) ∧ ((False → (p5 → (False ∧ False))) → (p2 → (True ∨ p4))))) ∧ p1))) → p3) ∨ (p2 ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135009921868660032498848508171 : (((p2 ∨ (((p4 ∨ (((p1 ∧ (p4 ∨ p1)) → (((p2 ∧ False) ∨ True) ∨ p1)) → p2)) ∨ p5) ∧ True)) ∧ (p1 → p5)) ∨ (p3 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136895093006710991877532361964 : (((p4 ∨ False) ∨ (((p2 → (False ∧ (p5 ∧ False))) ∧ (p3 → ((p3 ∧ False) ∧ ((p3 → p5) ∨ (p1 → p2))))) → p5)) ∨ (True ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244131063980181830554480346073 : ((True ∧ p4) ∨ ((False ∨ ((((p2 ∨ False) ∨ p4) ∧ False) ∨ (((p3 ∧ False) → (p5 ∧ (p5 → p3))) → (((p1 → True) ∧ p5) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166709753577328316236780029264 : ((p3 → (((False → (p1 ∨ ((p2 ∧ True) ∨ (p4 ∨ p5)))) → (p2 → p2)) → (p3 ∧ p5))) ∨ (p5 ∨ (p1 → ((p5 ∧ p4) → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172861706904752292562532962048 : ((False ∧ (True → ((((p5 ∨ p1) → False) → p5) → ((p1 → (True ∨ p4)) ∧ False)))) ∨ (True ∧ (((False ∧ (p3 → False)) → (p4 ∧ p5)) ∨ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714579688399766836114106427936 : (((((True ∨ p4) ∨ ((p2 → p4) ∧ True)) → (p2 → ((p3 ∧ p1) ∨ (((p2 → (True ∨ ((p1 → (p2 ∧ p1)) ∧ True))) ∧ p4) → p4)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161674054087879755055429303324 : ((p1 ∨ (p4 → (p3 ∧ ((((p2 → ((p4 ∨ (True ∧ p5)) → p4)) ∨ p3) → (False → p1)) ∨ p2)))) → (((p4 ∧ p2) ∧ p4) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174481505935093953607291314367 : (((True ∧ (p5 → (False ∨ (p5 ∧ False)))) ∧ (((p2 ∧ p4) ∧ p3) → (True ∨ p4))) → (((p4 ∨ True) → p1) ∨ ((p3 → False) → (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727575055274441960297506867807 : ((((p5 ∧ (p1 ∧ True)) ∨ ((p4 → True) → (p4 ∧ ((((((p1 ∧ p4) → True) → ((p4 ∧ p4) ∧ p4)) ∧ (p2 ∨ p3)) ∨ p1) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800437193328888471248616545101 : (((p2 → ((True → ((p3 ∧ (((((p1 ∨ (p2 ∧ p5)) ∧ (False → (p4 → ((True → p3) ∧ True)))) → p3) → p3) ∧ True)) ∨ p3)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357454569844304705076290975132 : (p5 → ((p1 → p1) → (p3 → (p3 → ((((p5 ∧ ((p2 → ((p1 ∨ p2) ∧ p1)) ∧ p1)) ∧ (p3 → (p4 ∨ True))) ∧ p2) ∨ (p4 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39421141743041369815511836024 : (((p4 ∧ (False ∧ (False ∧ (False ∨ ((((p1 ∧ p5) ∨ (p3 ∧ p4)) ∨ True) ∧ ((p2 ∧ (((p3 ∨ p2) ∨ p2) ∨ p4)) ∨ True)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346040057908714030000733674747 : (p3 → (((True → True) → (((((((((p2 ∧ p2) → (p2 ∨ False)) ∧ False) → (p1 → (True ∨ False))) → p4) ∧ p2) ∧ p4) ∨ True) → False)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((((((p2 ∧ p2) → (p2 ∨ False)) ∧ False) → (p1 → (True ∨ False))) → p4) ∧ p2) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133812093287824647444744550842 : ((((p4 ∨ p2) ∧ ((p4 ∨ p3) ∧ (p2 ∨ (((p2 ∧ (True ∨ ((True ∨ (p5 ∧ True)) ∨ p1))) ∨ p2) ∧ p4)))) ∧ p1) ∨ ((p5 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666148232744450569457431586681 : ((((((((((p3 ∨ (False → (p2 → (p3 ∨ p4)))) ∨ p4) ∨ True) → p3) ∧ (p2 ∨ False)) ∨ p4) ∨ (p5 ∧ p4)) ∧ ((p3 ∧ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186496482626190045791913946776 : (((p4 ∧ (p5 ∨ ((p5 ∨ True) ∧ (p3 ∧ p2)))) ∧ (p5 → True)) → (((p1 ∨ (False ∨ p4)) ∨ (p3 → ((p5 ∧ (p2 → p5)) → False))) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h9.left
      let h15 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251548789167945250608437436600 : ((p3 → False) ∨ ((((p3 ∧ (p3 ∨ (((p5 → (p2 ∧ p2)) ∨ (p2 ∧ p4)) → (p4 → p4)))) ∧ p2) ∧ ((p5 ∧ p4) ∧ p3)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336384360472615631837512591552 : (p1 → ((p1 ∧ ((((True ∨ (p2 ∨ ((p3 ∨ (p4 ∧ p2)) → p1))) → ((True ∨ (True ∧ p1)) → ((False ∨ p5) ∧ True))) ∨ True) ∨ p2)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172793599664354228333118275915 : (((p2 → p1) → ((False → p5) ∧ (p1 ∨ (p1 → (p4 ∧ ((False ∧ p5) ∨ p2)))))) ∨ (((p1 ∨ (True → (p3 ∨ True))) ∨ p4) ∨ (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_301094296367049058009424983750 : (False ∨ ((p4 ∧ ((p1 → (p4 ∧ ((True ∧ p5) → p5))) → False)) → (((False ∧ ((p2 ∨ False) ∨ ((p3 ∨ p3) → p5))) ∧ (p5 ∧ p5)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (p4 ∧ ((True ∧ p5) → p5))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749955972428971531968162860547 : (((True ∧ ((((p5 → (p2 ∨ p1)) ∧ ((p4 → p5) ∧ (True → ((((False ∨ (True → p3)) ∨ p2) → False) → p1)))) ∧ (p2 ∨ p4)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62924870904654478732612797330 : ((p4 ∧ (p1 ∧ (((((((p1 ∨ (p1 ∨ p2)) → p5) → p2) ∧ p4) → (((False ∧ False) → (p5 → (True ∨ True))) → p4)) ∧ True) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50292942659035437077066291816 : ((((True ∧ ((p2 ∨ (True ∧ ((p1 ∨ p4) ∧ (p4 → p4)))) ∨ (p5 ∨ False))) ∧ ((p4 → True) ∧ False)) ∨ (p3 ∨ (p5 ∨ (True ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315832269020782823419617885691 : (p3 ∨ ((p5 ∨ p4) → ((p3 → ((False ∨ ((p5 ∧ (p5 ∨ False)) ∨ (p2 → p1))) ∨ (False → False))) ∨ (p5 ∧ (p5 ∧ ((p1 ∨ False) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346280686348086666686602380456 : (p3 → ((((p3 ∧ (((p3 ∧ (p5 ∨ (((p3 ∧ p4) ∨ ((p3 → True) → (False → True))) ∧ p1))) → False) ∧ p2)) ∧ p4) ∧ True) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670276582706981683012348053166 : (((((True ∨ (p4 ∧ (False ∧ p5))) → ((p1 ∨ (p3 → (p1 ∧ p5))) ∨ ((p5 ∨ p2) ∨ (p2 ∧ (False → p3))))) ∨ ((p4 ∨ p4) → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653632879826091489657489281048 : ((((((((p3 → (False ∧ False)) ∧ ((p1 ∨ p3) ∨ (((p4 ∨ p5) → p5) ∨ p5))) ∨ (p2 → (p2 ∧ True))) ∨ False) ∧ True) ∨ (True → p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802078515468082383050128916370 : (((p2 → (True ∧ (((p2 ∧ True) ∧ (p5 ∧ ((p1 ∧ p5) ∨ ((p3 → (False ∨ p4)) ∨ p4)))) → ((p5 ∧ (p1 ∧ (p1 ∧ p4))) ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119802746118672243772895317782 : ((((((True → p4) → (((p3 ∧ (p5 ∨ p1)) ∨ ((True → False) ∨ (True → p3))) ∧ (True ∧ p4))) ∨ (p1 ∨ True)) → False) ∧ p4) → (p4 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((True → p4) → (((p3 ∧ (p5 ∨ p1)) ∨ ((True → False) ∨ (True → p3))) ∧ (True ∧ p4))) ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227617239210751700954271995754 : ((False ∧ (False ∨ p3)) ∨ (((True → p1) ∧ p3) → (p5 ∨ ((((p5 → p1) ∧ (((p1 ∧ (p4 ∨ p2)) ∨ False) → (p4 → p4))) ∨ p2) → p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319574273742489360490751572853 : (p4 ∨ (((((True ∧ False) ∨ (False ∨ p3)) ∧ False) ∨ (p5 → p1)) → ((p1 ∧ p2) → ((((p5 ∧ ((False ∧ p4) ∨ p2)) ∨ True) → p3) ∨ p2)))) := by
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
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h7
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176359642378895906345278941709 : ((((p1 → p1) → (True ∧ ((p5 ∨ (True ∨ p4)) ∧ False))) → (p3 ∧ p5)) ∧ (True ∧ (True ∨ (((False → p1) → (p3 ∧ p1)) ∧ (p3 ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300363217104666319253375014737 : (False ∨ (((p1 ∨ (True ∧ (((p3 → True) → p1) ∨ (True ∨ ((False ∨ ((False ∧ False) ∧ False)) ∨ (p3 ∧ False)))))) ∨ p4) ∨ ((False → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112810579502954808413002602013 : (((((p4 ∨ (p4 → p3)) → (p1 ∨ p4)) → (((p4 ∨ (p5 → (p5 → ((True ∧ p5) ∧ True)))) → p2) ∨ (p5 ∨ False))) → p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163013132190428030592952464845 : ((((((((False → p1) → (False ∨ p1)) ∨ p1) → p3) → p5) ∨ True) ∨ (p1 ∧ (p3 → False))) ∧ (p3 ∨ ((p1 → (True ∧ (False → False))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64660360296405081332411171407 : ((p1 ∨ (False ∨ ((p3 → ((False → (((p1 → (p4 ∧ p1)) → True) ∨ False)) ∧ ((False ∧ True) ∨ p2))) ∨ (p1 ∨ ((True → False) → False))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137038918468072338664793924458 : (((True → False) → (p2 ∨ ((False → (p5 ∨ p5)) → ((p3 → (True → ((True → p3) ∧ (True ∧ (True ∧ p3))))) → p5)))) ∨ (False ∨ (p4 ∨ p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352494087864444503731429354791 : (p4 → ((False → (True ∨ False)) → ((((p1 → (p2 → p5)) ∨ (p1 ∧ p5)) ∨ p3) → ((p1 ∧ (True ∧ (p3 ∨ True))) → ((p1 ∧ p5) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187705988062247241176635332825 : ((False → (p3 ∧ (p5 ∧ (p4 ∨ (p4 ∧ (p2 ∨ (p2 → p1))))))) → ((p1 ∨ p1) → (((p2 ∨ False) ∨ ((False ∨ p5) ∧ p4)) → (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149790028799309404177308163660 : ((False ∨ (((p4 ∧ p1) ∨ (p2 ∨ (False ∧ True))) ∨ (p5 ∧ ((p4 ∧ (p3 ∧ (p1 ∧ (p5 ∧ False)))) ∨ p1)))) ∨ ((p3 ∧ p3) → (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56394708203510532342358475170 : ((((False ∧ (p2 ∧ p5)) → False) → ((p4 ∨ True) → ((((p5 ∧ p4) → (True → p4)) ∧ (p5 ∧ ((True ∧ (p4 ∨ p3)) → p4))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246115495781978931950194337259 : ((p4 ∧ p1) ∨ (p1 ∨ ((((((p2 → (p3 → (False ∨ p4))) → p4) ∧ p1) → p2) ∨ ((True ∨ (p4 → p1)) → True)) ∨ (p4 ∨ (p3 → p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589798806508895914926012352181 : (((((((((p2 ∧ p5) ∧ (p3 ∧ (p2 ∧ ((False → (p1 → (p3 ∧ p4))) ∧ True)))) ∧ p2) ∧ (True ∨ True)) → (p2 ∨ True)) → p3) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65259167776118346053925203715 : ((p3 ∨ ((((p5 ∧ p5) → p2) ∨ (((((False ∨ True) ∨ False) ∨ p1) → ((p3 → False) → p4)) ∧ (p1 → ((p5 ∨ False) → p5)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588352385174374878624712188869 : (((((((p1 → p1) ∨ (False ∧ True)) → (p1 ∧ ((((False ∨ p3) ∨ p1) ∧ (p2 ∧ (p4 ∨ ((True ∨ p4) ∨ p4)))) ∧ p2))) ∨ True) ∧ True) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983500611816252603667181192640 : (((p1 ∧ (((False ∨ (True → False)) ∧ p5) ∧ (((p3 ∨ (False ∧ p5)) ∧ p1) ∨ (p3 ∨ (p3 → ((((p3 ∧ False) → True) → p1) ∨ True)))))) → p3) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h21 := h9 h20
        -- False on the left can always be used.
        apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256893584607248005974650633540 : ((p1 ∨ p4) → ((False ∧ (((p5 ∧ p1) ∨ ((p2 ∧ ((((p1 → (p5 ∨ p5)) ∨ p2) ∧ p3) ∧ p3)) ∨ p4)) ∧ (False ∧ p5))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674788870589806512324300682705 : ((((p4 → ((((p4 → p3) ∨ True) ∨ ((p4 ∧ p4) ∨ (p2 → False))) → ((p5 ∨ True) ∧ ((False ∧ p3) → p5)))) → ((True ∧ p3) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153686231655831914571711297020 : ((p2 → (((p4 ∨ p4) ∧ p3) → ((True ∨ (False ∧ ((p5 ∧ p5) ∧ False))) ∧ (((True ∧ p4) ∧ p3) ∧ p1)))) → (((p1 ∨ p3) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_301327125506710581204725349142 : (False ∨ (((p3 ∧ (p3 ∧ p1)) → p1) ∧ ((((((p4 ∧ True) ∨ p2) ∨ False) ∧ p1) ∨ False) ∨ (True ∨ (((p1 ∧ p2) ∨ p1) ∧ (p2 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_960799430813862500494180324939 : ((((False ∨ p1) ∧ ((((p3 ∧ False) → p4) → p4) ∧ ((True → False) → ((p1 ∧ False) ∧ ((((p1 ∨ p4) → p5) ∧ (p5 ∨ p4)) → p3))))) → p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((p3 ∧ False) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175451539287342852416875789482 : ((p1 → (False ∨ (True ∧ ((((p3 ∧ False) ∧ ((p5 ∨ p3) ∧ p5)) ∨ False) ∨ p1)))) → ((p1 ∧ (p1 ∧ (((p5 → p2) ∧ True) → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179122439103166075606260253308 : ((p1 ∧ ((p4 → (((p4 ∧ p3) ∧ (p1 ∧ (p1 → p3))) ∧ p4)) ∨ p2)) ∨ ((False → ((p5 ∧ p1) → p2)) ∧ ((p3 → p2) ∨ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792385081598489897073429988219 : (((True → ((p1 → ((((p5 ∨ ((p4 ∨ p2) → p4)) ∧ p5) → False) ∨ (p2 ∨ p5))) ∨ ((p2 ∨ ((p2 → (p5 ∨ True)) ∨ p1)) ∨ p5))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713052610960328507324655633490 : ((((p4 ∧ ((False ∧ (False ∧ p5)) ∨ p5)) ∨ ((((True → p1) → p3) ∧ p5) → (p5 → (((((p2 ∨ True) → p1) → True) → True) → True)))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166702308627321808875526130166 : ((p3 → ((((p3 → p5) ∨ (True → (True → ((p1 ∧ True) ∧ True)))) → (False ∧ p2)) ∨ True)) ∨ (p3 → (((p2 → p4) → p3) ∧ (p3 ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260773492877345126611385231638 : ((p3 → p5) → (((p4 → (((p4 ∨ (p2 → ((p5 ∧ p3) ∧ (((p4 → p2) → p5) ∧ p1)))) ∧ p3) → ((p1 ∧ p3) ∨ p4))) → p3) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (((p4 ∨ (p2 → ((p5 ∧ p3) ∧ (((p4 → p2) → p5) ∧ p1)))) ∧ p3) → ((p1 ∧ p3) ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40476467896912135330035275209 : (((((True ∨ p4) ∧ ((p4 ∧ (((p3 → (True ∨ p5)) ∨ p3) → (p2 ∧ ((p2 ∨ False) → (p2 → (p5 → False)))))) ∨ p1)) ∨ p5) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790175233066713608219958431887 : (((p5 ∨ (True ∧ ((p3 ∨ ((True → (p3 ∨ p4)) ∧ ((p3 ∨ (False ∨ (p1 ∨ p3))) ∨ p2))) ∨ (False → (p4 → (p4 ∨ (p2 ∨ p5))))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_687533555558215641370210432457 : ((((((((p5 → p3) ∨ (((p5 ∨ p2) → (p2 → p3)) → False)) → p3) ∧ p4) → p3) ∧ (True ∧ (((p3 → p3) ∧ p1) ∨ (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347476397963298632915648444081 : (p3 → (((((p4 ∨ p5) → True) ∨ p3) → p1) ∨ ((p1 ∧ (True → (p5 ∨ (p3 → p3)))) ∨ ((p5 ∧ ((p5 ∨ (True ∧ p2)) → p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110778351925785504429967097289 : (((((False ∧ ((p1 ∨ p4) ∨ (((p5 ∨ p4) ∧ ((True ∨ (True → (p1 ∨ p1))) ∨ (True ∨ p1))) ∨ p3))) ∧ p1) ∨ False) ∧ p3) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112929378493232363513180647691 : ((((p5 ∧ p4) → ((((((p3 ∧ p2) ∨ (p1 ∧ (p3 → ((p2 → p5) ∨ p3)))) → p1) ∧ (p2 ∧ p5)) ∨ p3) ∨ p5)) → p4) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61346342288140497495010367341 : ((p1 ∧ ((((True ∨ (p5 → (p3 ∨ (p1 ∨ p4)))) → (p5 → (p2 ∧ (p4 ∧ (False ∧ True))))) ∧ ((p5 ∨ p3) → (p3 ∨ p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262346286883330422436483221633 : (True ∧ (((p5 ∧ ((False ∧ p4) ∧ p5)) ∨ (((p3 → (p2 → p5)) ∨ p1) → (p3 ∧ ((False → ((p5 ∨ p5) → (False → True))) ∧ p4)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340990158986080000206719240957 : (p2 → (((p2 ∨ p3) → (p1 → (((((p3 → ((False ∧ p5) ∧ (p5 → p3))) ∨ (True → False)) ∨ p3) → False) ∧ (p3 ∨ (False ∧ True))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330866859146374157416391224317 : (True → (p3 → ((((True ∧ (False ∧ (p1 ∧ p4))) ∨ p5) ∨ p3) ∧ ((p5 ∧ p2) ∨ (((True ∧ p3) → (p5 → p5)) → (False ∨ (p2 → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193853007075970106016933431781 : ((True ∨ (((p2 → p3) → p5) → ((p2 ∧ False) → p1))) → (p3 ∨ ((((True ∨ p1) → (p5 ∨ p2)) ∧ (p3 ∧ (p2 ∨ (False ∨ p1)))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323671567652768750289891761651 : (p5 ∨ (((((False → p3) → p5) ∨ False) ∧ (p2 → (p2 → ((p1 ∨ ((p3 → p3) ∧ (p2 → True))) → p2)))) ∨ (True → (p3 → (True ∧ p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113383177225707973646910092338 : (((p5 ∨ ((((True ∧ p1) → (p4 ∨ ((p5 → False) ∧ ((p3 ∧ p5) ∨ False)))) ∨ (p4 ∨ p4)) ∨ (p4 ∨ True))) ∧ (True → p1)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56858332732350551611218591610 : (((False ∧ (False ∨ p1)) ∧ ((((((p1 ∨ p3) → False) ∨ p1) ∧ (((p5 ∨ False) → ((p4 ∨ (True ∨ p1)) ∨ p5)) → p5)) ∧ p3) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164920713110216830458063693415 : (((((((True ∧ p5) ∧ p5) ∨ (True ∧ (((False ∨ p5) ∨ p1) ∨ p5))) ∨ p2) ∨ p3) → False) ∨ ((p4 ∨ (((p5 → p4) ∨ p4) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_599856525473449474819056951392 : (((((p1 ∧ p3) → (((((p3 → (p2 ∧ (p1 ∨ (p5 ∧ False)))) ∨ p1) ∨ True) ∧ ((p2 ∧ p3) ∧ p2)) ∨ (p5 ∧ (p4 ∧ False)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603216296250286542620586559308 : ((((p2 ∨ ((p1 ∨ (p2 ∧ (p3 ∨ ((((p5 ∨ True) ∨ p1) → p4) → p3)))) ∨ (False ∨ ((p1 ∨ (p1 → p4)) ∨ (p4 ∨ False))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47431844440885365670292440017 : (((p2 ∧ (((p2 → (((True ∧ p5) ∨ p1) → ((p2 → p5) → p4))) → (p1 → ((True → p5) ∧ True))) → (p3 ∧ p3))) ∨ (True → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208729999778779843260536167427 : ((p1 ∧ ((p5 → p4) ∧ (p1 ∨ p4))) → ((((True → p1) → ((p1 → (True → (p4 → (((p5 ∧ True) ∨ p2) ∧ False)))) → p4)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225484523696120761984182220921 : (((p5 ∨ True) ∧ p1) ∨ ((True ∧ True) → (((p1 ∧ (p4 ∨ (p3 → (True → (True ∨ p5))))) ∨ p3) ∨ (((p1 ∧ False) → (p1 → p1)) ∨ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177669507092933162595089298777 : ((((((True ∨ (False ∧ ((p1 ∧ p1) ∨ p5))) → p4) ∨ p4) → p1) ∧ True) ∨ (((p2 ∧ ((p4 ∧ (p3 ∧ p5)) → (p5 → p1))) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53042932443919024552134324996 : ((((p4 ∧ p3) ∧ ((p1 ∧ ((False ∧ False) → p5)) ∧ (p1 ∧ p1))) ∧ ((((True ∨ ((p5 ∧ (p3 → p2)) ∨ p3)) ∧ p4) ∧ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642103277716024857158235836999 : ((((True ∧ ((p2 ∧ ((p1 ∨ p1) ∨ (((False ∨ p5) ∨ False) ∧ (p4 → ((True → p2) ∧ p2))))) ∧ ((False ∧ p4) → (p1 → False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115538492543135000796155299354 : (((p3 ∨ ((p2 → ((False ∨ p2) → False)) ∧ p2)) → ((((p4 ∨ p2) ∧ (((False ∨ True) → (True → p4)) → p2)) ∧ p1) ∨ p3)) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49889146364702121118457541747 : ((((((True ∨ (p2 ∨ (True → p3))) ∧ p2) → ((p5 ∨ (p1 → p5)) ∧ ((False ∧ p4) ∧ p4))) ∨ False) ∧ ((False ∧ p4) → (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



