variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719873893420190550947892736029 : ((((p4 → ((p3 → p2) ∧ False)) ∨ (((p4 ∧ (p4 ∧ (((p1 → p5) → ((True → p4) ∧ (False ∨ p2))) ∧ p5))) ∧ (True ∨ p5)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720491181335034923195316425141 : (((((p2 ∨ (p2 → True)) ∨ p4) → ((p2 ∧ (((((p5 ∧ ((False → p5) ∨ False)) ∧ True) ∧ p3) → (p3 → p2)) ∧ p2)) ∨ (p4 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623444823656915373559065656946 : ((((False ∨ ((((p3 ∧ p2) ∨ (p2 ∧ p2)) ∨ (((p4 ∨ (True ∧ (p5 ∧ (False → p1)))) ∧ (False ∨ p2)) → False)) ∧ (p1 ∧ True))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_620322197677787049893777149093 : (((((p1 ∨ p2) ∨ (((((p3 ∧ (False ∨ p3)) ∧ (False ∨ p3)) ∧ (True → True)) ∨ ((p3 ∧ (p3 ∧ p5)) ∨ (p2 ∨ p3))) ∨ p1)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776752765253858190439388668740 : (((p1 ∨ ((((p2 ∧ True) ∨ ((((p5 ∨ (p5 ∧ (((p2 → p4) ∧ p1) → p2))) ∧ p1) → p1) ∨ (p4 ∨ False))) → (True → True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251797344751357760051369571658 : ((p3 → p4) ∨ ((((p5 → p2) → p5) → (((False → False) → (p2 → ((p3 → (p4 ∧ p2)) ∨ p1))) ∨ True)) ∧ (((p1 ∨ True) ∨ p1) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776997037351529301773922168384 : (((p1 ∨ ((p1 ∨ ((p1 ∧ ((p5 ∨ p2) → (p4 → p5))) ∨ ((((p2 → p2) ∨ (p5 ∧ p1)) ∨ p5) ∨ (p3 ∨ p4)))) ∧ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135679477438481829899518938128 : (((((((p5 ∧ (True ∨ True)) ∧ p5) ∨ p1) ∧ ((False ∨ p1) ∨ True)) ∧ p2) ∧ ((p3 ∧ True) ∨ (p1 ∨ (p1 ∨ p3)))) ∨ ((p4 ∨ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322832948229862629664017040424 : (p5 ∨ ((((p3 ∨ p4) ∨ ((p1 → (p1 → p1)) ∨ ((p4 ∨ p4) ∨ False))) → (p3 ∧ ((True ∨ (p2 ∧ (p4 → (p5 → p4)))) → False))) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p4) ∨ ((p1 → (p1 → p1)) ∨ ((p4 ∨ p4) ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ (p2 ∧ (p4 → (p5 → p4)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137694550284934590508631484897 : ((p1 ∨ ((p4 → (((((p3 ∧ p4) ∧ False) ∨ ((p1 → p5) → (p1 → ((False ∨ p4) ∨ p2)))) → p5) ∨ p2)) → p3)) ∨ ((p3 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147882079537452623599324561416 : ((((((p1 → ((p1 → p4) ∨ (p2 ∨ (p4 ∨ ((p1 ∨ p5) → True))))) ∧ False) ∧ p1) ∧ p4) ∧ (False ∧ p1)) ∨ ((p4 ∧ False) → (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338410363193567542265495983304 : (p1 → (((p4 → p4) ∧ (p2 ∧ p1)) → (((p3 ∨ (((p3 ∧ True) → (p3 → p2)) ∧ p3)) ∨ p4) → ((False ∨ (p4 ∨ p2)) ∧ (p2 → p1))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h2.left
      let h14 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h2.left
    let h19 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Implications on the right can always be decomposed.
  intro h22
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h2.left
      let h26 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h2.left
      let h33 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h2.left
    let h38 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117187254686435129119680778238 : ((True ∧ ((p2 ∨ (p4 ∨ (p3 ∨ (((((True ∧ p5) ∨ (True → p1)) ∨ p2) ∧ p3) ∧ (True → p3))))) ∧ (p4 ∧ (p2 ∨ p4)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111324664630831044726534417886 : (((p2 ∧ (((p4 ∨ ((p1 ∨ p3) ∧ p4)) → (((p5 ∨ (p2 → (True → p2))) ∧ (p4 ∨ (p4 ∧ p3))) ∨ p3)) ∧ p5)) ∧ p1) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685271015346893804988511376346 : ((((p1 → (((p5 ∨ True) ∧ (p4 ∨ ((p2 ∨ p3) ∧ p4))) ∧ ((p2 ∨ p3) ∧ (p4 ∧ False)))) ∨ ((True ∨ (True ∧ p1)) → (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52385024745958671817947316133 : (((((((p5 ∨ p5) → p5) → p4) → p1) ∧ (((True ∧ p1) ∧ False) ∧ p1)) ∧ (p1 → (p3 ∧ (False ∧ ((p3 ∨ True) ∧ (p1 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66561665802749586676080166321 : ((True → ((((((p5 ∨ ((p1 ∧ (p3 ∧ p2)) → ((p5 ∨ p3) ∨ p3))) ∧ (False ∨ (True → p5))) → p4) ∧ False) ∨ p3) ∨ (False → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255147167102159009208222757275 : ((p4 ∧ p3) → (((True → p4) ∨ ((p1 → p4) ∧ p3)) → ((((False → True) ∨ (p3 ∧ (p3 → False))) → p2) ∨ (False → (p4 ∨ (p5 → True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226627838611976660337348790104 : (((True ∧ True) → p3) ∨ (p3 → ((((p1 ∨ (((False ∧ True) ∨ p1) ∧ p4)) ∨ ((((False → p5) ∨ p5) ∨ p5) ∧ (p5 ∧ p1))) → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
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
        apply False.elim h9
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h14.left
        let h18 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h14.left
        let h21 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h14.left
      let h24 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309325285311952926424673909590 : (p2 ∨ ((((False ∨ p3) → (False ∨ (False → (((p3 ∧ ((True ∧ p2) ∧ ((p3 ∨ False) ∨ True))) ∧ (False ∧ p1)) ∧ p4)))) → False) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156934399455238353865030485431 : ((((p2 ∧ (((True → (p4 → (p2 → (p4 ∨ p5)))) → p3) → (p1 → p5))) ∧ (p2 ∧ p2)) ∨ False) ∨ ((((p3 → p3) ∨ False) ∨ p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159959316465144704078102039802 : ((((False → (((p2 ∧ ((p4 ∨ p5) ∨ p5)) ∨ ((p4 ∨ True) → p1)) ∨ p4)) → (p3 ∧ p3)) → p4) → ((p4 ∨ (p3 → p2)) → (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644923086290557191848502330993 : ((((p2 ∨ ((p3 ∧ p3) ∧ ((False ∨ (p3 ∨ ((((False ∨ p5) ∧ (p3 ∧ (False ∧ p3))) ∨ ((p4 ∨ p1) ∧ p2)) ∨ p1))) ∧ True))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141998007632013046164505003443 : (((True → False) → ((((p3 ∨ (p1 → ((False ∧ p2) ∧ p2))) → (p4 ∧ (p5 → p2))) ∨ (p1 → True)) ∧ (p1 → p5))) → (p4 ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302587548792179164050988209409 : (False ∨ (p1 ∨ ((p1 → (True ∧ True)) ∧ ((((False ∨ p5) → (p2 ∨ (p3 → p1))) → ((p2 → p1) ∨ ((p3 → False) ∧ (False ∧ p4)))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167692770523965227213511383101 : (((((p4 ∨ (p2 ∨ ((False ∧ True) ∨ p2))) → p2) → (p4 ∨ p1)) ∧ ((False ∨ True) ∧ p4)) → (p4 → ((True → p1) → (p1 ∨ (False ∨ p3))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680664557665782188706238320338 : ((((((((True → p3) → False) → p1) ∨ p3) → (((p4 → (p5 ∨ p5)) ∧ (p3 → p2)) ∧ (p5 ∧ p2))) → ((p3 ∨ (False ∧ p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167846227744331546166568638879 : ((((p2 → (p5 ∨ p5)) → (p4 → ((p4 ∧ p1) ∨ p4))) ∨ ((False ∨ p1) ∨ (p3 ∧ p5))) → (p1 → ((p4 ∨ p5) ∨ (True ∨ (p2 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117249669151458907678548117996 : ((True ∧ (p5 ∨ (((p2 ∨ ((p2 → p5) ∨ p5)) → False) → ((((p2 ∧ p5) ∧ (p2 ∧ p2)) ∧ p1) ∧ ((True → True) ∧ False))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164854080179683582509614872777 : (((False ∨ (((False ∨ (((True ∨ p3) ∧ True) → p5)) → ((p4 → p1) ∨ False)) ∨ p1)) ∨ p3) ∨ (((False ∧ (True ∨ p5)) ∧ True) → (True ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234642978380034372952403183756 : ((p3 → (p4 → True)) → ((True ∧ p3) → ((p1 ∧ (((False ∧ ((False ∧ (p5 ∧ (p4 ∧ (False ∨ False)))) ∧ (p2 ∧ p4))) → p1) → p4)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135913154941738018774916444983 : (((((p5 → p5) → p1) ∧ (((p5 → p1) ∨ (p2 ∨ False)) → p1)) → (((p2 → ((p5 ∧ p2) ∧ p1)) ∨ p4) → p3)) ∨ (p1 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118523609301357972935173541736 : ((p3 ∨ ((p2 → False) ∨ (True → (((False ∨ p1) ∨ ((((p4 ∧ p1) ∨ p2) ∧ p4) ∨ ((p2 ∨ p4) ∨ (p3 → p1)))) ∧ p2)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52117156302778528774298147494 : (((((((p4 ∧ p4) ∧ (p3 ∧ p1)) ∨ p3) ∨ (False → ((p1 ∨ p3) → False))) → p5) → (p1 ∧ ((True → (p5 ∨ (p4 ∨ p2))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58312147547654217914827609925 : (((True ∨ p5) ∧ (((p5 ∨ p3) ∧ ((p1 → (p5 → (True ∧ (p4 ∨ p5)))) ∧ p3)) ∨ ((p4 ∨ ((False ∧ p1) → (p2 ∧ p1))) ∧ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230296550806330167024593520466 : (((p1 ∨ p1) ∧ True) → (p5 → (p5 ∧ (((False ∨ ((((True ∧ ((p5 → (p5 → p2)) ∨ p1)) ∧ p1) → True) ∧ (False → p2))) → p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198950950466954496868203990991 : ((p4 → (p2 ∧ (((False ∨ False) → False) ∨ p4))) ∨ (((p2 ∨ True) ∧ p2) → (((p2 → p5) → (p1 ∧ p2)) ∨ ((p3 ∧ (p5 ∧ True)) ∨ True)))) := by
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
theorem thm_5_vars_118487562899047776293897345142 : ((p3 ∨ (((p1 ∧ p3) ∧ (p2 → ((((p3 ∨ (False → (p4 → p2))) ∨ p4) ∨ p5) → (p5 ∧ p2)))) ∨ ((True → p5) ∧ p4))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684466065280081725219562588815 : (((((False ∨ ((p5 ∧ p3) ∨ (p3 ∨ (p1 → False)))) → ((p5 ∨ (p4 → p5)) ∨ (p2 ∧ p4))) ∨ ((p2 ∧ (True → (p4 ∧ p3))) → p2)) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57027311838823749449582472105 : (((p1 → (False → False)) ∧ (True → ((((p4 ∨ p3) → (p2 ∨ (p3 ∧ (((p2 → p1) → (p5 ∨ p4)) ∧ p5)))) ∧ (p3 ∨ p5)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775952935207446007864238717037 : (((False ∨ (p2 → ((((((p5 ∨ True) ∨ p3) → ((p3 ∨ p4) → (False ∧ (p4 → p5)))) ∨ p3) ∧ (p5 ∨ (p2 ∨ (False ∨ True)))) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604249130488069820906969968627 : ((((True → ((((((p2 ∨ p1) ∨ p1) ∧ ((p2 ∨ (True ∧ p5)) ∨ (True ∨ p2))) → p3) → (p2 → (True → (p1 → p3)))) → p2)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55212711815596361926846279606 : ((((p5 → (True ∧ p3)) ∧ (p5 ∨ p3)) ∨ ((p3 ∨ (p3 ∧ (((True ∨ (p1 → ((True → p2) ∨ p3))) ∨ (p2 ∧ True)) → p3))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60061216826837152920882165948 : (((p2 ∨ p1) → ((p4 ∨ (((True → p2) ∧ (p1 ∨ p5)) ∧ p3)) ∨ (((p4 → (p3 ∨ (True ∧ ((False ∨ p3) ∧ True)))) → True) ∨ p1))) ∨ p5) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204383695304054473766925675556 : (((p5 ∨ (p4 ∨ (p3 ∧ p1))) ∧ p2) ∨ (((p3 → (p2 ∧ ((p5 ∨ (p4 → False)) ∨ ((True ∨ p4) ∧ (p3 ∧ p2))))) → p3) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66048700443539486883629162743 : ((p5 ∨ (((p5 ∧ (((p1 → p4) ∧ (p1 → ((p4 → (p4 ∨ p4)) → (((p4 ∨ p4) → p4) ∧ p3)))) ∨ (True ∧ p5))) ∧ True) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163420279350793731961893409295 : ((((p5 ∧ p1) ∧ (p3 ∨ p4)) → ((False ∧ (((p4 ∧ p5) ∧ p3) → (True → p1))) ∨ True)) ∧ ((p2 ∨ ((p3 ∨ p2) ∧ (p3 ∧ p5))) ∨ True)) := by
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
  cases h3
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50402565851641768049129836538 : (((True ∧ ((((False ∨ p1) ∧ p2) ∨ ((((p2 ∧ False) → p2) → p2) ∧ (True → (p1 → p3)))) ∧ True)) ∨ ((p4 → p1) → (p4 ∨ True))) ∨ False) := by
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
theorem thm_5_vars_256710286079053175498228258655 : ((p1 ∨ p1) → (((((p5 → (((p2 ∧ (p1 ∧ p5)) ∧ (((False ∨ False) → p3) → True)) → p4)) → p4) ∨ (p1 ∨ p4)) ∧ False) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166545481939517810858986501873 : ((p5 ∨ (((p1 ∧ (((p3 ∧ (p5 → p3)) → False) ∨ True)) ∧ (p1 → p5)) ∧ (p5 → p5))) ∨ (True ∧ (p1 → (p3 ∨ (True ∨ (False → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190779022714700880233055836164 : ((((p1 ∨ ((True ∧ False) ∨ p1)) ∨ p3) ∨ (p3 ∧ p3)) ∨ (((p5 ∧ ((p4 ∨ (p3 → p3)) ∧ (p2 ∧ p2))) → p2) ∨ (True ∧ (p2 ∨ p1)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659753541913309651704140385701 : (((((p1 ∧ (((p1 → p4) → (((p1 → p4) ∨ (p3 ∨ p3)) ∨ p4)) ∨ (p2 → ((p2 ∨ p1) → (p3 ∧ p5))))) ∧ True) → (p4 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302604803319484595117827417853 : (False ∨ (p1 ∨ (p5 ∨ (((True ∨ False) → ((((False ∧ (p3 ∨ (p3 ∧ True))) ∨ p4) ∨ True) ∧ (False ∧ (False → ((p3 ∨ p3) ∧ p5))))) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2197017239083011772234719189 : (((p2 → p3) → ((p5 ∧ (p2 ∧ ((True ∧ p3) ∨ p5))) ∨ ((p2 ∨ p3) ∨ p1))) ∨ (True ∨ (p2 ∧ (True → ((p3 → p5) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621104494407520320278607675114 : (((((p3 → p5) → ((p1 ∨ ((((((p5 ∨ p2) → p1) ∧ True) → p2) ∨ ((p4 ∧ False) → p1)) ∧ (p4 ∧ (p2 → False)))) ∧ True)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57040324512382578185373175666 : (((p2 → (p4 → True)) ∧ (((p4 → (((p1 ∧ False) → p2) ∧ False)) ∧ (p4 → (p4 ∧ p5))) → (p4 → (((p5 ∨ False) ∨ True) ∧ False)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57303565835179464387711554381 : ((((p5 → p1) → p3) ∨ ((p3 → ((((p1 → True) ∧ p2) → p4) → p4)) → (p1 ∨ (p4 → (((p5 → p2) → p1) ∧ (p3 ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206944660285204668110366023882 : (((((p3 ∧ False) ∨ True) → p3) ∧ p2) → (p5 → ((p1 → ((p2 → False) → p3)) → (((((False ∧ (p3 ∨ p4)) → p4) → p4) ∧ False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259675779663504349243100518880 : ((p1 → p1) → (((p3 → (((False ∨ (p2 → p2)) → p4) ∧ (p3 ∨ ((p5 → True) → p4)))) → ((False ∨ p5) ∧ (p4 ∧ (p2 ∧ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792964889950922925653457570880 : (((True → ((p2 → False) ∧ (((((p1 ∧ (p2 ∧ (p4 → (p5 → p2)))) ∧ p1) ∧ p3) → p1) ∧ (p4 ∧ (p5 ∧ (False ∧ (True ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174322231856259241663721947193 : (((p4 ∧ (p2 ∧ ((p1 ∨ (p2 ∨ (p3 → p4))) ∨ False))) ∨ ((p5 ∨ p4) → False)) → (p3 ∨ (((p4 → p4) ∧ (p4 ∨ (False → False))) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648633463483640390216235634524 : ((((((p5 ∨ ((p2 ∨ p2) ∧ False)) → (p2 ∨ (p2 → ((p3 ∨ (((p1 ∨ p1) → p1) ∨ p5)) → (p4 ∧ p4))))) ∨ p3) ∧ (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190394808480789442830551047258 : (((p1 ∧ (False → (((True ∧ True) → True) → p5))) ∨ p4) ∨ (((((p4 ∧ p2) → (p4 ∧ False)) → p3) → ((True → p1) ∧ p4)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165459269331799297151871937226 : (((((p2 → p2) ∧ p1) ∨ (p1 ∧ (p3 ∧ (p4 → True)))) ∧ (p5 → (p1 ∧ (p4 ∧ False)))) ∨ (False → ((p3 → (False → (p4 ∧ p4))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148675056957585947435385455754 : ((((((p5 ∨ False) → (p2 → True)) ∨ p4) → p2) ∨ (((p4 → (p3 → ((p4 ∧ p2) → p3))) ∧ p4) ∨ False)) ∨ ((p1 ∧ (False ∨ p3)) → p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778051240714817996917867891924 : (((p1 ∨ ((True ∨ p3) ∧ (p5 → ((True → (p1 ∨ (((p3 → (p3 ∧ p4)) ∨ p1) ∧ p2))) ∧ ((p5 → ((p2 → p2) ∧ True)) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303885031258308814986955329690 : (p1 ∨ (((((((True → (p2 ∨ p3)) ∨ p2) ∧ False) → p3) ∨ (p3 ∨ ((False ∨ p4) → (False ∨ p1)))) → ((p4 ∨ (False ∨ p1)) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41741917496739095291148348702 : ((((p5 ∨ (p5 ∧ (False → True))) ∧ ((((p4 ∨ False) ∧ (p3 ∧ p5)) ∨ False) ∨ (p4 → ((p3 ∨ p4) ∨ ((p4 → p3) → True))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382550521297548489393907270879 : (((((((((False ∨ p3) ∨ p1) ∧ False) ∨ p3) ∧ (((True ∨ ((True ∨ ((p5 → p5) ∨ (p1 ∧ p1))) ∧ p3)) → p2) ∧ p2)) ∨ True) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114738521983799245171294776079 : (((((False ∧ p3) ∨ p5) ∨ (p5 ∧ ((True → (False ∧ p3)) → (p3 → (p3 → p1))))) → (p1 → (p1 ∨ (p1 → (p1 ∨ p3))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626644342579842673934838274865 : ((((p4 → (True → (((True ∨ ((p4 ∧ p2) ∨ ((((p3 ∨ True) → False) → p4) → ((p5 → p2) → (False ∨ p5))))) → False) ∧ p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255909524907030938992302708153 : ((True ∨ p2) → (((((((((True → p4) → (p1 ∧ p2)) → (p5 ∧ True)) ∨ (p5 ∧ p5)) ∧ True) ∨ (p4 → False)) ∨ p2) ∧ (p5 ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_194140960028780270065036781783 : ((p1 → ((True ∨ ((False ∨ p1) ∨ p5)) ∨ (True → p4))) → ((True → (p5 ∧ ((p1 ∨ p3) ∧ ((p4 ∧ p5) → (False ∧ False))))) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45585557397900084057779509727 : (((p3 ∨ (((p3 ∧ (p5 ∨ False)) → (((p4 ∨ ((p5 → False) → ((p4 → (p5 ∧ (False ∨ False))) ∧ p3))) ∧ False) ∧ True)) ∨ p4)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207445564306686788278178868353 : (((p3 ∨ (p4 ∨ (p3 → p2))) ∨ p5) → (((p2 ∨ True) ∧ (p2 → (p4 → (((p1 ∨ True) ∧ (((p3 ∧ p3) ∧ p1) → False)) ∨ p4)))) ∨ p5)) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200843998921267795183626251079 : ((True ∨ ((False → (p4 ∧ (p2 ∨ p5))) → True)) → ((False → (p1 ∨ p5)) → (True ∧ (((p4 ∨ p4) → False) → ((p5 ∨ (p2 ∨ False)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_249456045667380855822642241746 : ((p5 ∨ False) ∨ (p1 ∨ (p5 ∨ ((((p2 ∨ True) ∨ (p4 ∧ (p3 → p3))) ∨ p1) → (((p2 → p5) ∧ (True ∨ False)) → (p4 → (p1 ∨ p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
          exact h3
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330262095888911626459081952022 : (True → (False ∨ (((p4 ∧ (p4 ∨ p1)) ∧ (p4 → False)) → ((((p2 → (True → (p4 ∨ False))) → p3) → False) ∧ (p5 ∨ (p4 ∨ (True → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343218304904283667772645591879 : (p2 → (((p2 ∨ p2) → False) → ((p1 ∧ p4) ∨ ((p4 → ((p1 ∨ (((p2 ∧ False) ∧ True) → p3)) → ((p4 ∧ (True ∨ p5)) ∧ p3))) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113510636120825248074959037110 : (((((p2 → (True ∧ ((((p2 ∨ p3) ∨ False) ∧ p4) ∨ p5))) → p3) ∧ (p4 → (p5 → (p1 ∨ (p2 ∧ p3))))) ∨ (True ∨ p1)) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185255072523296737086744643554 : ((p1 ∧ ((p5 → ((p2 ∨ (p4 → p4)) → (p1 ∨ p2))) → False)) ∨ (((p5 → (p5 ∧ (p4 ∧ (p4 ∧ False)))) ∧ ((p4 → p2) ∧ p4)) → p4)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134179230634213904672741972393 : (((((((p1 ∨ (True → p5)) ∨ (False ∨ False)) ∨ (p4 ∧ p3)) ∨ p5) ∧ ((p1 ∧ (p3 ∧ (p1 ∧ p3))) ∧ p2)) ∨ p3) ∨ ((p5 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781551486221327165708739452525 : (((p2 ∨ (False ∨ ((p2 ∧ (((p5 ∧ (p3 → p5)) → p1) ∨ (p5 ∧ (p5 → (((((p4 ∨ p5) ∧ p4) ∨ p3) ∨ p1) ∧ False))))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52480732156826524720787106195 : (((True → (p5 ∧ ((p2 ∧ (p5 ∧ p5)) ∨ (p5 → ((False ∧ True) ∨ p1))))) ∧ (((p1 → p2) → ((p1 ∧ p2) ∨ (p1 → False))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616298464182994878681399124744 : ((((((False ∨ ((False ∧ p1) ∧ (False ∧ True))) ∧ ((p4 → True) → p5)) ∨ (((p3 ∨ (False → p2)) → (False ∨ (p2 ∧ True))) → p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342884131126591652112157354941 : (p2 → (((p4 ∧ (p1 ∨ (p4 ∧ p3))) ∧ p1) → ((((p3 ∧ p4) → ((p3 → p5) → False)) ∨ False) ∨ ((p3 ∧ (False → p2)) ∨ (True ∧ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187816865818123727682565620034 : ((p4 → ((((p4 ∧ False) ∧ True) ∧ p2) ∨ (p5 → (p4 → True)))) → (((True → False) ∨ p2) → (p2 ∨ (False ∨ ((p1 ∧ p5) ∨ (p2 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704664359601895223113144791390 : ((((True ∧ (p4 → (False ∨ (p3 ∨ (False ∧ (True ∧ p2)))))) → ((p4 ∧ p2) → ((p3 ∨ (((p2 ∧ p3) → (p2 ∨ p5)) → p5)) ∧ p2))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197643974311142230680410679279 : (((((p1 ∧ p3) ∨ p4) → False) → (p1 → p5)) ∨ ((p4 ∧ (((p4 ∨ (True ∧ p4)) → True) ∨ (((p1 ∧ True) ∧ p2) → p2))) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135084311987207853364097812034 : (((((p2 ∧ (((p2 ∨ p2) ∧ (p3 ∨ p1)) ∨ (True → True))) ∨ True) ∧ ((p5 → (p2 ∧ p2)) → p3)) ∨ (True ∨ p5)) ∨ ((True ∧ p1) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37155476597013114169308623459 : (((((((p5 ∨ (False ∨ True)) → p2) ∨ (p5 ∧ (True ∨ (True ∨ ((False ∧ False) → (True ∨ p2)))))) → (True ∧ (p5 → p4))) ∧ p1) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115997628752025109177132685665 : ((((p3 ∨ (p2 ∨ True)) → p3) → ((((False ∧ p5) → True) ∨ (p3 ∧ (p3 ∧ (p1 ∧ (False ∧ (True → False)))))) → (p3 ∧ p3))) ∨ (True ∧ p2)) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ (p2 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : (p3 ∨ (p2 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305304171519127131688910650288 : (p1 ∨ ((((((p4 ∧ p2) → False) ∧ False) ∨ p4) → (p2 ∧ (p5 ∧ (p1 ∨ ((p2 ∨ p1) ∧ True))))) ∨ ((False → ((p2 ∨ False) → p2)) ∨ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192117854902299560956016931434 : ((p5 → ((False ∧ (((p1 → p1) ∧ p2) ∨ p2)) ∧ True)) ∨ ((((((p1 ∨ p3) ∧ p4) ∨ (p1 ∧ True)) ∨ True) ∨ ((p3 ∨ False) ∨ p2)) ∨ False)) := by
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
theorem thm_5_vars_165494534134478457034987638306 : ((((False → False) → (False ∧ (False ∧ (p5 ∧ (p3 → p2))))) ∨ ((p1 ∧ p2) → (p3 → True))) ∨ (p4 → (((p1 ∨ p4) ∨ (p2 → p4)) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309601826254744214332810952045 : (p2 ∨ ((((p2 ∨ False) ∧ (((True ∨ False) → ((p2 → p4) ∨ (p2 ∨ ((p1 → p4) → (True ∧ p1))))) ∧ True)) ∧ p2) ∨ (p4 → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173339409504964854584047076955 : ((p2 → (p1 ∨ ((((p4 → (p5 → (p4 → (p4 ∨ p2)))) → p2) ∨ False) ∧ p5))) ∨ (False → (True ∨ (((p4 ∨ p1) ∧ (p1 ∨ p4)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626086047548197734487058978818 : ((((p2 → (p4 ∨ (((p5 ∧ (p2 ∧ p3)) ∨ (p3 ∨ (((p4 ∧ p2) → p2) ∧ (((p5 → p4) → (p1 ∨ p2)) ∧ True)))) ∧ True))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45023161288506019939565320754 : ((((False ∨ p1) ∨ (True ∨ (p5 → ((p3 ∨ ((True → (True ∧ p4)) → p2)) ∧ (True → ((True ∨ (False ∨ (p2 ∧ p5))) ∨ p1)))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166443200395750993489049669387 : ((p2 ∨ ((((p5 ∨ p3) → p5) ∧ ((p5 ∨ ((False ∨ False) ∧ p4)) ∧ (False ∧ p3))) ∨ p3)) ∨ ((p3 ∧ ((True → False) → p4)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



