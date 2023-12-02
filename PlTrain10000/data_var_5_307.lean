variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157407625409518754618452792612 : (((((p5 ∨ p3) → (((p4 → (False ∨ p2)) ∧ True) ∨ p3)) ∨ ((False → p5) → p4)) ∧ (p5 → True)) ∨ (False → ((p3 ∧ (p2 ∧ p4)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346342954509549473209092387802 : (p3 → (((p5 ∧ ((((p2 → True) → False) → p3) ∨ p3)) → (p2 ∧ ((p1 → (p4 → True)) ∨ (((p4 ∧ True) ∧ p3) ∨ p5)))) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640732716020954914598067350832 : (((((True → True) ∧ (p3 ∨ (p4 → (False → ((((((True ∨ (p1 → False)) ∧ p2) ∨ (p4 → p1)) ∧ p3) ∧ (True → p2)) ∧ p1))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208606872527435006367981937355 : (((p4 → p4) → ((p5 ∨ p1) ∧ False)) → (((p2 ∨ p3) → p4) ∨ (p2 ∧ (p3 ∧ ((True ∨ (p3 ∨ ((p4 ∨ True) ∨ p3))) ∨ (p3 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → p4) := by
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
theorem thm_5_vars_115323397213699768027339744479 : ((((False → p1) ∧ (((p1 ∨ (p2 ∧ False)) ∨ p3) → False)) → (p5 ∧ (((False ∧ (p5 ∨ (p1 → (p2 ∨ p3)))) → False) → p4))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325028077063180726547119717074 : (p5 ∨ ((p3 ∧ p4) → (p2 ∨ (((p2 → (p1 ∨ ((p5 ∨ (p3 → False)) → ((p1 ∧ (p4 → p1)) ∧ p3)))) ∨ (p1 ∨ (p3 ∧ True))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263409477341214776339439512343 : (True ∧ (((True ∧ p2) ∧ ((True → ((p1 ∧ ((p4 ∧ False) ∨ p1)) ∧ (p5 → (p4 ∧ (p2 ∧ True))))) → (p4 → p5))) ∨ ((False ∧ p3) → p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643754342615202757710202813102 : ((((p5 ∧ ((((((True ∨ (True ∨ p4)) ∧ False) ∨ p4) → ((p1 ∨ True) ∨ (p1 ∨ p3))) ∧ p1) ∧ (p1 ∨ ((p1 → p2) → p5)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326144549254265648659322210657 : (p5 ∨ (p1 → (p4 ∨ (((((p4 → True) → False) → p4) ∨ ((False ∨ p4) ∨ p1)) → ((p5 ∨ (((p1 → p4) ∧ True) → (p3 ∨ True))) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197787691820762834036709128162 : ((((p3 ∧ p3) ∧ p4) ∨ (p2 ∨ (p5 ∨ True))) ∨ ((p5 ∧ (False ∧ p4)) ∧ ((p4 ∨ (((p3 → (p5 ∨ False)) ∨ (True ∨ True)) → True)) ∨ True))) := by
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
theorem thm_5_vars_348847213950430196838352283500 : (p3 → (p2 ∨ ((((p1 ∨ ((((False → (p1 ∨ p1)) → (p5 ∧ p5)) ∨ p5) ∧ (((p5 ∨ (False ∨ p1)) → p2) ∧ p4))) ∨ True) ∧ p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219558682605655472494885970670 : ((True → ((p5 → True) ∧ False)) → (((((p1 ∨ p3) ∨ (p1 ∨ p3)) → p3) ∧ p2) ∨ ((p5 ∨ (p3 ∨ (p2 ∧ ((p3 ∨ p3) ∧ p5)))) ∨ p1))) := by
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
theorem thm_5_vars_179034030490066481547807377910 : (((p5 ∨ True) → (((p2 ∨ ((False ∧ False) ∨ (True → False))) → False) ∧ p5)) ∨ ((((((p5 → True) ∧ True) ∨ (p1 → p5)) → False) → p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → True) ∧ True) ∨ (p1 → p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622021297117014872300587152866 : ((((p2 ∧ (((False ∨ (((p1 ∧ ((False ∨ True) ∨ (p3 → ((p3 ∧ p1) → False)))) → p4) ∨ p1)) ∧ ((False → p2) ∨ True)) ∨ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171600747353420987268970750321 : (((((p2 ∧ (p4 ∨ (p2 ∧ p1))) ∧ p4) ∨ (((p2 ∧ p1) ∧ p2) → True)) ∨ p1) ∨ (p3 ∧ (False ∨ (((False → (p5 → False)) ∨ True) → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219973868623299241834848463488 : ((p5 → ((p5 ∨ True) → p5)) → ((p3 ∧ (((p4 ∨ (((p5 ∧ (p1 ∧ p1)) ∧ True) ∨ False)) ∧ (p1 ∧ p3)) ∨ (p4 ∨ (p2 → True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66666453539408022968006576587 : ((True → ((((p5 ∨ p2) → (p3 → False)) ∧ p5) ∨ (p4 ∧ ((((False ∨ (True → (p4 ∨ p5))) ∧ ((p4 ∧ p3) ∧ p4)) ∨ p5) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149033943006170397555942307604 : (((p2 ∧ (False ∧ p4)) ∨ (p3 ∨ ((((((p1 → p3) → False) ∧ ((p4 → p4) → p1)) ∨ False) → p1) → p5))) ∨ (True ∨ ((p4 ∧ p2) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57558688374514232297984994346 : ((((p4 ∧ p4) ∧ p4) → (((p3 → ((False ∨ True) ∨ p4)) → (p2 ∧ ((p2 ∨ ((p5 ∧ (True → p2)) ∨ p3)) ∨ True))) ∧ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350047967189465020676007656555 : (p4 → (((p3 ∨ (p1 → (True → ((((p4 ∨ p4) ∨ ((p2 → p1) ∧ (False → True))) ∧ ((p2 ∨ (p4 ∧ p2)) ∨ True)) ∧ p2)))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166270319750164903669005578526 : ((p3 ∧ (False ∨ ((p3 ∧ False) ∧ (p4 ∧ ((p5 ∨ p2) ∨ ((p3 ∧ (p5 ∨ p4)) → p5)))))) ∨ ((p1 ∧ False) → ((p2 ∧ p2) ∧ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386076189951773377881227080958 : ((((((p4 ∧ (((p4 ∧ True) ∧ (p5 → (p4 ∧ False))) → (p2 ∧ ((p4 → (p2 ∧ p2)) → False)))) ∧ (p3 ∧ True)) ∨ (p1 → True)) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158668186361295055706885923845 : ((p2 ∧ (((p2 → True) ∧ ((p3 ∨ True) ∧ (False ∨ ((p4 ∧ (False ∧ p5)) ∨ (p2 ∨ p3))))) ∧ p3)) ∨ ((p5 → ((p3 → p4) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731759952357238315519916111064 : ((((p3 → (True ∨ False)) → ((p1 ∧ (p1 ∧ p4)) ∨ (False ∧ (((p4 ∧ (p1 → (False ∨ p1))) → True) → (p3 ∨ ((p1 ∨ p5) ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149567750495873225022229497362 : ((p2 ∧ (p3 ∧ ((p4 ∨ (p3 ∨ ((p5 ∧ (False ∨ (p4 ∨ (p2 ∨ False)))) ∧ (True ∧ True)))) → (p4 ∨ p4)))) ∨ ((p1 ∨ (p2 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345666530087620485087804254110 : (p3 → ((False ∨ ((((p4 → True) ∨ ((p3 ∧ p4) ∧ p4)) → False) ∨ (p5 → (False ∨ (p5 ∨ (p3 → ((True → (p4 ∨ p3)) → p3))))))) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191894223422934152149817863134 : ((p5 ∨ ((True ∧ (p4 ∧ ((p2 ∨ p1) → p1))) ∨ p5)) ∨ (((((p2 ∨ p2) ∨ (True → ((False ∧ False) ∨ (p1 ∧ True)))) ∨ True) → p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ p2) ∨ (True → ((False ∧ False) ∨ (p1 ∧ True)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153443431767189401907520449190 : ((p4 ∨ ((((p5 ∧ ((p4 → p2) ∧ p3)) → (False ∧ (True ∧ True))) → p4) ∧ ((p4 ∨ (p3 ∧ False)) → p5))) → ((p2 ∨ True) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302994294013998881236649055085 : (False ∨ (p1 → (((p5 → (p5 ∨ (((((((p3 → p2) ∨ p5) ∧ False) → (True ∧ p1)) → p5) ∧ p2) ∨ (True ∧ p1)))) → False) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136538976377001855303201716224 : ((((True ∧ True) ∧ p4) ∨ ((False ∨ ((True → p1) → p5)) ∧ ((p2 → p3) ∨ ((((p2 ∧ p3) ∨ True) ∧ p4) ∨ p5)))) ∨ ((p2 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148286193217628615192025065629 : ((((p2 → (True → (((p3 ∨ p3) → (p5 ∧ ((p4 → p2) ∧ p2))) ∨ p1))) → False) → ((p2 ∨ p2) ∧ p4)) ∨ (True ∨ ((p4 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68531579123147809539595775049 : ((p3 → (p1 → (((True ∧ ((p3 ∧ (((p5 → p2) ∧ p2) → p5)) ∨ p3)) ∧ p4) ∨ (p1 ∨ ((True ∧ ((p1 ∧ p3) ∨ p1)) ∨ p2))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_626474427798986629941862669634 : ((((p4 → (((((p1 ∨ p1) ∧ ((p1 ∧ (p2 ∨ p3)) ∧ True)) ∨ (p5 ∨ (p1 → p1))) ∨ (p5 → (p3 → p4))) ∧ (p5 ∨ True))) ∨ p5) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259814488453835013934375309160 : ((p1 → p3) → ((True → (p2 ∨ (((True → ((p1 ∨ p4) ∧ (p3 ∨ p5))) ∧ (p2 → (p4 ∧ p4))) → p1))) ∨ (((False ∨ False) ∧ p1) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114234803612018563375185959536 : (((p4 ∧ ((True ∧ ((p2 ∨ (p5 ∨ (p2 → p4))) → False)) ∧ (((False → False) → p2) → (p4 ∨ p5)))) → (p3 ∧ (p2 → True))) ∨ (p4 ∧ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∨ (p5 ∨ (p2 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40344379830788712803346704717 : (((((False ∨ ((p4 → p2) ∨ (((False → (p2 → p5)) → ((p4 ∨ p3) ∨ ((p1 ∧ p2) ∨ (p5 → False)))) ∨ p2))) ∨ False) ∨ True) ∨ p4) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111877621350467853564888293514 : (((((p4 → (((p4 ∨ ((False → p5) ∨ p3)) → (p2 ∨ p2)) → True)) ∧ (True ∨ p5)) → ((p5 ∧ (p4 ∧ p1)) ∨ p1)) ∨ p5) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37693074431368745051102988128 : (((((((p1 ∨ p1) → p5) ∨ ((p4 ∨ (((p1 ∨ (p5 ∨ p5)) ∨ p1) → ((p3 ∧ p2) ∨ p5))) ∧ p4)) → (p5 → p1)) → p4) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663456089092679315716655088178 : (((((p5 ∨ True) → (((((p3 ∨ p1) ∨ (False → True)) ∧ ((True ∨ ((True ∧ (p2 ∨ True)) ∧ False)) → p1)) ∨ p1) ∧ False)) → (p3 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599297802932070788632047578785 : (((((False ∧ p5) ∨ (((True → p1) ∨ ((p2 ∨ p2) ∧ (p3 ∧ ((True ∧ ((p2 ∧ (p3 ∧ False)) ∧ p1)) ∨ False)))) ∧ (p2 ∧ p3))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157772675138624174780042781490 : (((((True ∨ p5) ∧ (p3 ∨ (p1 ∧ ((p4 ∨ True) → p3)))) ∧ p1) ∨ (p4 ∨ ((False → True) ∨ p2))) ∨ ((p1 ∨ p5) ∨ (p3 ∨ (p2 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115075103427836066777430882104 : ((((True ∧ p4) → ((p1 ∨ ((p2 ∧ p3) ∧ p5)) → (p4 → False))) ∨ ((False → ((p5 → p1) → ((p2 → False) → p4))) → p2)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150608092886242783340601040297 : (((True ∧ ((((False → (p4 ∧ (True ∨ p4))) ∧ p2) ∨ (p4 → p3)) ∧ (((True → False) → p2) → False))) ∧ p5) → ((p3 ∧ (p2 ∨ False)) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : ((True → False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h11
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h15 : ((True → False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- False on the left can always be used.
      apply False.elim h18
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h19 := h7 h15
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h28
  case inr h29 =>
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h30 : ((True → False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h31
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h33 := h31 h32
      -- False on the left can always be used.
      apply False.elim h33
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h34 := h25 h30
    -- False on the left can always be used.
    apply False.elim h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h37 := h35.left
  let h38 := h35.right
  -- Conjunctions on the left can always be decomposed.
  let h39 := h38.left
  let h40 := h38.right
  -- Disjunctions on the left can always be decomposed.
  cases h39
  case inl h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
    have h44 : ((True → False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h45
      -- One of the premise coincides with the conclusion.
      exact h43
    -- We have shown the premise of h40, we can now drive its conclusion.
    let h46 := h40 h44
    -- False on the left can always be used.
    apply False.elim h46
  case inr h47 =>
    -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
    have h48 : ((True → False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h49
      -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
      have h50 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h49, we can now drive its conclusion.
      let h51 := h49 h50
      -- False on the left can always be used.
      apply False.elim h51
    -- We have shown the premise of h40, we can now drive its conclusion.
    let h52 := h40 h48
    -- False on the left can always be used.
    apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157736365840119846266825697681 : (((p4 → ((p2 → p5) ∧ ((p1 → p4) ∨ ((p5 → (p5 ∧ False)) → False)))) → (True → (True ∧ p4))) ∨ ((p4 ∨ True) ∨ (p1 ∧ (p4 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150149636333039802051512118598 : ((p1 → ((((((p4 ∧ p5) ∨ p2) ∧ ((False ∧ False) → True)) ∧ (p5 ∨ p3)) ∨ ((True ∧ p3) → p5)) → p2)) ∨ (p2 → ((True ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64548072429516771290849595193 : ((p1 ∨ ((((p4 → p4) ∨ p4) ∧ p5) ∧ ((p1 ∨ (p3 ∨ ((p5 ∨ p4) → (((True → p4) → p1) ∧ p3)))) → (p1 ∧ (p5 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723655727171837665003316525189 : (((((p4 ∨ p5) → False) ∧ (False ∨ (((True → p5) ∨ (p1 ∧ ((True ∧ (p5 ∨ (True → False))) ∧ True))) ∧ ((p3 → p5) → (p3 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117028535311704776424736111859 : (((p2 ∨ p3) → (((((p2 ∨ p4) ∨ p4) → (False ∧ (((False ∨ (p2 ∧ (p1 ∨ (p2 → False)))) → p2) ∨ p1))) ∧ p5) ∨ True)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210263354368601538478802662863 : ((((p5 ∨ p3) → p4) ∨ True) ∧ (((p1 → (((p1 ∨ (p4 → (p1 → p5))) ∧ False) ∧ (p5 ∧ p3))) → ((p2 → p3) ∧ p2)) ∨ (True ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_107120141872096432465458199641 : (((False → (False → (p5 → p2))) → (((p3 ∨ (True ∨ p3)) ∨ p5) → ((True → False) → ((p1 ∧ p2) → ((p5 → p5) ∧ p5))))) ∧ (p2 → p2)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h4.left
  let h15 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h23 := h3 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h26 := h3 h25
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h27
  -- Implications on the right can always be decomposed.
  intro h28
  -- One of the premise coincides with the conclusion.
  exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117587318882727637939029902539 : ((p2 ∧ (p2 ∧ ((((p2 ∨ ((((p1 → (p2 ∨ p2)) ∨ ((p5 ∨ False) ∨ False)) ∨ p4) ∨ (p3 ∧ p2))) ∨ p4) ∧ False) ∧ p2))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186504719609559304933580761778 : (((p5 ∨ ((p3 → p1) → ((p3 ∧ p3) ∨ p5))) ∧ (False → p2)) → (p2 ∨ (True ∨ ((p5 ∨ ((False ∨ p1) ∧ p5)) ∨ ((p1 ∨ p4) ∧ p1))))) := by
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
theorem thm_5_vars_50931682266424415807549441404 : ((((((p5 → p3) ∧ (p4 → (p3 ∧ False))) ∨ (p2 ∧ (p3 → p2))) → (p2 ∨ (p5 ∧ p2))) ∧ ((p2 ∧ ((p4 → True) ∧ False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114487758467223123970997923943 : (((((((p1 ∨ False) ∧ p4) ∨ ((p3 ∨ (False ∨ p1)) ∧ p2)) ∨ True) → ((p1 ∨ True) ∧ False)) → (p2 ∨ ((p1 → p3) → p2))) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ False) ∧ p4) ∨ ((p3 ∨ (False ∨ p1)) ∧ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909026000780575850207263827515 : (((((True ∨ (p2 ∧ ((p1 ∨ p2) → (p5 ∧ ((p4 → p5) → p5))))) → ((p1 → p1) → p3)) ∧ ((p2 → (p5 → p4)) → (p3 ∨ False))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p2 ∧ ((p1 ∨ p2) → (p5 ∧ ((p4 → p5) → p5))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52267664723124347848188672815 : (((True → ((p4 ∨ ((((p4 → p2) → True) ∧ p5) → (p3 ∨ (False ∨ p5)))) ∨ p2)) → ((p2 → False) → (((p2 → p1) ∨ p1) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112025190286350623318105168179 : ((((p5 ∨ (p5 → p4)) ∧ (p3 ∧ ((p2 ∧ (((p2 ∧ (p3 ∨ ((True → p4) ∧ True))) → (p1 ∨ p5)) ∧ True)) ∧ p4))) ∨ p2) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149462543899514875624928639313 : ((False ∧ ((False ∧ (((p1 ∨ p1) ∧ p5) ∨ False)) ∧ ((((((p5 ∨ p5) ∨ p1) ∧ p5) → True) ∧ p4) ∨ p1))) ∨ ((p2 ∧ (False ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340908405703110042135902718007 : (p2 → (((((p5 ∨ p2) ∨ (p2 ∨ True)) ∧ ((p4 ∨ p2) ∧ p3)) → (p5 ∧ (p3 ∧ (p2 ∨ ((((False ∨ p5) ∨ p1) ∨ p5) → p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354868107646881528169194649924 : (p5 → ((True ∧ ((p5 ∧ (False ∧ p4)) ∧ (p3 ∧ ((((((False → True) → p2) → p2) ∨ p2) → (p3 → (False ∨ p3))) ∨ (p3 ∧ p1))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111661149162135687696851508978 : ((((p4 ∧ (p4 → (((False → (p3 → (p4 → p5))) ∨ p5) → ((p3 ∧ False) ∨ ((p3 → (p1 ∧ True)) ∧ p1))))) ∨ p3) ∨ True) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208290761713578780787752336366 : (((p2 ∨ p5) ∧ (p1 → (p2 ∨ p3))) → (((((False → (p3 ∧ (False ∨ False))) ∨ p5) → p1) ∨ (((p2 ∨ p5) ∧ p1) → (p4 ∧ p5))) ∨ True)) := by
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
theorem thm_5_vars_57979927335807442971675207176 : (((p4 → (p2 ∧ p1)) → ((p3 ∧ p3) → (((p1 ∧ p2) ∨ ((p2 ∧ ((True → (p3 ∧ p1)) ∨ True)) ∨ ((p3 → p2) ∨ p4))) → p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h2.left
        let h15 := h2.right
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h2.left
        let h18 := h2.right
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h2.left
        let h22 := h2.right
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h23 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h24 := h20 h23
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h2.left
        let h27 := h2.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h28 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h29 := h1 h28
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- One of the premise coincides with the conclusion.
        exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62094142025918018353945415486 : ((p2 ∧ (p4 ∧ ((p4 ∨ p2) ∧ (((((False ∧ p2) ∨ p1) → p4) ∧ (p5 ∨ p1)) → ((p3 ∨ (p1 ∧ p3)) ∨ ((True ∨ p2) ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199671743829412046672160906290 : ((((p1 ∨ p1) ∨ ((p1 ∨ p1) → p2)) → False) → ((((p1 ∨ p3) → (False ∧ p4)) → ((True ∨ p3) → (p5 ∧ p5))) ∨ ((False ∧ False) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 ∨ p1) ∨ ((p1 ∨ p1) → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h8 : (p1 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h9 := h2 h8
        -- We need to get the left conjuct of h9 based on <expert-advice>.
        let h10 := h9.left
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (p1 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- We need to get the left conjuct of h13 based on <expert-advice>.
        let h14 := h13.left
        -- False on the left can always be used.
        apply False.elim h14
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h5
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h17 : (p1 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h18 := h2 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h20 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h21 : ((p1 ∨ p1) ∨ ((p1 ∨ p1) → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h24 : (p1 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h24
        -- We need to get the left conjuct of h25 based on <expert-advice>.
        let h26 := h25.left
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h28 : (p1 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h29 := h2 h28
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- False on the left can always be used.
        apply False.elim h30
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h31 := h1 h21
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h33 : (p1 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h34 := h2 h33
    -- We need to get the left conjuct of h34 based on <expert-advice>.
    let h35 := h34.left
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172645554644222068493758541198 : (((p2 ∨ True) ∧ (((True ∨ (((p4 → True) ∨ True) ∧ (p2 → p4))) ∨ p4) → p3)) ∨ ((True ∨ ((p3 → p3) ∨ (p5 → p3))) ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178633872934553607790091128775 : ((((p5 ∧ p5) ∨ ((p1 → p4) ∧ p5)) → (p3 ∨ (False ∧ (p5 → p1)))) ∨ ((False → (p3 ∧ (((p4 ∨ p2) → p3) ∧ p3))) ∨ (True ∧ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917174550717493364124619968982 : ((((((p1 ∨ (p2 → p4)) ∨ (p3 ∨ ((p5 ∨ p5) ∨ ((p1 ∧ p3) ∧ p1)))) ∨ True) → (((p5 ∧ p1) ∧ False) ∧ (p3 ∨ (p4 → p5)))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (p2 → p4)) ∨ (p3 ∨ ((p5 ∨ p5) ∨ ((p1 ∧ p3) ∧ p1)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48980975309471782929847826375 : (((((True ∨ (p5 ∧ (p2 ∧ (p3 ∧ (p5 ∨ p5))))) ∧ (p2 → ((p3 → p2) → (p5 ∨ (p4 ∧ p2))))) ∨ p2) ∨ (p2 → (False ∨ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158129966194976411447427385576 : ((((False → (p3 → p5)) ∧ False) ∨ ((p2 ∧ (((p1 → (False ∨ (p5 ∧ False))) → False) ∧ p2)) ∧ True)) ∨ ((p1 → (p1 ∧ p3)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85464609224460538736657811427 : (((True → ((((p4 ∧ ((p3 ∨ p2) ∨ p1)) → p3) → p4) ∧ False)) ∧ ((((((p3 ∧ True) ∨ True) → (p2 ∧ p4)) ∧ True) ∧ True) ∧ True)) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351702928229796250469635612633 : (p4 → ((((p3 ∨ p1) → (p2 → p3)) ∨ (p5 ∨ (((False ∨ False) ∧ p4) → True))) ∧ (p3 ∨ ((p1 ∨ p1) ∨ (((p4 ∧ p1) ∨ p4) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110794986259777732732863735824 : ((((((p1 → ((p4 ∧ (((p1 ∨ p2) → p1) ∧ (p2 ∨ (True ∨ p4)))) ∨ (True → True))) ∧ p3) ∧ (True ∧ p2)) ∨ p4) ∧ True) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41162923520083575037875437241 : ((((True → (((((p1 → (True → p4)) → True) ∧ p5) ∧ (False ∨ ((p3 ∧ p5) ∨ (p5 ∨ p5)))) → p1)) ∨ (False → (p2 ∧ p3))) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_51311310693130543846139320867 : (((p3 ∨ ((((p1 → (p1 ∨ False)) ∧ (((p4 ∧ True) ∨ p2) → p1)) → p1) → (p2 ∨ p4))) ∨ ((p3 ∧ p1) → (True ∧ (False → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57598861288716667527902254367 : ((((p1 → p4) ∧ p1) → (((((((p5 ∨ False) → (p1 ∨ (p1 ∨ True))) → True) ∧ p4) ∨ (p2 ∨ ((p1 ∨ p3) ∨ p1))) → False) ∨ p1)) ∨ False) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56589271153843336852004978007 : (((p2 → ((p4 ∨ False) → p3)) → ((p5 ∧ (True → ((((False → p2) → p1) ∧ p1) ∨ (((False → p1) → p5) ∧ (p4 ∧ p1))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321474711138077413214955761540 : (p4 ∨ (p1 → (((p1 ∨ (((p5 → p4) → (True ∧ p2)) ∧ ((True ∨ ((True ∧ (p4 ∧ (p3 ∧ p3))) → (p2 ∨ p3))) ∧ p4))) → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50709231328104181194830353480 : ((((p1 → True) ∧ (True ∨ ((p2 ∨ (((((False → (True → p5)) → True) ∨ False) → p4) ∨ p2)) ∨ p1))) → ((p2 ∨ False) ∧ (p1 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159412885094100869113311601625 : ((((p1 → (p2 ∧ ((True → ((p5 ∨ ((p1 → True) ∧ p3)) ∧ p1)) ∧ (p4 ∧ False)))) → p2) ∧ True) → (((True → (True ∧ p4)) ∧ p5) → p4)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148611948602762168167142374911 : ((((p3 ∨ (p5 → (((p3 → p4) ∧ False) → p2))) ∨ p1) → ((True ∧ ((p1 ∨ (p3 ∧ p2)) → p4)) ∨ p2)) ∨ (((True → p3) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662276551194118283752459110792 : (((((((False ∨ False) → (p4 ∨ ((p2 ∧ False) → False))) → True) → ((((((p2 ∨ p5) → p5) → p5) → p2) ∧ p5) ∧ p1)) → (p5 ∨ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ False) → (p4 ∨ ((p2 ∧ False) → False))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213416693691173608510621477262 : (((p2 ∨ (True → True)) ∧ p3) ∨ ((((p5 ∨ ((False ∧ True) ∨ (True ∧ True))) ∨ (p2 ∧ False)) ∧ True) ∧ ((p1 ∨ (True → (True ∨ p2))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_41145867277135408525040196916 : (((((((p2 ∨ p1) ∨ (p4 → p3)) ∨ p2) ∧ ((p1 ∨ (True → (p2 ∧ p2))) → (p2 ∧ (p4 → p2)))) ∨ (p2 ∨ (p1 → True))) ∨ p3) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792889900951184973864677925980 : (((True → ((p1 ∨ (p5 ∨ p4)) → (True ∧ ((p3 ∧ ((p2 ∧ (((p1 ∨ (False → False)) ∧ p2) ∨ p3)) → p4)) → ((True ∨ False) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157491587968088962624110278610 : (((((False ∧ (p5 ∧ p3)) ∧ p4) ∧ ((p2 ∧ (p4 ∧ p3)) ∨ (p1 ∨ (p1 → p1)))) ∨ (p3 ∧ False)) ∨ ((p4 ∧ (p1 ∧ p4)) → (False ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741426333033452484447016662934 : ((((p5 ∨ p1) ∨ ((p4 ∨ (((p5 → ((((p5 ∧ (p1 → p3)) ∧ p5) ∧ p1) ∨ p3)) ∧ (p4 ∨ p2)) ∨ p4)) ∧ ((p4 → False) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185478688526030292779428355915 : ((p1 ∨ (p4 ∧ (p2 ∨ (p1 ∧ ((p4 → (p5 ∧ p3)) ∧ p1))))) ∨ (((p3 ∨ p3) ∧ ((p4 ∧ p1) → (((p3 → False) → True) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307810173224107044203040359230 : (p1 ∨ (p4 → ((((p1 ∨ (False → p5)) ∨ (((True ∨ p2) → p1) → False)) ∧ False) ∨ (((((p3 ∧ False) ∧ (p3 ∨ p1)) ∨ True) ∨ p1) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_116502004023749346574139885576 : (((p3 ∧ p4) ∧ ((True → p3) ∨ ((p2 ∨ ((((False → p4) → (((False ∧ p5) ∧ True) → p1)) ∧ (p2 ∧ p3)) → p4)) → p4))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64914147163838510664141460711 : ((p2 ∨ ((p4 → ((p3 ∧ ((True → (p2 ∨ ((p5 ∧ (True → (p5 ∨ False))) ∧ True))) ∧ False)) → p5)) → ((True ∧ (p3 ∨ p4)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207907544457016273762448336747 : (((p2 ∧ (p4 → p3)) ∧ (p1 ∨ p3)) → (p5 → ((p4 ∨ False) → (((((p5 ∧ p4) ∨ (True ∧ (p4 ∧ p1))) ∨ (False ∨ p5)) → False) → False)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : (((p5 ∧ p4) ∨ (True ∧ (p4 ∧ p1))) ∨ (False ∨ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : (((p5 ∧ p4) ∨ (True ∧ (p4 ∧ p1))) ∨ (False ∨ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346601762296700322791038062392 : (p3 → ((((p4 ∨ (p4 ∨ (((p2 ∧ p5) ∨ True) → p1))) → ((p5 ∧ (True → p2)) → (p1 → p2))) ∧ (p5 ∨ p3)) ∨ ((p5 ∨ True) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h15
      -- One of the premise coincides with the conclusion.
      exact h16
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608272615499204318582814448435 : (((((((p3 ∨ (((True → ((p5 → (p2 → p4)) ∨ (p3 → (p4 ∧ p2)))) ∨ p3) ∧ ((p3 ∨ True) ∧ True))) → False) ∨ p3) ∨ True) ∨ p1) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_691039602620799018091678572840 : (((((((p5 ∧ ((p3 ∨ p1) ∨ False)) ∨ (p5 → False)) ∨ True) ∨ (True → (p2 ∨ False))) → ((p2 ∧ p5) → (True → (True ∧ (p3 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166212091322384301625315804301 : ((p2 ∧ (((((p1 ∧ (p2 → False)) → (p2 → (p5 ∨ p4))) ∧ False) ∨ (p2 ∧ p4)) ∧ p5)) ∨ ((True ∨ ((p5 → True) ∧ p5)) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41249466347144547641885134242 : (((((((p3 ∧ p5) → p1) ∨ (((p3 → ((False ∨ p2) ∧ (p4 ∧ p5))) ∨ p1) → p2)) → False) ∨ (((p5 ∧ False) ∧ p3) ∨ p4)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169417904977234336243787462911 : ((((p3 ∧ (((p1 → p4) ∨ ((p1 ∨ (False → True)) → p1)) → p4)) → p2) ∨ True) ∧ (p1 → ((p1 ∧ (p3 ∨ (p4 → p1))) ∧ (p5 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81181956383513655380821409841 : (((p4 ∧ ((p2 → p2) → ((((((p3 → p3) ∨ p3) ∨ True) ∨ ((p3 ∧ True) ∧ p4)) ∨ True) ∧ (p3 ∨ p2)))) ∧ ((p3 ∨ p2) → p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133802211452160043549752843449 : ((((p5 ∧ (True → p5)) → ((p5 → p1) → ((p2 ∧ (((p4 ∧ p2) → p1) → (p2 ∨ (p2 ∨ p5)))) ∨ True))) ∧ p2) ∨ ((p1 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



