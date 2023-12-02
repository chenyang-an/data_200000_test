variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55981979320036924757303093604 : ((((p1 ∧ (p5 ∨ p4)) ∧ p3) ∨ (False ∨ ((p2 ∨ (p1 ∨ p2)) → ((p1 ∨ p4) ∨ ((((p5 → (p3 ∨ p4)) → p3) ∧ p4) ∨ True))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60148351565253862262878579781 : (((p4 ∨ p3) → (((((p4 ∨ p2) ∨ (False → True)) ∨ (p1 ∨ (((p2 → p3) ∧ p2) → (((p3 ∨ p4) ∨ p4) ∧ p2)))) → p5) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187543375249599112332743516032 : ((p2 ∨ ((((p4 → p1) ∧ False) → (p2 ∨ p3)) ∧ (p4 ∧ True))) → (p1 → (((p5 → p2) ∧ p3) ∨ (((p3 ∧ p3) ∧ False) → (True ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136797527967416448214208837809 : (((p2 → p2) ∧ ((p3 ∧ (True → p1)) ∨ ((p5 ∧ True) ∨ (p2 ∧ (p3 ∨ (True ∨ (p3 ∨ ((True ∧ False) ∧ False)))))))) ∨ (p4 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703360931761428706123447098688 : ((((False ∨ (((False → p5) → p4) ∧ (p4 → (p5 → True)))) ∨ (p5 ∧ ((((p5 ∨ (p5 ∨ p3)) ∨ p1) → p1) ∧ ((p2 → p3) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197817305533902360201798644894 : ((((p4 ∨ p3) → False) ∨ (p3 ∧ (p3 ∧ p3))) ∨ ((((((False ∨ p2) ∨ p4) ∧ p3) ∨ p5) ∧ (p5 ∧ p5)) → (True ∨ (p1 ∧ (p3 ∨ p4))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h3.left
        let h11 := h3.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598964756985897890000590163063 : (((((p1 ∨ p5) ∧ ((True ∨ True) ∧ (((p2 ∧ False) ∨ (((False → ((False ∨ p3) → (p4 ∨ False))) ∧ p2) ∧ (p2 ∨ p3))) → p4))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42553129846809905125956031830 : (((p1 ∨ ((True → p5) → ((p3 ∧ (p3 ∧ False)) ∧ (p2 → (((((p5 ∨ False) → p2) → (p5 ∨ p5)) → (p1 → p3)) ∧ True))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783610486995443664462107007673 : (((p3 ∨ (((((p2 ∨ False) ∧ (p1 → p3)) ∨ p5) ∨ True) ∧ ((((((p1 ∧ False) → p1) ∨ p5) ∧ p3) → (p3 ∨ p3)) → (False ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740978009310842829020034002225 : ((((p3 ∨ p3) ∨ (p4 → ((True ∧ p4) → (((p5 ∧ (False ∧ (False ∧ (False → ((p2 ∧ True) → ((True → p1) → p1)))))) ∨ True) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642005508708607407098114703099 : ((((True ∧ (((False → (p5 ∧ p3)) ∨ (p1 ∧ ((((False ∧ p3) → True) ∧ (((p5 ∨ p2) → (p2 ∧ True)) ∨ p1)) ∧ p3))) ∧ p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9619332667522476711249325049 : ((((p3 ∨ False) ∧ ((p4 ∨ True) ∧ ((p2 → (p5 ∧ (p4 ∨ p1))) ∧ (((p1 → p1) → ((p4 ∧ p1) ∨ False)) ∧ (p5 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42659702546315649415309121592 : (((p4 ∨ ((((p2 → (p5 ∧ (p2 ∨ (p3 ∨ p4)))) → (p3 → False)) → ((p5 → p3) ∧ p5)) ∨ ((True ∨ (p5 → p2)) ∨ False))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70691114027303736511737824785 : ((((((True → False) ∧ (p1 ∨ ((p5 → (p4 ∧ p5)) ∨ (False → (p2 → True))))) ∧ p4) ∧ ((False → ((False ∨ p2) → False)) → p3)) ∧ p4) → p5) := by
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
  cases h9
  case inl h10 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h19 := h8 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42885598548250942641083022726 : (((p3 → (((p1 ∨ True) → (((p5 → p3) ∧ p3) → ((((p4 ∨ (p1 ∧ (p2 ∨ p4))) → (False ∧ p1)) ∨ p1) ∨ True))) ∨ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185039870055447164487699164776 : (((p2 → False) ∧ ((p4 ∧ p1) ∧ (((False ∨ False) ∨ p4) ∧ p2))) ∨ (((p1 → ((p1 ∨ p4) ∨ (p2 ∨ p5))) ∨ (False ∨ p4)) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698089248968931452555173719909 : (((((p3 ∧ ((p2 ∨ ((p3 → p4) ∧ (p4 → p3))) ∧ p4)) ∨ p1) ∨ (p4 → ((True → p2) ∨ ((p4 ∧ p3) ∧ ((p2 ∧ p3) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227618847761906368561022133373 : ((False ∧ (False ∨ p5)) ∨ (((p5 ∨ p3) ∨ p2) → ((True ∧ (((p1 ∧ ((p2 → (p5 ∧ p2)) ∨ True)) ∨ (p5 ∨ (False → p2))) ∨ p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151027295704187103317234205861 : (((((((((p2 ∧ (True ∧ (True ∧ p3))) ∧ True) ∧ (p5 ∨ (p2 → p4))) ∨ p1) → p2) ∧ p5) ∧ p4) → p3) → (((True ∨ p1) → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149717630418993447953427163120 : ((p5 ∧ (p4 → ((p2 ∧ p3) ∨ (p3 ∨ ((((False ∧ ((p5 → (p5 ∧ p5)) ∧ p4)) ∧ p2) ∨ p2) ∨ p5))))) ∨ ((False → False) ∨ (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139886291414104465374356946958 : (((((((True ∧ p1) → p3) → ((p1 → (False ∨ (p1 → p2))) → ((p2 ∧ p1) → p5))) → p1) → p5) ∧ (p5 → p2)) → ((p2 → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792930931292560748908161586197 : (((True → ((True ∨ p5) ∧ (False ∧ (p5 ∧ ((p2 ∨ (True → (p5 ∧ p2))) ∧ (((p4 → (False → p1)) → p5) ∨ ((p3 → p5) ∨ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300416840515542336543783497685 : (False ∨ ((p4 → (p3 ∨ (p2 ∧ (p3 → ((((p5 ∧ (True ∨ ((p5 → False) ∧ (p3 → p1)))) ∨ p1) ∧ True) ∧ p1))))) ∨ ((True → True) ∨ p5))) := by
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
theorem thm_5_vars_47962535433171977168768738304 : ((((((False ∧ (p4 ∧ (p3 ∨ ((False ∨ (p5 → (p4 → p1))) ∨ p2)))) ∨ p1) → p5) ∧ ((True → (p4 ∧ p3)) ∧ p3)) → (True → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601645873378291192742594947287 : ((((p3 ∧ (p3 ∧ (((p2 ∧ (((True ∧ (p3 → p3)) ∨ p1) ∨ (p1 ∧ p3))) ∧ p2) ∧ ((p5 ∨ (p5 ∧ (True → p5))) → p1)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58772338210480255348088692178 : (((p4 → p3) ∧ (((((p4 → p3) ∧ (((p1 → p3) ∨ ((p3 ∨ p5) ∧ True)) ∨ p2)) ∧ p1) ∧ (p2 ∨ (p3 ∧ p2))) ∨ (p3 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467501613481139594940532091009 : (((((p5 ∨ (p2 ∨ ((p2 → True) ∨ ((True ∨ False) → True)))) → (p4 ∧ p1)) ∨ (True ∧ ((p4 ∨ (False → p2)) ∨ (False ∧ (p3 ∧ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642700246590184944525716757349 : ((((p1 ∧ (((True ∨ p5) ∨ (p2 → p5)) ∨ (((p5 → ((p4 ∨ (False ∧ (p4 ∧ p5))) → False)) → (p5 ∧ p3)) ∨ (p5 ∨ False)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218967597956975774056090669015 : ((p4 ∧ ((p5 ∧ p4) ∨ p2)) → (((True ∧ p1) ∧ (((p2 ∧ p3) → True) ∧ ((p3 → (p3 ∨ p5)) ∧ (((p1 ∧ True) → p3) ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
theorem thm_5_vars_676006910034270793940182702285 : (((((p1 ∨ (((p3 ∨ (p3 ∨ p2)) → p1) ∧ True)) ∨ (True → (((p4 ∧ False) ∨ (p2 ∧ p3)) ∧ p2))) ∧ (p5 ∨ ((False ∧ p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_462972673487301554062215965515 : (((((p5 → (((((p4 ∨ p5) ∨ p5) ∨ p3) ∧ p5) ∧ p1)) → ((p3 ∨ False) → p4)) ∨ ((False ∨ ((False ∨ p4) ∨ p1)) ∨ (p4 ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41562221086712669062973218384 : ((((((p2 → False) ∨ p2) ∧ (p4 ∨ ((p1 → p2) → p1))) → (((True ∨ True) ∨ (p1 → p4)) → ((p2 ∨ (p2 → p4)) ∨ p1))) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h12 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h13 := h7 h12
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h25 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h26 := h20 h25
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h1.left
    let h32 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h35
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h36 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h38 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h37
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h39 := h33 h38
        -- False on the left can always be used.
        apply False.elim h39
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h41 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h42 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59933798006420573490809731184 : (((True ∨ True) → (p3 ∨ ((((((True ∨ False) ∨ p2) ∧ (p1 → (((p3 ∨ False) ∨ p5) → ((p2 → p3) → True)))) → p4) → p4) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111572969939043470046284847220 : (((((True → False) ∧ ((p2 → p5) ∨ (True ∧ (((p1 ∧ p2) ∨ True) ∧ (p3 ∧ (((p3 ∨ p3) ∨ p5) → p5)))))) ∧ p3) ∨ p4) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755098796283845136216676165072 : (((False ∧ (p1 → ((p2 ∧ (p4 ∧ ((p2 ∨ p3) ∧ (False ∨ p1)))) ∨ (False ∧ ((p3 ∧ ((p2 ∨ ((p4 → True) ∧ p1)) → False)) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115264586436597383166539106011 : ((((p4 ∨ p5) → ((((p3 ∨ p5) → p4) ∧ p4) → p1)) ∨ (((p5 → (p1 ∨ p5)) → (False ∨ p4)) ∧ ((p1 ∧ p4) → p5))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232229438778562417242190122919 : (((p1 → p1) → p5) → ((p2 ∨ ((True ∧ p3) ∨ (p1 → ((p5 → False) ∧ (p5 → (((((p4 ∨ p2) ∨ False) ∨ True) ∧ p4) ∨ True)))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113496413621086977202846781473 : (((((p4 ∨ (p1 ∨ (((p4 → True) ∨ False) ∧ p5))) ∧ (((p5 ∨ p1) ∨ p3) → p4)) ∨ ((p5 ∨ True) ∨ True)) ∨ (p4 ∨ False)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259484533121713852084547025378 : ((False → p4) → (p4 → (p3 → (p4 ∧ ((((p5 → (p4 ∧ p4)) ∧ p4) ∨ True) → ((p3 → p4) ∧ ((p4 ∧ ((p3 → p2) ∧ True)) → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171538928218376039983607983027 : ((((p2 ∧ ((((p4 ∧ p5) ∧ p2) → p1) → (p2 ∧ (p5 ∧ p4)))) ∨ p2) ∨ p1) ∨ (p3 → (p4 → (p1 → ((p1 ∧ p3) → (p5 → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601881872496214541538917184225 : ((((p4 ∧ ((p5 ∧ (p2 → p3)) → ((p3 ∧ p4) ∧ ((False → (p3 → ((p2 ∨ p1) ∨ p1))) ∧ (p5 ∧ (p2 → (True ∨ p3))))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248604704479613417033929696397 : ((p3 ∨ False) ∨ (False ∨ (((False ∧ (((p3 → p4) → p5) ∧ False)) ∨ (True ∨ False)) ∨ (True ∧ (p2 ∧ (p2 → ((False ∧ (p5 ∨ p5)) ∨ True))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141736444774661748967051916934 : (((True → False) ∧ ((((True ∧ True) ∧ True) ∨ (((p1 → p2) → p2) ∧ (p2 ∧ (True ∧ p5)))) ∧ ((p5 → p3) → p1))) → ((p4 ∧ p3) ∨ p1)) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628271491479423602699103476079 : ((((((p1 → True) ∨ (p1 ∨ (p2 ∨ (((p3 ∧ (p5 ∨ p3)) ∨ ((False ∨ p2) → (p4 ∧ ((p2 → p1) → p3)))) ∧ p1)))) ∧ True) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257755294758787409713424244139 : ((p3 ∨ p4) → ((False ∧ ((p1 → (p2 → False)) ∨ (p3 ∧ (p4 ∨ p4)))) ∨ ((((p5 → p1) → ((False → p5) ∨ p4)) ∨ (p1 ∧ p2)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56970946262242866168453364380 : (((p3 ∨ (p4 ∨ p5)) ∧ (((((True → ((True → p3) ∨ ((p5 ∧ p1) ∨ (p1 → (True ∧ p4))))) ∨ p1) ∨ (False ∧ p4)) → p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205380736503714642161020034704 : ((((True → True) ∨ p2) → (False ∧ p3)) ∨ ((p4 ∧ p3) → ((p2 ∧ (False ∧ p3)) ∨ ((p2 → p3) ∨ (False ∨ ((p3 ∧ (p4 → p1)) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353978157324754166876690620400 : (p4 → (p3 → (((((p5 ∨ p5) ∨ (p3 ∧ (((p3 ∨ p3) → p2) ∨ True))) → False) ∨ p4) ∧ (((p5 ∧ True) → (p2 ∨ p2)) → (p4 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708139625470886280693378621341 : ((((True → (p5 → (p2 ∧ ((True ∧ False) ∨ p5)))) ∨ (((p2 ∧ (False ∨ ((p4 → p3) ∧ p5))) → p4) ∨ ((p3 ∧ p3) → (True → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69035624990733198320751747552 : ((p5 → (((p4 → (p2 ∧ ((False → True) → ((True ∨ (False ∨ (((True → False) → p2) ∧ (False ∨ p2)))) ∧ p1)))) → (p2 ∧ p2)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224025885870242493563699109616 : ((p4 ∨ (p5 → p5)) ∧ (p4 ∨ (p2 → (True ∧ (((False → False) ∨ p5) → (p5 ∨ (p1 ∨ (p3 ∨ ((p4 → ((True → p3) → p4)) ∨ False))))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54064888912995302066163689292 : (((((p3 → False) ∧ p3) ∨ (False → (False → (False ∧ p5)))) → (p2 ∧ (((p4 ∧ (p3 → p3)) → p3) → ((p4 → False) ∧ (p4 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254231676334417980268183123846 : ((p2 ∧ p2) → (((p4 ∨ p4) → (((p2 ∧ (p5 ∧ p5)) ∨ (True ∧ p1)) ∧ p5)) ∨ ((p2 ∨ ((p1 ∨ True) → (p1 → p2))) ∧ (p4 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55331666545750956152712549004 : (((p4 ∨ (p2 ∧ (p4 ∧ (True → p4)))) ∨ ((p4 ∨ (p3 → ((False → p2) → p1))) ∨ (p2 ∨ (((p1 → (p2 ∧ p5)) ∧ False) ∨ True)))) ∨ p4) := by
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
theorem thm_5_vars_315751346973876754461421367218 : (p3 ∨ ((p5 → p1) ∨ ((p4 → p1) → (p3 → (((p1 ∨ p4) ∧ (((p2 → p2) → False) ∧ (p3 ∧ (((True ∨ p4) → True) ∨ True)))) → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : (p2 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h12
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h16 : (p2 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h18 := h7 h16
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h25 : (p2 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h27 := h20 h25
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h29 : (p2 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h31 := h20 h29
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55755296369281659186990807483 : ((((False → (p5 ∧ p4)) → p3) ∧ (((p1 → (False ∨ (p5 ∨ ((p5 ∧ p1) → ((p1 ∧ False) ∧ (True → (p5 → p5))))))) ∨ False) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113724796356580383212339593443 : (((((p5 → (p4 ∨ False)) ∨ (p5 ∧ (p5 ∨ ((True → ((p2 ∨ True) → p1)) ∧ p5)))) ∧ (p4 → (p4 → p4))) → (True → p3)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747324714189797185331050411348 : ((((p5 ∨ p4) → ((((((False → p2) ∧ (p4 ∨ p4)) ∧ (p4 ∨ (p4 → True))) ∨ (p2 ∨ (p1 ∨ p1))) ∨ ((p5 ∨ True) → False)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747415607601625956947438336488 : ((((True → True) → (((p5 → (False ∧ False)) ∧ ((p5 ∧ False) → p3)) → (p5 ∧ ((((p1 ∧ p2) ∧ (p5 ∧ False)) → (True → p1)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178428846137416534668166726895 : (((((p4 ∧ (p1 ∨ (p3 → p4))) ∨ p3) ∧ p5) ∧ ((False ∨ True) ∧ False)) ∨ (False ∨ (False → (((False ∨ (True ∧ p1)) ∧ (p4 → p3)) → p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52070460816200035401477663743 : (((((((p4 ∧ ((p3 ∨ p4) ∨ p3)) → p1) → (p3 → p5)) → (False ∧ False)) ∧ p3) → ((p1 ∨ ((p2 ∨ (p2 ∧ False)) → p4)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45030715942509957531024837551 : ((((p2 ∨ p2) ∨ ((((p4 → p2) ∧ (((p5 ∧ (p2 ∨ p3)) → ((False ∨ p1) ∧ (p2 ∧ True))) → p3)) ∨ (p5 ∨ p4)) → True)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116188654592328669043819646646 : ((((False ∧ False) ∧ p5) ∨ ((((p4 → True) ∨ (p1 ∧ True)) ∧ (False ∨ ((p5 ∨ p3) → (p5 → (p5 ∧ (p1 ∨ p4)))))) → p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873888145624411098820488129707 : ((((p4 → ((False ∨ (((p4 → (p1 ∧ (p3 ∨ p2))) ∨ (p5 → True)) ∨ p2)) → ((p2 ∨ (p1 ∨ ((p2 → True) → p1))) ∨ p4))) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((False ∨ (((p4 → (p1 ∧ (p3 ∨ p2))) ∨ (p5 → True)) ∨ p2)) → ((p2 ∨ (p1 ∨ ((p2 → True) → p1))) ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165527855333802296018821586300 : (((p3 ∧ ((p3 → p5) → ((p1 ∨ p2) ∧ (p5 ∧ p1)))) → ((p4 ∧ (False ∨ p5)) ∧ True)) ∨ (False → ((((p3 ∧ True) → p4) ∨ p4) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264974492757509292644741904567 : (True ∧ ((p5 ∨ True) → (((p3 ∧ False) ∨ ((((p4 → (((p4 ∨ (p4 → p3)) ∧ p1) → True)) ∨ p2) → (p1 → p5)) ∨ (p4 → False))) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40941010488862603874030367301 : ((((((((p1 ∧ False) → (p1 → (p2 → p2))) ∨ ((p4 → (p2 ∨ True)) → ((p1 ∨ p5) ∧ p3))) ∨ p1) → p2) ∨ (p3 → p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118326328309633389980954369695 : ((p2 ∨ ((((False ∨ (((p3 ∨ p4) → p5) ∨ (p5 → (((p4 ∧ (p5 → p5)) → p3) ∧ (False ∨ p4))))) ∧ p3) → p2) ∧ p1)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219450358509008375058244627448 : ((p4 ∨ (True ∧ (p3 → p1))) → (p3 ∨ (p1 → ((((p5 ∧ (p1 ∨ (p4 ∧ p5))) → p2) ∨ True) ∨ ((p2 → ((False ∨ p5) → p4)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60437491903681575143589269015 : (((p4 → p5) → (((True ∨ (p4 ∧ p5)) → (((p1 ∧ p4) ∨ ((True ∧ p3) ∨ p2)) ∨ p5)) ∧ (((p3 ∨ True) ∨ p2) ∧ (p3 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37436407520814918807290918574 : ((((((False ∨ (((True → (p2 ∨ p2)) ∧ (True ∨ p4)) ∨ (p1 ∧ (p5 → False)))) ∨ p3) ∨ ((p3 ∧ (False ∨ p5)) ∧ p1)) ∨ p5) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228400526990365608582089387220 : ((False ∨ (True ∧ p5)) ∨ ((True → p1) → (p3 ∨ (((p2 ∨ (((p4 ∨ p1) ∨ (p4 ∨ True)) ∨ (False ∧ True))) ∧ ((False ∧ p5) → p1)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41195150071452731398441595177 : (((((p3 ∨ p4) ∧ (((p2 ∧ p2) → (p1 ∨ p4)) ∧ (p4 ∧ (((p4 ∨ True) ∧ p2) ∨ (p1 → p2))))) → (p1 ∧ (p4 ∨ True))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191425111334169001226152735606 : (((p1 ∨ p3) → (((False → p5) → (p1 ∨ p2)) ∧ False)) ∨ (p5 → (True → ((p4 ∨ ((p1 → p1) ∧ (((p2 → p4) ∨ p2) ∨ True))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232017750584852456425890047422 : (((p3 ∨ True) → False) → ((False ∨ p1) ∧ ((p5 → ((((True → True) → p5) ∨ (p4 ∧ False)) → (p1 → p2))) → (p2 → ((p1 → p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218535202219599166314386615068 : (((p5 ∨ True) → (p5 ∨ False)) → (True ∧ ((((p1 ∨ p2) ∨ (((True → p1) ∨ p5) → (p3 ∨ p4))) ∨ (p2 → ((p3 ∨ False) ∨ True))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205304437729393389910543746559 : (((False ∨ (p3 ∧ True)) ∨ (p1 ∧ p5)) ∨ (((p1 ∨ p3) → (p1 ∨ ((p3 ∧ ((p2 ∨ (p4 → p2)) ∧ (p2 ∧ p4))) → p2))) ∨ (p5 → False))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51383458619558999381326061356 : (((((((False → p2) → (p1 ∨ p1)) ∧ p2) ∧ (p3 ∨ (((p5 ∨ p5) ∧ p1) → p5))) ∨ False) → (p4 ∨ ((p4 ∨ (True ∨ p3)) → p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h4
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h8
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h16 =>
            -- One of the premise coincides with the conclusion.
            exact h11
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h17
    case inr h23 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h24 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- False on the left can always be used.
        apply False.elim h25
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h26 := h5 h24
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h32 =>
            -- One of the premise coincides with the conclusion.
            exact h27
      case inr h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h34
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h38 =>
            -- One of the premise coincides with the conclusion.
            exact h33
  case inr h39 =>
    -- False on the left can always be used.
    apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181534511353068468987976938395 : ((True → ((p3 → p2) ∨ (((p1 ∨ (p5 ∨ p4)) → (p5 ∨ p5)) ∧ True))) → ((((p4 ∨ (True → p1)) ∨ False) ∨ (p3 → (p2 ∨ True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_117589982153328277814601865643 : ((p2 ∧ (p3 ∧ ((p1 ∧ True) → ((p5 → (p4 ∧ ((p2 ∨ p5) ∨ p4))) ∧ (p5 ∧ (p2 ∧ (((True ∧ p3) → p5) ∧ True))))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67531973949521837512908633629 : ((p1 → ((True → ((True ∨ p2) → p5)) ∨ (((((p4 → p2) ∧ True) ∧ (p4 ∨ (False ∧ (True ∨ ((p1 → p3) → p2))))) → p5) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52056183040810789308417091509 : (((p4 → (((p2 → ((p3 → False) ∨ (((True → p4) ∧ p3) ∨ p4))) → p3) ∨ False)) ∨ (((False ∨ (p5 ∧ (False ∧ False))) → False) ∨ p4)) ∨ p2) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45482242041164897323886663923 : (((False ∨ ((p2 → ((True → (p4 ∨ (False ∨ p4))) → False)) ∨ (((p5 ∨ p5) ∨ ((p4 → p3) ∧ ((p3 ∧ p2) ∧ p5))) ∨ p5))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1784282892638056496312233780 : (((True → (True → (p4 → (p2 → ((p3 ∧ ((p4 → p1) → p5)) ∨ (p1 ∧ p4)))))) → ((p1 → p5) ∧ p2)) ∨ ((True ∧ False) → p4)) := by
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
theorem thm_5_vars_146936525212510483595529893882 : ((((((p4 ∧ ((p3 ∨ p3) ∨ (p1 ∧ p2))) ∨ ((p5 → (p5 ∧ p4)) → (p5 → p2))) ∨ True) ∨ p2) ∧ p3) ∨ (((False ∧ p3) ∧ p2) → p1)) := by
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
theorem thm_5_vars_233820754546033133714226126415 : ((p3 ∨ (p4 → p5)) → ((((((p3 ∧ p3) → (False → p5)) ∨ p5) → p1) ∧ (p3 ∨ ((False → (p1 ∨ False)) → ((p4 ∧ p3) ∨ p5)))) ∨ True)) := by
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
theorem thm_5_vars_58085097832386070400696231119 : (((p1 ∧ False) ∧ ((((p3 ∧ p4) ∨ ((((((p4 ∨ p5) → p2) ∧ (p1 ∧ p2)) → ((p5 ∨ p5) → False)) ∧ p2) → p4)) ∧ p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654134135252252395213475609362 : (((((((p5 → (p2 ∨ False)) → ((p3 → True) → (((((p5 ∨ True) → p5) ∧ (p5 ∨ p3)) ∧ p1) ∧ p1))) ∧ p4) ∨ True) ∨ (p1 ∨ p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_167157113637381524256867260115 : ((((p3 ∧ (p3 ∨ p4)) ∨ (True → ((False ∨ p2) ∧ ((False → p5) ∨ (False ∨ p1))))) ∨ p3) → ((p5 → False) → (p3 ∨ (False ∨ (False ∨ p2))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193241284640031413441379305048 : ((((p1 ∨ p4) → p1) ∧ ((p1 ∨ p5) ∧ (p5 → False))) → ((p4 → p1) ∧ (((p3 ∨ ((p3 → False) → p5)) ∨ ((p1 ∨ p1) ∧ True)) ∨ p4))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305798934031128846860813990746 : (p1 ∨ (((True ∧ ((p3 → (p3 ∧ p2)) ∨ True)) → False) → ((p5 ∨ (((True → False) ∨ p2) → p1)) ∧ (False ∧ (((p3 → p5) → True) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((p3 → (p3 ∧ p2)) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ ((p3 → (p3 ∧ p2)) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∧ ((p3 → (p3 ∧ p2)) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46385601351594391165626444500 : ((((((((p5 ∨ True) → p5) → p3) → p2) ∨ (p4 ∧ True)) ∨ ((p4 ∨ p2) ∨ ((p1 → ((p2 ∨ True) → p3)) ∨ True))) ∧ (p1 → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147331091497247906621771100872 : (((((False ∨ ((p4 ∧ p5) ∨ (((True ∧ True) ∨ True) ∧ (p5 ∧ (p3 ∧ p2))))) ∧ True) ∨ (False → p5)) ∨ p1) ∨ (True ∧ (False ∧ (p5 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159467977007515922343967524603 : (((((True → (p3 ∨ p4)) ∨ (False ∧ (p1 ∧ p4))) → ((False → p5) → (True ∧ (p4 → p2)))) ∧ p2) → (True ∧ (p4 → ((True → p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111188794445183806431370402707 : (((((p4 ∧ p5) ∧ False) ∧ ((True ∧ p4) → (p3 ∨ (False ∨ (((False → p1) ∧ p3) ∨ (p2 → (True ∨ (p2 → False)))))))) ∧ p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117163043836477247017299056497 : ((True ∧ ((p4 ∧ ((p5 → ((True → (p2 ∨ p3)) → (p4 → (p2 ∧ (p3 → (p5 ∧ p1)))))) ∨ (p2 ∨ (True ∨ p1)))) ∨ p5)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754227411793959949898417650964 : (((False ∧ ((p1 ∧ p5) ∧ ((p3 → ((p2 ∧ (((p5 ∨ ((p3 ∨ ((p4 → p5) ∨ False)) → False)) ∧ p4) ∨ False)) → (p5 ∨ p5))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117031850252676944612814602759 : (((p2 ∨ p5) → (((p3 ∨ (((p5 ∧ (p4 ∧ ((p2 ∨ (p2 → False)) ∧ ((p2 ∧ False) ∨ p4)))) → p1) ∨ False)) ∨ p4) → p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932193849364326756932061504734 : ((((((False → (p2 ∧ p4)) → p1) ∧ (p4 → p1)) ∧ (((p1 → p1) ∧ p2) ∧ (p1 ∧ (True ∧ ((p5 → ((True → p3) ∨ p4)) ∧ True))))) → p1) ∧ True) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797257587627981685805185854415 : (((p1 → (((p5 ∧ (p3 → (p1 ∨ (((p4 ∧ ((p2 ∨ False) → ((True ∨ ((p1 → p5) ∧ p3)) → p2))) → False) ∨ p4)))) ∨ p3) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



