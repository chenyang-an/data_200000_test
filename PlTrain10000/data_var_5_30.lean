variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147477969925635477592357782665 : (((p2 ∧ ((p4 ∨ p3) → ((p5 → (p4 ∧ True)) → (((p4 ∧ p1) ∧ p1) ∧ (p2 → (p4 ∧ p4)))))) ∨ p1) ∨ (((p3 → True) ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736079253307989550850130064615 : ((((True → p5) ∧ ((((True ∨ ((p3 ∧ p4) → p4)) ∨ p3) ∧ p5) → (((p3 → ((False → True) → True)) → p3) ∨ (p3 → (p3 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208317654468099528415392924143 : (((False → p1) ∧ ((True → False) ∧ True)) → ((((((p3 ∧ p2) → False) → ((True ∧ p5) ∧ (p3 ∨ True))) ∨ (True ∨ True)) → (p4 ∨ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37787963012538175161284974652 : (((((p5 → p3) ∨ (((True ∨ p4) → (((p3 ∨ p1) ∨ ((False ∨ (p4 → p3)) ∧ False)) → (p1 → (p1 ∨ p2)))) ∨ p1)) → p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62571584596103680928623106097 : ((p3 ∧ (True → (p3 → ((p5 ∨ (p3 ∧ (((p4 → ((True ∧ ((p1 → p1) ∧ (False → False))) ∧ (False ∨ True))) ∧ p4) ∨ p4))) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197001067190365973008957597317 : (((((p2 ∨ p4) ∧ p2) ∧ (False ∨ p4)) ∨ p4) ∨ (((p5 → p5) ∨ p2) ∧ (True ∧ (((False → p2) → ((p2 ∨ p1) ∨ (p4 ∨ p1))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676564099942374708622806119543 : ((((p1 ∧ ((p1 ∧ ((((False ∧ ((p2 ∨ p1) ∧ (p4 ∧ False))) → False) ∨ p1) → p4)) → (p5 ∧ p4))) ∧ (((p3 ∨ p1) ∨ False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213980805745386565997002615435 : (((p4 → (p2 → p5)) ∨ p3) ∨ ((False ∨ ((p1 ∧ (p2 → p4)) ∨ (p4 → p1))) ∨ (((((True ∧ p2) ∨ p2) ∧ p5) → (p4 → True)) ∨ p4))) := by
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
theorem thm_5_vars_147800332466306710663831194935 : (((p1 ∧ ((False → p4) ∧ (p3 → (p5 ∧ ((p2 ∧ (False ∨ p2)) → ((p3 ∨ (p4 ∨ p1)) → p4)))))) → p5) ∨ (((True ∧ False) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744225746439098202447260630223 : ((((p1 ∧ p2) → (((p1 → (p3 ∧ False)) ∧ ((p5 ∧ (p3 ∨ p5)) ∨ p4)) ∧ ((p1 → ((False → False) ∨ (False ∧ (p4 → True)))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250940950243285095807477625434 : ((p1 → p4) ∨ ((((((False ∧ p5) ∨ ((((p4 → p3) ∧ p5) ∧ (p1 → (p2 → (p3 → p1)))) ∨ False)) → False) → p2) ∧ p5) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234127612792377473307205797862 : ((True → (p3 ∨ p2)) → ((((False → (((True ∨ (True ∧ p1)) ∧ False) → (p2 → p2))) → p3) ∨ ((True ∨ (p2 ∧ False)) ∨ (p2 → p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41019969979068165727689684889 : (((((((p2 ∧ (False ∨ True)) ∧ (((p2 ∨ (False ∨ p4)) ∨ (p2 → p1)) ∨ p4)) ∨ ((True ∧ False) ∨ p3)) → p1) → (False ∨ p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178006424932348901516593358400 : (((p3 ∨ (p4 ∧ (((p4 ∧ p1) ∧ (p2 ∧ p3)) ∧ (False → p4)))) ∨ True) ∨ ((p4 → p3) ∧ ((p5 ∨ p4) ∧ (p5 → ((True ∨ p3) ∧ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344771338812362583690337764673 : (p2 → (p4 → (((((p5 ∨ (p1 ∨ p3)) → ((((p2 → (p4 → True)) → p3) ∧ (p2 → (p3 ∧ p2))) ∨ p3)) ∨ (p2 ∧ p5)) ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65365701417180085173190274638 : ((p3 ∨ ((p5 → ((((p1 ∧ p5) ∨ (True ∨ p5)) ∨ p4) → (p4 ∧ p3))) ∨ ((True → False) → (((p4 ∧ (p1 ∨ p2)) → p1) ∧ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351448255122874601375448605967 : (p4 → (((((False ∧ ((p2 → (p5 ∨ p4)) ∨ p5)) → (p4 → (p5 ∧ True))) ∨ p2) ∧ ((True ∨ p4) ∧ p1)) → (p1 ∧ ((p1 → p3) ∨ True)))) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h16.left
    let h24 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175167458931328868477025327555 : ((True ∨ ((p1 ∨ (((((p4 → p3) ∧ p3) ∧ p2) ∨ p3) → p1)) ∨ (p4 ∧ p4))) → ((((False ∨ (p1 → (p2 ∧ False))) ∨ p5) ∨ True) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213542362160951256895268539137 : ((((p2 ∧ False) ∧ p2) ∨ p4) ∨ (((p5 ∨ (p5 ∨ (p1 → ((p3 ∧ (False ∨ p2)) → p4)))) ∨ (p1 ∨ p1)) ∨ ((p4 ∧ p5) → (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618242966299082911143308253197 : ((((((p2 → (p5 ∧ False)) ∨ p2) ∨ ((p5 → p5) → (p3 ∧ (((p5 ∨ (p4 ∨ p4)) ∨ (p4 → (True ∨ (p3 ∨ p4)))) → p4)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_114073506283312327368793978706 : ((((False ∨ (p1 ∨ (p4 ∧ p1))) ∧ ((True ∧ (((True → (p3 ∧ p5)) ∧ p1) ∨ p5)) ∨ (False ∧ p2))) ∨ (True ∧ (False → True))) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199650129628623208317020954711 : ((((False ∨ (p2 → p1)) → (p3 ∧ True)) → p1) → ((((((False ∨ ((p5 ∧ p4) → p1)) ∧ ((p2 → p1) → p4)) ∨ True) → False) ∨ p3) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((False ∨ ((p5 ∧ p4) → p1)) ∧ ((p2 → p1) → p4)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∨ (p2 → p1)) → (p3 ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344654320896445321111410123098 : (p2 → (p2 → ((True → (((True ∨ True) ∨ (((p5 → p5) → True) ∧ p3)) → (((p4 ∨ True) ∧ p2) → (p3 ∧ ((False ∨ p1) ∧ p5))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314841893017806391166997314221 : (p3 ∨ (((p4 ∨ True) → (False ∧ ((p5 → p3) ∨ ((p2 → p1) ∧ True)))) ∨ (False → ((p4 ∨ ((p4 → ((p5 → p1) ∧ p1)) ∧ p3)) → p1)))) := by
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165350282084649436269488355913 : ((((p3 → p3) → ((p4 ∧ (p1 ∨ (p5 → (p5 ∨ p4)))) ∨ p3)) ∧ ((p1 → p1) ∧ True)) ∨ (p4 ∨ ((False ∧ p1) → ((p3 ∧ p2) → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136598552715216453678649226859 : (((p4 ∨ (p2 ∨ p4)) ∨ (((False ∨ (p1 → p5)) ∨ (p1 ∧ (((p5 ∧ ((p2 → True) ∧ p2)) → p1) → p4))) ∧ p3)) ∨ ((p3 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148742477957641806243524310232 : ((((p5 ∨ (p4 ∧ p3)) ∧ (p2 → True)) ∧ ((p3 → p2) ∨ ((p5 ∧ True) ∨ (((p3 ∧ False) ∧ False) → p2)))) ∨ ((True ∧ p3) → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_620878037063006078070464309399 : (((((p2 ∨ True) → ((((True ∧ p5) → ((False ∧ False) ∨ (p3 ∧ p5))) ∧ ((p3 → True) ∨ False)) → (((p4 ∨ p4) → p2) → p1))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358611300800246814386764486081 : (p5 → (p3 → ((p2 ∧ (p2 ∧ p2)) ∨ ((True ∧ (False → True)) ∧ (((p3 ∧ ((True ∧ (p3 → True)) → (False ∨ (p3 → p5)))) → p2) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111947235201075230278669791920 : (((((((p5 → p2) ∨ p3) ∨ (p3 ∨ True)) → True) ∧ (((p3 ∧ p4) → ((p4 ∨ ((p3 ∨ p5) → False)) → p1)) → False)) ∨ p2) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166908097279814331556609587384 : (((((((True ∨ True) ∧ p5) ∧ p4) → True) ∨ ((((False ∨ p2) → p2) ∧ p4) ∧ False)) ∧ p3) → ((True ∧ p2) ∨ (((p4 → False) → p4) ∨ p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113598125178594451260460418639 : (((False ∨ (((p3 ∧ ((p3 ∨ (p3 ∨ ((p5 ∨ (p5 → p4)) → (p3 ∧ p1)))) → (False ∨ p4))) → False) ∧ p1)) ∨ (p2 ∨ p4)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223863208342554046223543019924 : ((p3 ∨ (p5 ∨ True)) ∧ (((False ∨ (True ∧ (p3 ∧ (p2 ∨ p1)))) ∧ (True → ((p2 ∧ p3) → ((p3 → True) ∨ False)))) ∨ (p2 → (p5 → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191732061821571278397705273614 : ((False ∨ ((p1 ∧ (p5 ∨ ((p4 ∨ p2) ∧ p4))) ∨ p5)) ∨ ((((True → p3) ∧ False) → False) ∧ ((p5 ∧ (True → (False ∧ p3))) → (p3 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593387999054152768108268861564 : ((((((p3 → ((True → (p3 ∨ p3)) → ((False ∨ (p3 ∨ p3)) ∧ ((p3 ∧ (True ∧ p1)) ∨ p4)))) → True) → ((p1 ∨ p5) ∧ p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53033158134719521241604037483 : (((((p4 ∧ False) ∨ False) ∨ (((p5 ∨ (p2 ∨ p3)) ∧ p5) ∨ p1)) ∧ (((p2 ∨ ((p5 ∨ p3) ∧ (p3 ∧ p3))) ∧ (False ∨ p1)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137875145893164820904617897355 : ((p4 ∨ (((((p4 → (p4 ∧ p1)) ∧ ((p5 → (False → ((p1 ∨ False) → (True ∧ p3)))) ∧ p4)) → p5) ∨ p1) ∧ p3)) ∨ ((False ∧ p1) → p3)) := by
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
theorem thm_5_vars_75647314673866993093705739291 : ((((((p1 ∧ (p3 ∧ (((p4 → p1) → True) ∧ p2))) ∧ ((((((p1 ∨ p3) → p1) ∧ p3) ∨ False) ∧ p2) ∧ False)) ∧ p4) ∨ True) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ (p3 ∧ (((p4 → p1) → True) ∧ p2))) ∧ ((((((p1 ∨ p3) → p1) ∧ p3) ∨ False) ∧ p2) ∧ False)) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324291547918254968164346669240 : (p5 ∨ (((True ∨ (((True ∨ p3) → p3) ∨ p1)) → p3) → ((p1 ∧ (p3 ∨ p1)) ∨ ((((p5 → True) → (p4 → p1)) → p3) ∧ (p3 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((True ∨ p3) → p3) ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208589470075560344135326419134 : (((p1 → p5) → (p1 ∧ (p1 ∧ p3))) → ((p4 ∨ (p5 → (p1 ∨ (p3 ∨ p5)))) ∨ (p3 ∧ ((True ∧ (True → (p4 → p2))) ∧ (False ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149014654257289176706811156585 : ((((p5 ∧ p1) ∨ p1) ∨ (((p2 ∨ p3) ∨ ((True ∧ p4) → p1)) ∨ ((True ∧ True) ∨ ((False ∧ p2) ∨ p4)))) ∨ ((p4 ∨ p3) ∨ (p2 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66459801097635120101330913684 : ((True → (((p5 → False) → (True ∧ (((p3 ∧ (p5 → (True → p3))) ∨ (p2 ∨ (p4 ∧ p2))) ∧ (((p5 → p1) ∧ p5) → p4)))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200270178986460159851122342930 : (((p2 ∨ (True ∨ False)) → (p5 ∧ (True ∧ True))) → (p4 → (((False ∨ False) ∨ ((p5 → p4) → (p5 ∧ (p1 ∧ p2)))) ∨ (p4 ∨ (p1 → p1))))) := by
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
theorem thm_5_vars_614046811259463680276569467755 : (((((True ∧ (((p1 ∧ (False ∧ (p5 → True))) ∨ (p2 ∧ p2)) ∨ ((p1 ∨ p2) → (p1 ∧ (p1 → p2))))) ∨ (p5 → (False ∨ True))) ∨ p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111288127402469549092184067820 : ((((p3 → False) → ((p4 ∨ p5) ∧ (((((p4 → ((p4 → p4) ∧ p5)) ∧ (p1 ∧ (False → p2))) ∨ p3) → p3) ∨ True))) ∧ p4) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141927994018998194627159223776 : (((p1 ∧ p5) → (((False ∧ False) → p5) → (False → (((p5 → p1) ∧ (p1 ∧ (p5 → ((p5 ∨ p5) → p4)))) ∨ True)))) → ((p4 ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113729772337759465751061175180 : ((((p4 → (((p5 ∧ False) ∧ (p1 ∨ True)) ∧ ((p1 ∧ (p2 ∨ p5)) → (p1 ∧ p3)))) ∨ (True → (p1 ∨ p5))) → (p4 → p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206128118265314996241805255937 : ((p4 ∧ ((p5 ∨ p1) → (p5 → False))) ∨ (((p2 ∧ p1) → p4) → ((p5 ∧ ((p5 → (True ∧ (False ∧ False))) ∧ p1)) ∨ (p1 → (p2 → p1))))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208986477329204902095041567847 : ((True ∨ (p3 → (p5 ∧ (p5 → p4)))) → (((False → False) → False) ∨ ((True ∨ (((p4 → ((p4 ∧ True) ∨ (p2 ∧ False))) → p2) ∨ False)) → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349043285210574705185555310306 : (p3 → (p5 ∨ ((False ∧ ((p2 → (((p4 → False) → (((True ∧ (p4 ∨ True)) ∧ False) ∨ (p1 ∨ p3))) ∧ (False ∨ p1))) ∧ True)) ∨ (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591471827306357409279510569437 : (((((False ∧ (False ∨ (((((p1 ∨ p3) ∨ True) ∨ ((p2 ∧ False) ∧ (True → p2))) ∧ (p1 → p3)) ∧ (p5 → p1)))) ∧ (p5 ∨ p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49507817248952693678791514967 : ((((p3 → (((((p2 → p4) → ((p3 ∧ p4) → ((p4 → p4) → p5))) → (p5 ∨ p2)) ∨ p5) ∧ True)) → p5) → (p5 ∧ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233682592854362307381928553827 : ((p2 ∨ (p1 → p1)) → (((False ∨ ((p4 → p2) → p1)) → (((p4 → (((p3 ∧ p2) → ((p4 ∧ True) ∧ False)) ∨ p5)) ∨ p3) ∧ p1)) ∨ True)) := by
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
theorem thm_5_vars_666961019940906682054717361981 : (((((p5 ∧ ((p3 → True) ∧ p3)) ∧ (p4 ∨ ((p5 ∨ p3) ∧ (((True ∨ True) → p5) ∧ (True → (p1 ∧ True)))))) ∧ ((True ∨ False) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339724191380452652746341219825 : (p1 → (p4 ∨ (((p3 ∨ (((p2 → p5) ∧ (False ∧ (p4 ∧ p3))) ∨ (((p1 ∧ (p2 ∨ p2)) ∨ p1) → (p4 ∨ False)))) ∧ (p3 → p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65216299133609012212590106618 : ((p3 ∨ (((p2 → (p1 ∨ ((p1 ∧ p4) ∧ (p3 ∨ p1)))) ∨ ((False → ((p2 → False) → ((p5 ∨ p2) ∨ (p1 ∧ True)))) ∨ p5)) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66275005362174246742904859101 : ((p5 ∨ (((p2 → p5) ∧ p2) → (((p4 ∧ (False ∧ p4)) ∨ (p2 ∨ (p4 ∨ (True → True)))) → (p5 ∧ (p1 ∧ (True ∨ (p4 → True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167480558870006222444862029143 : (((((False ∨ (p3 ∨ p2)) ∧ (((p1 ∧ p1) → p1) ∧ (p3 ∨ True))) ∧ p1) ∧ (p4 ∨ p3)) → (p1 → (((p1 → False) ∧ p1) → (p5 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h12.left
      let h17 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h19 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h20 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h21 := h5 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h23 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h24 := h5 h23
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h26 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h27 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h28 := h5 h27
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h30 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h31 := h5 h30
          -- False on the left can always be used.
          apply False.elim h31
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h12.left
      let h34 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h36 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h37 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h38 := h5 h37
          -- False on the left can always be used.
          apply False.elim h38
        case inr h39 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h40 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h41 := h5 h40
          -- False on the left can always be used.
          apply False.elim h41
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h43 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h44 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h45 := h5 h44
          -- False on the left can always be used.
          apply False.elim h45
        case inr h46 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h47 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h48 := h5 h47
          -- False on the left can always be used.
          apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255676986248512980416673070520 : ((p5 ∧ p5) → (((p5 ∧ (False ∧ ((((False ∨ p2) → (p4 ∨ p5)) ∨ p5) → False))) ∨ (((False ∧ p3) ∨ p5) ∨ (True ∨ True))) ∧ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608369406449267359981125309800 : ((((((p5 ∧ (False ∧ ((((p5 ∨ (p4 ∨ p1)) ∨ p1) → ((p5 → ((p5 ∧ p5) ∧ (p2 ∨ p5))) ∧ p3)) ∨ False))) ∨ True) ∨ p2) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616832143448353326610084225866 : ((((((((False ∨ p4) → True) ∨ ((p5 ∨ p1) ∧ p5)) ∧ p4) → (p1 → (False ∨ (False ∨ ((p1 ∧ False) ∨ (p3 ∨ (False ∨ p4))))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314460542933700888671000120112 : (p3 ∨ (((((True ∧ ((True → p5) ∧ p4)) → p2) ∨ ((p5 ∨ (p5 ∧ (p4 → True))) → p2)) ∧ (True → p2)) → (False ∨ (p5 ∨ (p2 ∨ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196759617770524838581213736515 : ((((False ∨ (p5 ∨ p3)) ∨ (False ∧ p3)) ∧ p4) ∨ (((((p3 ∧ p3) ∨ ((p5 ∧ False) ∧ True)) ∨ False) ∨ (False → p3)) → (p2 ∨ (p4 ∨ True)))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
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
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115058645360931528653242490160 : ((((p1 ∨ ((p3 ∨ p4) ∨ (p3 ∨ (p3 → p5)))) → (True ∧ p3)) ∨ ((((p2 ∧ False) ∧ p5) → ((False ∨ False) → p5)) ∨ p1)) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245424274143446006675829325740 : ((p2 ∧ p4) ∨ ((((p1 → False) → (((p2 → (p1 ∧ (True ∧ p4))) ∨ True) ∧ True)) ∧ False) ∨ (p4 ∨ ((p5 → ((False → True) ∨ True)) ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148682745469466657746648841212 : (((((p3 ∨ p3) ∨ False) ∨ ((p5 ∧ True) ∨ p5)) ∨ ((((p2 → p3) ∧ p1) ∨ p3) → (p5 → (p1 → p2)))) ∨ (((p4 ∨ p2) ∧ False) → p1)) := by
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
theorem thm_5_vars_729471801029502862157745269015 : (((((False ∨ True) ∨ p1) → (p3 ∧ (((p1 ∨ (((p4 ∧ p5) ∨ (p1 ∧ ((p3 ∧ (p1 ∧ (p2 → p3))) → p3))) → False)) ∧ False) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180596931046017308764556615345 : (((((p3 ∨ (p1 → p4)) ∨ p3) ∧ p1) ∧ ((p1 ∨ (p2 → p4)) → p2)) → ((((((p3 ∨ p5) → p2) ∧ (False ∨ p1)) ∧ p1) ∨ p4) ∨ p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112876857534011448278636542362 : ((((True → (p2 ∨ p2)) → ((False ∧ (p4 → p1)) ∨ ((p2 → p3) → ((p5 ∧ ((p2 → p1) ∨ (False → False))) ∨ False)))) → p3) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111469522237101201656756088921 : (((p1 → ((((p3 ∨ ((p5 → ((p1 → True) ∨ ((p4 ∧ (p3 ∧ p2)) ∨ False))) ∧ (p2 ∨ p3))) ∧ p3) ∨ p2) → False)) ∧ p1) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340242386745792028218493033729 : (p1 → (p5 → ((True ∨ p1) ∧ ((((p3 → (p3 ∨ (p2 → p3))) → (False ∨ False)) ∨ (((((p2 ∨ False) ∨ p1) ∨ p4) → p3) ∨ p1)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593958639397954466016742836867 : (((((((p4 ∨ p1) ∨ p3) → (((p3 → (p5 ∨ (True ∨ (p1 → (p1 ∨ False))))) ∧ False) ∧ p3)) ∨ ((p3 ∧ p4) → (p4 ∧ p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41853086671766044268932603279 : (((((p1 ∧ p3) ∧ p2) ∨ ((p3 ∧ ((p4 ∧ ((p2 ∨ (p1 → (p1 ∧ p1))) ∨ (p4 ∧ p1))) ∨ p4)) → ((True ∧ False) ∧ p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312263790296026042106046557966 : (p2 ∨ (p1 → ((True ∧ True) → (((((p5 ∨ True) ∧ (((p5 → (p1 ∧ p3)) ∧ p5) ∨ False)) ∧ p2) ∨ p2) ∨ ((p1 → (p4 ∨ True)) ∨ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167373213774158817063438718772 : ((((False ∧ ((p2 ∧ p2) → p2)) ∨ ((((p3 → p4) ∧ p2) ∧ (p4 ∧ True)) ∧ p1)) → p5) → ((p1 ∨ True) → ((p1 ∧ p5) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149570778211892953748889123361 : ((p2 ∧ (p1 ∨ ((((p2 → p1) ∧ (((p3 ∨ (p2 ∨ p4)) ∧ False) → p5)) ∧ ((p3 ∨ False) ∧ p2)) ∨ p4))) ∨ ((p2 → (p3 → p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45005177170011093262515098776 : ((((p2 ∧ p2) ∨ (((p5 ∧ (p1 ∧ True)) ∨ p1) ∧ (p4 ∨ (p3 → ((((p4 → True) ∨ (p2 ∨ (p1 ∨ p4))) ∨ p1) → p4))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64800725573879620587825979696 : ((p2 ∨ ((p2 ∧ (True ∧ (p4 ∧ ((True → (p2 ∧ (((p1 ∨ ((False ∨ (p1 → p5)) ∧ p3)) ∧ p4) ∨ (p3 ∧ p2)))) ∨ p1)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695653759046373511296916500665 : ((((((p3 ∧ p4) ∨ ((p2 ∨ p1) ∨ True)) → (((p1 → False) → p5) ∨ False)) → ((p5 ∨ p3) ∨ (True ∨ (p2 ∧ (p2 → (p1 ∧ p1)))))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177924682432174043951685260295 : ((((p5 ∧ ((True → p1) ∧ (True ∧ p2))) → (p4 ∨ (True → False))) ∨ p2) ∨ ((p1 ∧ (True → (((True ∨ p2) ∧ True) ∨ p5))) → (p3 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751644703547205439960944522049 : (((True ∧ (p3 ∧ ((p1 → (p3 ∨ (False ∨ (p4 ∨ (p4 → ((p3 → (False → p4)) ∧ ((p5 → p3) ∧ p1))))))) ∧ ((p1 → p3) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720418062930713914720597919261 : (((((True ∧ (False → p4)) ∨ p4) → (p5 ∧ ((True → p2) → ((p4 → (((p2 ∧ p5) ∧ False) ∧ p5)) ∨ ((p3 → p2) ∨ (p2 → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118425215743402046186498540878 : ((p2 ∨ (p2 ∨ ((p4 ∨ ((((False ∧ p5) → True) ∧ False) ∨ (((False ∨ (True ∧ ((p2 ∧ p2) ∧ p1))) ∨ p4) ∧ False))) ∨ True))) ∨ (p3 ∧ p1)) := by
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
theorem thm_5_vars_44043391291052237971015165260 : ((((p1 ∨ (((True ∧ p2) → (False → ((True ∨ (p5 ∨ p3)) ∧ (p4 ∧ ((p4 ∧ p1) ∨ p4))))) → (True ∨ p4))) → (p5 ∧ p4)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216986152049656102417917949081 : (((p4 → (p3 ∨ p1)) ∧ p1) → (((((p1 ∨ (((p2 ∨ True) ∨ p2) ∧ p5)) ∧ (True ∨ p2)) → ((p1 ∨ p4) → p3)) ∧ p1) → (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 ∨ (((p2 ∨ True) ∨ p2) ∧ p5)) ∧ (True ∨ p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608583524099542133612826340411 : ((((((p5 → (p5 ∧ (False ∨ ((p5 ∧ (p1 → (((p3 → True) ∨ p1) ∧ ((p3 ∧ p3) ∨ (p5 → p3))))) → p2)))) → False) ∨ True) ∨ p4) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_46626993392593121642790030620 : (((p4 ∧ ((((p2 ∧ ((p4 → p5) ∨ p4)) ∧ (p1 ∧ False)) ∧ (((True ∧ (p1 → p1)) ∧ p2) ∨ p3)) ∨ (True ∧ p4))) ∧ (True ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64516872206950775004940682128 : ((p1 ∨ (((((False → False) → (False → p1)) ∨ p3) → (p3 ∧ (True ∨ False))) → ((((p3 ∨ p3) ∧ p5) ∧ ((True ∨ p2) ∨ False)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148433172907023410512955688078 : (((p1 ∧ ((((p1 → p2) ∧ (p3 ∨ (False → p4))) ∨ (p2 → p2)) ∧ p1)) → (((False ∨ False) → p4) → p5)) ∨ (((p3 → True) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53789519142023151231218937483 : ((((((p3 ∧ (p4 ∧ p3)) → (p4 ∧ p5)) ∧ True) → False) ∨ (((True ∨ (((p2 → (p1 ∧ p1)) → (True ∧ True)) → False)) → False) → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p2 → (p1 ∧ p1)) → (True ∧ True)) → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328706863767362038695984139574 : (True → ((((p3 → False) ∨ True) ∧ ((((p5 ∧ p5) ∧ p1) ∨ False) ∧ p4)) ∨ ((p1 → ((p3 ∨ (p3 ∧ p1)) ∨ ((p1 → p3) → p1))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137051553477926752121399345630 : (((p1 → p1) → ((((p3 ∨ p5) ∨ p1) ∨ (((p2 → p5) ∨ (((p4 → p5) ∨ p2) ∨ (p2 ∧ p5))) → p2)) ∧ True)) ∨ ((p1 → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66492098448419876854659829806 : ((True → ((((p2 → (p1 ∧ p5)) ∧ (p5 ∧ p4)) ∧ ((((p5 ∧ (p4 ∧ p2)) ∨ (p3 ∨ (False ∨ True))) ∨ p5) ∧ (True → p2))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43207208905004952731256801643 : ((((p2 ∧ (((True ∨ (p3 → (False → ((p4 → (True ∧ p4)) ∨ (p3 → ((p4 ∧ (p3 → p2)) ∨ p5)))))) ∧ p3) ∨ False)) ∧ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698430618373633109140523842089 : ((((((p2 ∨ p3) ∧ (p2 → (True ∧ p5))) ∧ (p4 ∨ (False ∧ p1))) ∨ ((p2 → (p3 ∨ ((((False → p5) → p3) → p5) → p2))) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323894473646108271594762028855 : (p5 ∨ (((((((p5 ∨ p1) ∧ False) ∧ (False → (p5 → p3))) ∨ p1) ∧ p5) ∨ (p3 → p3)) ∨ (p4 → ((p3 ∧ ((p1 ∧ p3) → p3)) → p4)))) := by
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
theorem thm_5_vars_150212556056658670915409202253 : ((p2 → (((p4 ∧ (p1 ∧ p1)) → True) → ((((p1 ∨ p5) → (p1 → p3)) ∧ ((p2 → p3) ∧ p5)) ∨ p2))) ∨ ((p4 ∨ (p3 ∨ p2)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142232890888498867115703257835 : ((p1 ∧ (True → ((p3 ∨ (((p1 ∨ p4) ∧ (False → (((p4 ∧ (True → p2)) ∨ p2) → p3))) → p3)) ∧ (False ∨ p5)))) → (p1 → (True → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135993509279936745681508011650 : ((((p4 ∨ p2) ∧ ((((p4 → p3) → p5) ∨ p4) ∧ False)) ∨ (True → ((p5 ∨ ((p5 ∨ (False → p4)) → p4)) ∧ p3))) ∨ (True ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179424536278899733501220495593 : ((p4 ∨ ((p5 → ((p5 ∧ p5) → p4)) → ((p3 → p3) ∧ (p4 → False)))) ∨ ((False → p1) ∨ (p1 → ((p5 ∨ (p4 ∨ False)) ∧ (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



