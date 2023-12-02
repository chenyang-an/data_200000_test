variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37795826724181020762629532961 : ((((True ∧ ((((((True → p5) ∨ (((False ∧ False) → (p4 → p4)) ∨ (p5 ∧ p4))) → p2) ∨ p5) ∨ (p1 ∧ p3)) ∨ False)) → p4) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52542686986042532667359912990 : ((((((p4 → p3) ∧ ((False → False) → ((p5 ∨ p3) ∧ p1))) ∧ p2) → p4) ∨ ((p3 ∧ p5) ∨ (p4 → ((p3 → (p3 ∨ p1)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312483630190437876040675984807 : (p2 ∨ (p5 → ((((p1 → p4) ∧ ((((False → p1) ∧ p1) ∧ p4) ∨ p2)) ∨ ((p5 → (True ∧ p3)) ∨ ((p2 → True) → p1))) ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_113619458780215266024382150677 : (((True → (p3 ∨ (p4 ∧ (p5 ∨ (((False → ((((False ∨ p3) ∨ p3) → (p1 → p2)) ∨ p4)) ∧ p5) ∨ p4))))) ∨ (p3 → p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172801265643045759785004818307 : (((p4 → p5) → ((p5 ∧ ((p1 ∨ p3) ∨ False)) ∨ (((p5 → p1) ∨ False) → p4))) ∨ (False → ((p1 → True) ∨ (((p2 → p3) ∧ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165141951829648670048543241684 : ((((p3 → (((p1 ∧ ((p1 → False) ∧ p4)) → (p3 ∨ True)) ∧ True)) → p4) ∧ (True → p2)) ∨ ((True → (((p1 ∧ True) ∧ p4) → p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148856075533806226749739620719 : (((p2 ∧ (p2 ∧ (p4 → p1))) ∧ ((((p1 → True) → p4) → p3) → (p4 ∧ (((p3 ∧ p2) → p3) → p2)))) ∨ (False → (True ∧ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199923051165653242935020155825 : ((((p3 ∧ p5) ∨ (False ∧ p2)) ∨ (p3 → True)) → ((((p4 ∧ (((False ∨ (p4 ∨ p4)) ∨ p1) → p5)) ∧ (p4 → False)) → (False ∨ False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h16 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h18 := h4 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110815922736017991664807868142 : ((((((p2 ∧ (False ∨ p2)) ∧ False) ∧ (p1 ∧ (p3 ∨ (((True → p1) → ((p2 ∨ (p5 ∧ False)) → True)) ∨ True)))) ∨ p4) ∧ False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322362284133768597768297911037 : (p5 ∨ (((((p5 → (((((p4 ∧ (p3 → False)) ∧ False) ∨ p4) ∨ p4) ∧ p1)) → p2) ∧ (p2 → (True ∧ False))) → ((True → p4) ∨ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_349320922789376089244773434546 : (p3 → (p2 → (p5 ∨ ((((p4 ∨ True) → ((True → p1) ∨ (True ∧ ((p5 ∧ (p5 → ((p1 → True) ∧ (p1 ∧ False)))) ∨ p3)))) ∨ False) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341676574850730369029682155991 : (p2 → (((p4 ∧ ((((False ∨ True) ∨ p2) → ((((p4 ∨ p1) → p5) ∨ p4) ∧ p2)) ∨ (((p1 → p5) ∧ p4) → p3))) ∨ True) ∨ (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137490544047058243958391218373 : ((p5 ∧ (((p2 ∧ ((p3 ∨ (((p1 ∨ ((p2 ∧ p1) → p5)) ∧ ((p1 ∨ p2) ∨ p2)) ∨ p2)) ∨ True)) ∧ p1) → p3)) ∨ ((p4 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225632114571348400928096822337 : (((p1 → p4) ∧ p3) ∨ ((p4 ∧ ((p4 → (p3 ∧ (p1 → (p5 ∧ False)))) ∨ ((True → p2) ∧ (p5 → p2)))) ∨ ((p1 ∧ False) → (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53901354575208127395318954960 : (((p3 ∧ (((False ∨ p1) ∧ False) → ((False ∨ p1) → False))) ∨ (((False ∨ True) ∨ False) → (p3 ∧ (((p4 → p3) ∧ p5) → (p4 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346806295670365858060074036425 : (p3 → ((p3 → (((p4 ∨ ((p1 ∧ p4) → p5)) ∧ False) ∧ (p3 → ((((p2 ∧ p1) ∧ p4) ∧ True) ∧ p4)))) ∨ (p4 → (p1 → (p5 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606138038116201016686408870029 : (((((((((True ∨ (((p4 ∧ p2) ∨ p3) → ((p2 ∧ ((p2 ∨ p4) → p1)) ∨ False))) ∨ p3) → (p3 ∧ p5)) ∨ True) ∧ p3) ∧ False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_164774921524520778459640480633 : ((((((p3 ∧ (p1 → p2)) → p2) → (p2 ∨ p4)) → ((False ∧ (p5 ∧ p2)) ∨ p1)) ∨ p3) ∨ (p1 ∨ ((p3 ∧ (p2 ∧ (False ∨ p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135907254325875197320270837231 : (((((p3 ∨ p2) ∨ (False ∧ (False ∧ (p2 → True)))) → (p1 ∨ p2)) → (p3 ∧ ((False → ((p5 ∧ False) ∨ True)) ∧ p5))) ∨ ((p4 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319385054595436361651042368026 : (p4 ∨ ((p4 → ((p3 ∧ ((p3 ∧ False) ∨ (p3 ∨ ((p4 → p2) → False)))) ∨ p4)) ∨ (p2 ∧ ((False ∨ False) ∨ (p1 → (True ∨ (p5 ∨ False))))))) := by
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
theorem thm_5_vars_59542723063031383945081784814 : (((p3 → False) ∨ (((((True → True) ∧ (p4 → (p5 ∨ True))) → p4) ∧ ((p4 ∧ ((p1 → p3) ∧ p2)) ∨ (p2 → p4))) ∨ (p2 → True))) ∨ p5) := by
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
theorem thm_5_vars_962295401150599137970209418963 : ((((p5 ∨ p4) ∧ ((p4 ∨ ((True ∨ False) ∧ True)) ∧ ((((p2 → p1) → False) ∧ (True ∧ p1)) ∧ ((p1 → (p4 ∨ (p5 ∨ p3))) → p2)))) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : (p2 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h16 := h10 h14
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h6.left
        let h22 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h27 : (p2 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h29 := h23 h27
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h3.left
    let h33 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h41 : (p2 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h42
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h43 := h37 h41
      -- False on the left can always be used.
      apply False.elim h43
    case inr h44 =>
      -- Conjunctions on the left can always be decomposed.
      let h45 := h44.left
      let h46 := h44.right
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h47 =>
        -- Conjunctions on the left can always be decomposed.
        let h48 := h33.left
        let h49 := h33.right
        -- Conjunctions on the left can always be decomposed.
        let h50 := h48.left
        let h51 := h48.right
        -- Conjunctions on the left can always be decomposed.
        let h52 := h51.left
        let h53 := h51.right
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h54 : (p2 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h55
          -- One of the premise coincides with the conclusion.
          exact h53
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h56 := h50 h54
        -- False on the left can always be used.
        apply False.elim h56
      case inr h57 =>
        -- False on the left can always be used.
        apply False.elim h57
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135465306505407522877686580923 : (((((((p4 ∨ p4) ∨ p4) ∧ ((False → p2) ∧ p1)) → (False ∨ (p1 → False))) ∨ (p1 ∨ p5)) → ((p2 → False) ∧ p4)) ∨ ((True ∨ p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159742040033304975633066267759 : (((((p1 → True) ∨ (p3 ∨ p4)) ∧ (((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) → False)) ∨ False) → (p3 → (False ∧ ((p1 ∧ p5) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h11 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h12 := h5 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h14 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h15 := h5 h14
        -- False on the left can always be used.
        apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h21 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h22 := h19 h21
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h25 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h26 := h19 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h28 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h29 := h19 h28
        -- False on the left can always be used.
        apply False.elim h29
  case inr h30 =>
    -- False on the left can always be used.
    apply False.elim h30
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h35 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h36 := h33 h35
      -- False on the left can always be used.
      apply False.elim h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h39 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h40 := h33 h39
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h42 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h43 := h33 h42
        -- False on the left can always be used.
        apply False.elim h43
  case inr h44 =>
    -- False on the left can always be used.
    apply False.elim h44
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h45 =>
    -- Conjunctions on the left can always be decomposed.
    let h46 := h45.left
    let h47 := h45.right
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h48 =>
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h49 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h50 := h47 h49
      -- False on the left can always be used.
      apply False.elim h50
    case inr h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
        have h53 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h47, we can now drive its conclusion.
        let h54 := h47 h53
        -- False on the left can always be used.
        apply False.elim h54
      case inr h55 =>
        -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
        have h56 : ((p2 ∨ (True → False)) ∨ ((p1 ∧ p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h47, we can now drive its conclusion.
        let h57 := h47 h56
        -- False on the left can always be used.
        apply False.elim h57
  case inr h58 =>
    -- False on the left can always be used.
    apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677189183862209799391227846110 : ((((((((False ∨ ((p5 ∧ (p3 ∨ (p5 ∨ (p3 → (p1 → True))))) ∧ False)) → False) ∨ p3) → p4) ∧ False) ∨ ((p5 → (p4 ∨ p3)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337363495094128844851486942023 : (p1 → (((((p3 ∨ (p1 ∨ (p2 ∧ (p4 ∧ False)))) → (p1 ∧ True)) → (p4 ∧ p1)) ∧ ((True → (p3 → p2)) ∨ p5)) ∨ ((p5 ∧ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624632231232337869902362925784 : ((((p4 ∨ ((p2 ∧ (p5 ∧ p5)) ∧ (p1 ∨ (((((p2 ∧ p2) → ((p1 ∨ (p2 ∨ p1)) ∧ True)) ∨ (p4 ∨ True)) → p4) ∨ False)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_52946075491757684995440836007 : ((((((p4 ∧ (p4 → p3)) → (p3 ∧ (p5 → p3))) → p5) ∨ p1) ∧ (True ∨ ((p3 → p5) → ((p3 → (p5 → True)) ∧ (p3 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117223694741188609633930404635 : ((True ∧ ((p2 ∨ p3) ∨ (p1 → ((((p3 → (((((False → (p2 → p4)) → p2) ∨ p5) ∧ p3) ∨ p3)) ∨ p1) ∨ p5) ∨ p3)))) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639036963379663853039854867818 : ((((((p5 ∧ (p3 → p1)) ∧ p1) ∨ (p4 → (p5 ∨ (p5 ∧ (((True ∧ p1) → (p2 → (p2 ∨ (p4 → (p2 ∨ p5))))) ∨ p5))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114146901154209785747963110966 : ((((((p5 ∧ (((((p1 ∨ p4) ∧ p2) → False) ∧ (p1 → True)) → True)) ∨ (p3 → False)) → True) ∨ True) → ((p2 ∨ p5) ∨ p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688946816236678021615818449385 : (((((p5 ∨ ((((((p4 → p4) → p4) → p1) ∨ p3) ∨ p2) ∨ (p2 ∧ p2))) ∧ p4) ∨ (p4 → ((p1 ∧ True) ∨ ((p5 → p5) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65865392212662126941775339484 : ((p4 ∨ ((p4 → p1) ∧ ((((((p4 → p4) → p3) ∧ (((p5 ∨ p2) ∧ p2) ∨ p4)) ∧ p2) ∨ (False → False)) → (p3 ∧ (p2 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247762212601110453044178317347 : ((p1 ∨ False) ∨ (p3 → (((((((p5 ∧ False) ∧ p5) ∧ (((False ∧ p4) → ((False ∨ p5) → p5)) → p1)) → p1) → (p2 ∧ True)) → p1) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187628529056455452900827285132 : ((p5 ∨ (((p5 → p5) ∨ (((p4 ∨ False) ∧ True) ∨ False)) ∨ False)) → ((True → (False → True)) → (True → ((True → p4) → (True → (False ∨ p4)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h19 =>
            -- False on the left can always be used.
            apply False.elim h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727917161898985276858274743416 : ((((p2 ∨ (p3 ∨ False)) ∨ ((p2 ∨ ((False ∧ p4) ∨ True)) ∧ (p5 ∧ ((p2 ∧ p4) ∧ ((p3 ∧ (p1 ∨ (True ∧ True))) ∨ (p5 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303867081604362356225334644497 : (p1 ∨ (((p4 ∨ (p4 ∨ (((True ∧ p4) ∨ ((True → p3) ∨ (((p4 → p1) ∨ True) → (p1 → p3)))) ∨ p5))) ∨ (p5 → (p3 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115155021970587358592860469037 : (((p1 → (((True ∧ p3) → ((True ∧ (p4 → True)) ∧ p2)) ∨ p2)) → (((p3 ∧ ((p5 → p4) ∨ False)) ∧ (True ∨ p1)) → p5)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47161597364392149859658331355 : (((((False ∧ ((True ∨ False) ∧ (((p1 → p3) ∧ (p2 ∨ p5)) ∨ p5))) ∧ True) ∧ ((p4 ∨ (p2 → (p2 → p5))) ∧ p3)) ∨ (False → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140852635228863268826092678397 : ((((((p1 ∧ False) → (True → (p3 ∨ p3))) ∨ (p1 ∨ False)) ∧ True) → (((p4 ∧ (p3 ∨ (p3 → False))) ∨ True) → False)) → (p3 ∨ (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ False) → (True → (p3 ∨ p3))) ∨ (p1 ∨ False)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 ∧ (p3 ∨ (p3 → False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113611266594289214077483380355 : (((p4 ∨ ((((True → p3) ∨ (p1 → p2)) → ((p4 ∨ (p1 ∧ (False ∧ p2))) ∧ ((p3 ∨ False) ∨ p5))) → p1)) ∨ (p5 → p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451284830063334380627772324661 : (((((((((False ∧ p1) → p4) ∨ True) ∨ (((p5 ∧ (p2 → p5)) → p3) → p3)) → False) ∧ (False ∨ p5)) ∨ (p1 → ((p5 → p1) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38510450075233701990202077818 : ((((p5 ∨ (((p3 ∨ p4) → (p3 ∨ (p3 ∧ p3))) ∨ (p1 ∧ p2))) ∨ ((p4 ∨ p2) ∨ ((p5 ∨ p1) ∨ (p4 ∧ (p2 ∨ p2))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23070411958515333807148993652 : ((((((True ∧ p3) ∨ p2) ∧ p1) → False) → ((((((p5 ∧ (p1 → p5)) → (False ∧ p1)) ∧ False) ∨ False) ∨ p3) ∨ (False → (False → False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122341393277892239081967799477 : ((((((p2 ∨ (((p2 ∨ ((p4 → p5) → p4)) ∨ True) ∧ (p2 → p1))) ∨ (p5 → p2)) ∨ (True ∧ True)) ∧ True) ∨ (True ∨ p5)) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h14 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324077409691553704355364098975 : (p5 ∨ (((((False → p4) ∧ ((p4 ∧ True) ∨ p1)) → False) ∧ (p5 → p5)) ∨ (((p3 → (p2 ∨ False)) ∨ (False ∧ (p5 ∨ False))) ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228883428483704483394525151377 : ((p4 ∨ (p1 ∧ p4)) ∨ (p2 ∨ ((p4 ∧ ((((((p5 ∧ False) ∧ False) ∨ ((p4 ∧ p2) ∧ (p3 ∧ p2))) ∨ (p4 ∧ p5)) → True) → p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((p5 ∧ False) ∧ False) ∨ ((p4 ∧ p2) ∧ (p3 ∧ p2))) ∨ (p4 ∧ p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345364012709768871370540541813 : (p3 → ((((p3 → (((p3 → False) ∨ False) → ((True → (((p1 ∧ p5) ∧ p4) ∨ ((p2 → False) ∧ p1))) ∧ p5))) ∨ (False ∨ False)) ∨ p2) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138267196154485384075503807811 : ((p2 → (p1 → (((p4 → p3) → ((False ∨ p4) ∨ False)) ∨ ((False ∨ (p1 → p2)) ∨ ((p2 ∧ (p1 → False)) ∧ p3))))) ∨ ((True → p1) ∧ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260034371291936651970540313291 : ((p2 → False) → (((p4 ∧ ((((((p1 ∨ p4) ∨ False) ∨ p5) → ((p5 → p1) ∨ p5)) ∨ p2) ∨ True)) → (((p5 → p3) ∧ False) ∨ p4)) ∧ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192820850009499910023590142170 : (((p3 → ((p1 → p5) ∨ ((p2 → p4) → p2))) → p1) → ((False ∨ (((True ∧ True) ∧ False) ∧ True)) ∨ (p2 ∨ (((p4 ∧ p2) ∧ True) → p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p3 → ((p1 → p5) ∨ ((p2 → p4) → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112440057107222459043248265390 : (((((True → ((((p2 → ((((p5 ∨ p3) → (False ∧ p3)) ∧ (p2 ∧ p5)) ∨ p4)) ∧ p4) → p3) → p1)) ∨ p3) ∨ p4) → p3) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177771841708946151344723811477 : (((False ∧ (p1 ∨ (True ∧ (((p1 → True) → (p3 → p1)) → False)))) ∧ p2) ∨ ((False ∧ p4) ∨ ((p4 ∨ ((p1 ∨ (p4 ∧ p3)) ∨ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_65364829995804827162672664942 : ((p3 ∨ ((True ∧ ((p1 → (True ∧ p3)) → (p5 ∨ (p5 ∧ (True → p3))))) ∨ (False → ((True ∨ ((p5 ∨ True) → p2)) ∧ (True ∧ True))))) ∨ p1) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199730228063366321511725593391 : (((False ∨ (p1 ∨ (p3 → (p5 → p5)))) → p4) → (((p5 → (False ∨ p1)) ∨ True) ∨ ((p1 → p1) → (((p2 ∧ p4) → p3) → (True ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114304321103000687851338608301 : ((((p1 ∧ ((p3 → ((p5 ∧ p3) → p3)) → (p1 → p5))) ∨ ((p4 → (False ∨ p4)) ∨ p5)) ∧ (p5 ∨ (p1 ∨ (True ∨ p3)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322257727082835140668268345848 : (p5 ∨ (((((p5 → p4) ∨ (p4 ∧ (p3 ∧ p4))) → ((p5 ∧ (p4 ∨ ((p5 → p4) ∨ p2))) ∧ (p3 ∧ (True ∧ (p1 ∨ p1))))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191618470985557466169055120951 : ((p3 ∧ (False ∧ (((p4 ∧ p4) ∨ False) ∧ (False → p1)))) ∨ (((p2 → p4) ∧ ((p1 ∧ p1) → (False ∧ (False → (False → p3))))) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157834611396938577824575578761 : (((False → (((((p5 → p3) → p1) → (p1 ∨ p2)) → p4) ∨ True)) → (False ∧ (p3 → (False ∨ p5)))) ∨ ((p1 ∧ ((p3 ∨ p3) ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342293179833497990775364810956 : (p2 → (((p2 → False) ∧ ((p4 → p5) ∨ (p1 → ((((p5 ∨ p5) ∧ (False → p2)) ∨ p4) → False)))) ∨ ((p3 ∧ (False → (p4 ∧ p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171160869465721232855201815360 : ((p1 → ((False ∨ p1) ∧ ((p3 → p3) ∧ ((((p5 ∨ p4) ∨ p3) ∨ True) ∨ p4)))) ∧ (False ∨ (False → ((p3 ∧ (p3 ∧ (p1 ∧ p3))) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323193142339666028354665442032 : (p5 ∨ (((((p5 ∨ p4) → (True ∧ p3)) → (p4 → (((((((p5 ∨ True) ∧ p2) ∨ p5) ∨ True) ∨ False) ∨ p4) ∧ p4))) → p2) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38302616024362468074043426623 : (((((p1 ∨ (True ∧ (False ∧ (p3 ∧ (((p3 ∧ (p1 ∧ p3)) ∧ (p1 ∧ p2)) ∨ p1))))) ∨ p5) → ((p4 ∨ (p1 ∧ p2)) ∧ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147011072314026240815478279940 : ((((p3 ∨ ((((((p1 ∧ p4) → False) ∨ p3) → (p1 ∧ (p4 ∨ p2))) ∧ True) ∧ p1)) ∨ (p4 ∨ p4)) ∧ p4) ∨ ((p3 → (p2 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175790937617938993510154363587 : (((((p2 ∨ ((p3 → p3) ∨ p5)) ∧ (p2 ∧ (p1 ∨ p1))) ∧ p4) ∨ True) ∧ (False → ((p3 ∧ p5) ∧ ((False ∧ (False ∧ p5)) ∨ (False ∨ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137530605340331182686279009995 : ((p5 ∧ (p5 ∧ (((((p3 ∧ (p3 ∨ p1)) → ((((p3 ∧ p4) ∨ p5) ∧ False) ∧ p4)) ∨ (p3 ∧ p2)) → p5) → p4))) ∨ (False → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309780765253895043592251741589 : (p2 ∨ (((p5 ∨ (((p4 ∨ False) ∧ ((p5 ∧ (p1 ∧ ((True ∧ p5) → p3))) ∨ p3)) ∨ (p2 → p2))) ∧ False) ∨ (((True → p4) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113966722451780729341142907177 : (((False ∧ (p2 ∨ ((((p3 ∨ p3) ∨ True) ∨ (((p5 ∨ (True → p2)) → p4) ∧ (p3 → p5))) → p5))) ∧ ((False → True) → p3)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310137660230645477376032627199 : (p2 ∨ ((p1 → ((((True ∧ (p5 ∨ False)) → p2) ∧ ((p3 ∨ p3) → False)) ∨ p4)) ∨ ((p2 → ((((p3 → p4) ∧ False) ∧ p3) ∨ True)) ∨ p3))) := by
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
theorem thm_5_vars_45721365846245776984181447750 : (((True → (((True → p4) → p2) ∧ (((p3 ∧ ((((p4 ∨ True) → (((p3 ∧ True) ∨ True) → p5)) ∨ False) ∧ p2)) → True) ∧ p2))) → p2) ∨ p4) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337869137386894482113331614809 : (p1 → ((True ∧ (((p5 → True) ∧ (p1 ∨ ((True ∨ (p1 ∨ p4)) ∧ p2))) → p5)) ∨ ((p2 → (p4 → p3)) ∨ ((p4 ∨ p5) → (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215188736574952646668042968911 : ((True ∧ (p2 ∧ (p2 ∧ p4))) ∨ (((p2 ∨ p3) → (((p5 ∨ True) ∧ ((p3 ∧ (p3 → p1)) ∧ p1)) ∨ p1)) → ((True → False) → (p4 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702291103043889464525034097959 : (((((p5 ∧ (p3 → (True ∧ (p2 ∨ (p4 → p2))))) ∧ False) ∨ (p3 ∨ (((p2 ∨ (False ∨ p1)) ∧ False) ∨ (((p5 → False) ∧ p3) → True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50284470875637626460968977332 : (((((True ∧ (p5 ∨ (True → ((False ∧ False) ∧ p1)))) → (False ∨ ((p2 → True) ∨ False))) → (p1 → False)) ∨ ((p2 ∧ False) → (p5 → p1))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705289157529091321679564805965 : (((((((p3 ∨ (False ∧ False)) ∧ False) ∧ False) ∨ False) ∧ ((p3 ∧ True) ∨ ((p2 → (True → (p5 ∨ (p2 ∨ p5)))) ∧ ((False → p4) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47318434086466601137331607930 : (((((p5 ∨ p4) ∧ p4) → ((True → (p1 ∧ (p1 ∨ p2))) ∨ (p3 → (((p3 ∨ True) → p2) ∨ (p1 → (p3 ∧ p1)))))) ∨ (p3 ∨ p1)) ∨ False) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355539716432327128572985884444 : (p5 → (((((True → (p2 ∨ p2)) ∨ (p4 → ((p5 ∧ (p1 → (((p4 ∨ (p3 ∧ p2)) ∧ True) ∧ p5))) ∨ p1))) → p2) ∨ True) ∨ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759600205585930514765058947358 : (((p2 ∧ (((p3 ∨ p2) ∨ (((False ∨ (p3 ∨ p4)) ∨ ((p4 → False) ∨ (False ∨ True))) ∨ p4)) → (p4 ∨ (((p4 ∨ p4) ∧ p2) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60467080987524483592986502968 : (((p5 → p3) → ((False ∨ p3) → ((p3 ∧ p2) → (p2 ∧ (((p2 ∧ ((True → p1) ∨ ((True ∧ p3) ∧ p3))) ∨ p1) → (False ∨ p3)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h3.left
      let h23 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h3.left
    let h28 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h29 =>
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111851649385544596458530183785 : ((((((p1 → True) ∨ p3) ∨ ((((p2 ∨ p4) ∧ p5) ∧ (p5 → (p3 → (p2 → False)))) → p3)) → (p5 → (p1 ∨ p1))) ∨ p4) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179588700392762659514798204546 : ((p3 → ((((False ∧ p2) ∧ (p2 → (p4 ∨ True))) ∨ (False ∧ True)) ∨ False)) ∨ (False → ((False ∨ (p3 → p1)) ∨ (p1 → (p5 ∧ (p2 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347999752528963193019551156951 : (p3 → ((True ∧ p1) ∨ (((((p1 ∧ False) ∨ (p3 ∨ p1)) ∨ (p1 ∨ p1)) → (False ∨ (False → (False ∨ (((p5 → False) → p3) ∧ False))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44813695202086322155640361540 : ((((True ∨ (p5 ∧ True)) ∧ (p2 → (((((p1 → True) → p2) ∧ p5) → p3) ∨ (p2 ∧ (p2 → (((False ∧ p5) ∨ False) ∧ p5)))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221411901983783492932736363298 : (((True → p3) ∨ True) ∧ (p1 ∨ (((p4 ∨ ((p2 ∨ p2) ∧ p5)) ∨ (p1 ∨ p2)) ∨ ((True ∨ ((True ∧ (False ∨ True)) → (False ∧ False))) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50137528889096611561998017842 : (((p5 ∨ (p5 → ((p4 → ((p3 ∨ (p2 ∨ ((p4 ∧ True) → False))) ∧ p4)) ∨ (p5 ∧ (False ∨ True))))) ∧ (True ∨ (True → (True ∨ p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65605709847658501245397798755 : ((p4 ∨ (((p5 ∧ (p2 ∨ p1)) ∨ ((p3 → ((p1 ∨ ((p2 ∧ (p4 → (p1 → ((p1 ∨ p1) ∨ p1)))) ∨ p1)) → p1)) ∧ p5)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221423158387570390938574990861 : (((True → p5) ∨ True) ∧ (p2 ∨ ((p5 ∧ (((p1 ∧ (p1 ∧ (p1 ∨ (p3 → p4)))) ∨ p3) ∨ p4)) ∨ ((p4 ∧ ((False ∧ p1) ∧ True)) → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111686513509422258151082254721 : ((((((((p3 ∧ ((((p1 → (p3 → p3)) → (p3 → p1)) ∧ p3) ∨ True)) → True) ∨ p4) → (p4 ∧ True)) ∨ p4) → p3) ∨ p4) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227319938892783530597499506514 : (((p2 → p3) → p4) ∨ (((((p3 ∨ p2) ∨ False) ∧ (True ∧ p3)) → p4) → (((((False → p2) ∧ (p3 ∧ p3)) → p4) ∨ p5) ∨ (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p3 ∨ p2) ∨ False) ∧ (True ∧ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116201113182146973116740813874 : ((((p5 ∨ False) ∧ p5) ∨ ((((False ∨ ((p2 → p2) ∧ p1)) ∨ ((True ∨ (p3 ∧ p5)) ∨ p4)) ∨ ((True → True) → p1)) → p5)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114775965784139648524288334288 : ((((p5 ∨ (p1 → (p1 ∨ ((p2 ∨ (False ∧ p5)) → (p1 ∨ p2))))) ∧ p1) ∧ (((False ∨ (False ∨ p1)) → (False ∧ p1)) ∨ p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705409600370898678290449928528 : (((((p1 ∧ (p5 → ((True ∧ p4) → p1))) ∨ p1) ∧ (((p1 ∨ False) → ((p5 ∨ (p1 ∧ (p5 ∨ False))) ∧ ((p1 → p4) ∧ True))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801926218996913818152344889715 : (((p2 → ((p4 ∧ p2) ∨ (((p2 → p1) ∨ ((True → ((((p4 ∨ p4) ∧ True) ∧ (p2 ∧ p1)) ∧ p4)) ∨ (p4 → p2))) → (p1 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172457295439089166496475518080 : (((p1 ∧ ((False → False) ∨ True)) ∨ (((p1 ∨ (p4 ∨ (p5 ∨ p2))) ∧ p2) → p5)) ∨ ((p4 ∨ ((False ∧ True) ∨ p1)) ∨ ((True ∧ False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_323520433542398050114526647890 : (p5 ∨ ((p5 ∧ (p4 ∧ ((False ∨ True) ∧ ((((p2 → p4) ∧ (((p5 ∨ False) ∧ True) → p3)) → (p5 → p1)) ∨ True)))) ∨ (True ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703296734541328247819868657477 : ((((p4 ∧ ((p4 → p4) ∧ ((False → p2) → (True ∧ True)))) ∨ (((p1 ∨ (False ∧ p3)) ∧ ((True ∨ p4) → False)) ∨ ((False → True) ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160487053204015855517641637795 : ((((p4 ∧ ((p2 → p3) ∨ (((p1 ∧ p4) ∨ p2) ∧ p1))) ∧ p4) ∧ (((p2 ∨ True) ∧ p5) → True)) → ((p4 ∧ p3) → ((p5 ∧ True) → p3))) := by
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
  let h6 := h2.left
  let h7 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60042352288958492873731458495 : (((p1 ∨ p5) → ((p1 ∨ ((True ∨ ((p5 ∨ (p3 → (((False → True) ∧ (False ∨ p2)) → (True → (p1 ∧ False))))) → p1)) → p3)) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148597994174980776451079778579 : (((p3 ∧ (((((p5 ∨ p5) ∨ True) ∧ False) → False) ∨ p2)) ∨ ((((True → p5) ∨ p2) → p2) → (p5 ∧ False))) ∨ (p3 ∨ ((p3 ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_355844406811036039170935224750 : (p5 → (((((p1 ∧ False) → True) ∧ (((p5 ∧ True) ∧ (p3 ∨ ((True ∧ (p4 → (p5 ∧ p1))) ∨ p5))) → p2)) → p2) ∨ ((True → True) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 ∧ True) ∧ (p3 ∨ ((True ∧ (p4 → (p5 ∧ p1))) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



