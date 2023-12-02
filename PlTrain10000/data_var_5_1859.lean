variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244273185357125633826900833530 : ((False ∧ True) ∨ ((((p1 ∧ (p5 ∧ False)) ∧ p5) ∧ ((p1 → False) → p2)) ∨ ((p3 ∨ (p4 ∧ p3)) → (((p5 → p5) → p5) ∨ (True → p3))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147978029386077183765676972164 : (((((p1 → ((True ∨ ((True ∧ ((p2 → p1) ∨ (p1 → p5))) ∧ p1)) ∨ p3)) → p3) ∧ p1) ∨ (p5 ∨ p5)) ∨ ((True ∧ (p1 ∧ False)) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216511103359740530782808604993 : ((p5 → (p2 ∧ (False ∧ False))) ∨ (((p4 ∨ p2) → p5) → ((p1 → (((False ∧ False) → True) → ((p5 ∨ p1) ∧ False))) ∨ (False → (False ∨ True))))) := by
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
theorem thm_5_vars_48969971732029467639600297545 : (((((((p2 ∨ ((False → True) ∨ False)) ∨ False) → ((p4 → ((p3 ∧ p1) ∧ (p2 → p4))) ∧ p3)) → p1) ∨ True) ∨ ((False ∧ p1) → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258758291340885085660661682427 : ((True → False) → (((p2 ∧ (((False ∨ (p4 ∧ (True → p4))) ∧ p3) ∧ (((False ∧ p1) ∨ True) ∧ (False ∧ (p3 ∨ True))))) ∧ (p3 → p2)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341012273134632124609041850304 : (p2 → ((p1 ∧ (p3 → (p4 ∨ (p2 → ((((True ∨ (False ∧ p5)) → ((p3 ∧ (False → False)) ∨ (p5 ∧ p4))) → False) ∨ (p2 ∧ p3)))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156875032958178609783124716096 : ((((p3 ∨ ((p3 ∧ False) ∧ ((p2 → p4) ∨ ((p4 ∨ p3) → (False ∨ (p1 ∨ False)))))) ∧ p5) ∨ True) ∨ ((p4 ∨ (p1 ∨ False)) ∧ (True → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341697066912429797329819486714 : (p2 → ((((((p1 → p2) ∧ (False → (p5 → False))) ∨ ((p5 ∧ ((False ∧ True) ∧ True)) → p2)) ∧ (p5 ∧ p3)) → (p4 ∨ p1)) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740384690712329851824757008370 : ((((p1 ∨ p2) ∨ (True → ((p1 → (((True ∧ p4) → ((p4 ∧ p5) → p2)) → (p2 → ((p3 → False) → (p3 ∧ (True → p1)))))) ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_200352185502495856636441870583 : (((True → False) ∧ (((p3 → p3) ∨ p2) ∨ p2)) → ((p1 ∨ (p1 ∧ False)) ∨ ((((p1 ∧ p4) ∨ (p1 → p1)) ∧ True) → (p2 ∧ (p2 → p4))))) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206963425375073853931966020862 : ((((p4 ∧ (p1 ∨ p3)) → p2) ∧ p3) → ((p2 ∨ p3) ∧ (((p2 ∧ p2) → (p5 ∧ ((p5 ∧ p1) → False))) ∨ (p3 → ((p3 ∨ p1) ∨ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248586415306026670319046485333 : ((p3 ∨ False) ∨ (((p1 ∨ p2) → (((True ∨ True) ∨ False) ∧ p3)) ∨ ((p5 ∨ (True → (((p4 ∨ p5) → p2) ∨ (True ∧ (p3 ∨ p1))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45228824472260676701164637276 : (((p1 ∧ ((p2 → (p2 ∧ (p1 ∨ (True ∨ ((True → ((True ∨ (True → True)) ∨ ((p4 ∨ False) ∧ p4))) ∨ (p2 → p2)))))) ∧ p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208045024967584448684000038918 : (((p5 ∧ (False ∧ p2)) ∨ (p3 → p4)) → ((False ∨ (((p3 → p5) ∨ (p5 ∨ False)) → (((p5 ∨ ((False → p5) ∧ p2)) ∨ p4) ∨ p3))) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355584263985869981789415769885 : (p5 → ((((p2 → False) → (p5 → (p2 ∧ (False → (p3 ∨ p5))))) ∧ ((((p3 ∨ p3) ∨ (True → (p2 ∧ p3))) → False) ∧ p1)) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325177148555369137949730205778 : (p5 ∨ (True ∧ (p2 → (False ∨ ((((p3 ∧ p1) → ((((True ∧ (p1 ∨ p5)) ∨ False) ∨ (True ∧ p5)) → (p5 ∧ p5))) ∨ (p1 ∧ p1)) ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308380118613070591055759825888 : (p2 ∨ (((((((True → ((False ∧ False) ∧ p2)) ∧ (False ∧ p4)) ∨ (p5 → p5)) ∨ ((True ∧ (p1 ∧ p5)) → p5)) → (False ∨ False)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43037512411864662940815224686 : ((((((((False ∧ p2) ∧ p5) → p3) ∧ ((p1 → (p3 ∧ p4)) ∧ (p2 ∨ (p4 → ((p3 ∧ (p3 → False)) → p5))))) ∨ True) ∧ p3) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149140498638794739985174349099 : (((p5 ∧ p3) ∧ (((p1 ∧ ((p5 → ((p1 → (p1 ∧ True)) ∨ (True ∧ p3))) ∧ p3)) → (p1 ∨ False)) → p1)) ∨ (p1 → (p1 → (p1 ∧ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729845360243535201668156577885 : (((((False ∧ p3) → True) → (((p1 → p3) → ((p3 ∨ p1) → p3)) → ((((p4 ∨ (p2 ∧ p3)) → (True ∧ p4)) ∨ p4) → (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206964027720121955043469541546 : ((((p5 ∧ (True ∧ p4)) → p4) ∧ p3) → (((((True → p3) ∨ False) → False) ∨ True) → (((p1 ∨ p4) → ((p3 ∧ p1) → p5)) ∨ (p3 ∧ True)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62863798512466328032609113181 : ((p4 ∧ (((p3 → p3) → p5) ∧ (((p5 ∧ ((p5 → (p4 ∨ (p1 ∧ p5))) → (((False → (p5 ∨ p2)) ∨ False) → p3))) → p3) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67742442753667591892272737168 : ((p2 → ((p5 ∨ (p3 ∨ (((p1 → p1) ∨ (p2 ∨ p5)) → ((((((p4 → p4) ∨ p5) ∨ (True ∧ p2)) → True) → p3) ∨ p2)))) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676525859649042312751437722588 : ((((False ∧ (((((False ∨ True) → p2) ∧ (p5 ∧ (p4 → False))) ∧ (p4 ∧ (False ∨ (p4 ∧ True)))) ∨ p5)) ∧ (((p4 → p2) ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151702367960305230221372341703 : (((((p2 ∨ True) → ((p1 ∧ (p1 ∨ p5)) ∧ (p2 ∧ (p2 → (True ∨ p4))))) → p2) ∨ ((p1 ∨ False) ∨ p3)) → (p5 ∨ (p4 → (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137731257633335531209492646733 : ((p1 ∨ (False ∨ (p2 ∧ ((((((False ∨ (False ∧ p5)) → p2) ∨ p4) ∧ p3) ∨ p1) → (True ∧ (p1 ∨ (p2 → p1))))))) ∨ (True ∨ (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192294732764864649077952020738 : ((((p2 ∨ True) → (p2 → (p3 ∧ (p3 → p5)))) ∧ p3) → ((p3 → ((p3 ∨ ((p1 ∧ (True ∨ p1)) → (p2 → p2))) → (p2 ∧ False))) ∨ True)) := by
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
theorem thm_5_vars_134344545980127321173786438661 : (((p5 ∧ (((p4 ∨ p1) ∧ ((p2 ∨ (p4 ∧ p3)) ∧ (p2 ∧ ((p3 ∨ p3) ∧ (p4 ∧ True))))) → (False ∨ False))) ∨ p3) ∨ ((p4 → p4) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46840997331519096199013930354 : (((((False ∨ ((p1 ∧ (p3 ∨ p4)) → True)) ∧ ((p2 → (p2 ∧ False)) ∧ (((p2 → p5) → True) ∧ (p3 ∨ p2)))) ∧ p4) ∨ (p5 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127056492295334597559865931577 : ((False ∨ ((((True ∨ False) → p3) → (((p2 ∧ p1) ∨ (((p4 ∨ p3) → p5) ∨ (p4 ∨ True))) ∧ (p3 ∨ p1))) → (p3 ∧ p1))) → (p3 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((True ∨ False) → p3) → (((p2 ∧ p1) ∨ (((p4 ∨ p3) → p5) ∨ (p4 ∨ True))) ∧ (p3 ∨ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h5
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h4
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139917595104673476507285181335 : (((((((p3 → (p5 ∧ (False → p5))) ∨ True) ∨ p2) ∧ p2) ∧ (((True ∨ p1) ∨ (p2 ∧ p4)) → True)) ∧ (True → p3)) → ((p3 ∨ p1) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h17 := h3 h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65243400998194515473516081418 : ((p3 ∨ (((((True → (((p2 → (p2 ∨ (((p1 ∨ False) ∨ False) ∨ p2))) ∨ (p4 ∧ False)) → p4)) ∨ p5) ∨ (True ∧ p2)) → p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860330394034449324857096262400 : (((((p4 → (((((p1 ∨ p5) → False) ∧ p2) → False) ∨ (((False ∧ (p1 ∧ (False ∨ p3))) ∧ p1) ∨ (p2 ∨ True)))) ∨ (p1 ∧ p5)) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (((((p1 ∨ p5) → False) ∧ p2) → False) ∨ (((False ∧ (p1 ∧ (False ∨ p3))) ∧ p1) ∨ (p2 ∨ True)))) ∨ (p1 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728219326947773778148123969548 : ((((True → (p1 ∨ p2)) ∨ (((((((p2 → p1) → p1) ∧ ((p2 ∧ True) → p5)) ∨ ((p3 ∧ False) ∨ True)) ∧ p5) ∧ False) ∨ (True ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165002843825169666277412541278 : (((((p1 ∨ True) → ((p2 ∨ p1) ∧ (p3 ∧ p5))) → ((p5 ∧ (p1 ∨ p5)) → p5)) → p1) ∨ ((p5 ∧ (False → p5)) ∨ (p1 ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_207011490514286936435153415107 : ((((p1 ∨ p4) ∨ (p4 ∧ p5)) ∧ True) → ((((False → False) ∧ ((p4 → p2) → (((True ∨ p3) ∧ True) ∨ True))) ∧ p3) ∨ (p2 → (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135824548047567727315078829857 : ((((False ∧ ((p1 ∧ ((p1 → p4) ∧ p5)) → p3)) ∧ (p4 → True)) ∧ (((p2 ∨ p5) → ((True → p4) ∨ p1)) ∨ False)) ∨ (True ∨ (p2 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65967294742391906414140317042 : ((p4 ∨ (True → (((p5 ∨ ((True ∨ ((p3 ∧ p1) → True)) ∨ p3)) ∧ (p1 → (((((p5 → p4) ∨ p5) ∧ p2) ∧ p3) ∧ p5))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806543422915632150292206593133 : (((p4 → (((p5 ∧ (True ∨ ((p3 ∨ ((False → p4) ∨ (p3 → p4))) ∧ p4))) ∧ (((False → p4) → (True ∧ (p1 ∧ p3))) → p3)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184066002067701279802765356336 : ((((p5 ∨ (((True → True) ∧ p4) ∨ p3)) → (p5 ∨ p5)) ∨ False) ∨ (((((p4 → p3) ∧ False) ∨ (p3 ∧ (p5 ∨ p3))) ∧ (False ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178816764918419387721495131860 : (((False ∨ (p5 ∧ True)) ∨ (((False ∧ p4) → p5) → ((False → p5) ∧ p2))) ∨ (((p2 ∧ p4) ∨ (p5 → ((p1 → p2) ∨ p4))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326292611815220727112405052504 : (p5 ∨ (p4 → ((p1 ∨ (p5 ∧ (p5 ∧ ((p4 ∧ (((((p4 ∧ p1) → p3) ∨ p5) ∨ (p4 ∨ (False ∨ p3))) ∧ p3)) ∨ p1)))) ∨ (p4 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187064524549250298657777229451 : (((p1 ∨ p5) ∧ (p3 ∧ ((((True → p1) ∨ p4) ∨ p1) → False))) → ((p1 ∧ p2) ∨ (p3 ∧ ((p1 ∧ False) ∨ ((p2 ∨ False) → (p3 ∨ p4)))))) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (((True → p1) ∨ p4) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111987793926217079237279858524 : ((((((p2 ∧ p1) ∧ p4) ∧ p2) ∧ (((False ∧ p4) ∧ p5) ∨ (((p2 ∧ ((p3 ∨ p3) ∨ True)) → p3) ∧ (p2 ∨ p2)))) ∨ True) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786815435274521586234183320452 : (((p4 ∨ ((True → ((False ∨ p4) → True)) → ((p5 ∧ (p1 → (((False ∨ p4) → (p2 ∨ (p2 → (True ∨ p3)))) ∧ (p5 ∨ False)))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183991388719987606950375714099 : (((((p1 ∨ p4) ∨ (p5 → (True ∧ (p4 → p3)))) ∧ p4) ∨ p5) ∨ (((p3 ∧ p5) → p5) → ((True ∧ p2) ∨ (p1 → ((p3 → p2) ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148484706429910876527589421236 : (((((((False → True) ∧ (True ∨ p5)) ∧ (p5 → p2)) ∨ p3) → p1) ∨ ((((p1 ∧ p3) → True) → p3) ∨ True)) ∨ ((False → p1) → (p3 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261160618074929582113298501033 : ((p4 → p4) → (((p2 ∨ p4) → (p2 ∧ False)) ∨ ((((((p4 → False) ∧ p3) → (p5 ∧ False)) ∨ p3) ∨ p4) ∨ (((False → p5) → False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217127209566333437801539532094 : ((((p5 ∨ True) ∨ True) ∨ p4) → (((p1 ∧ ((p3 ∧ p5) ∧ (((p3 ∨ p1) ∧ (True ∧ ((p3 ∨ p5) ∨ (p2 → p4)))) ∧ p5))) ∨ p3) ∨ True)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
theorem thm_5_vars_709481605975762228852014407244 : ((((p4 ∧ ((((p2 ∧ False) ∧ False) → p5) ∨ p5)) → (((((False ∨ True) ∨ False) ∨ p1) ∧ ((p5 ∧ (p3 ∨ p3)) ∧ p2)) ∨ (p4 → p4))) ∨ p4) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781377573139635434157907362917 : (((p2 ∨ (p2 ∧ (False ∧ (p4 → (p3 ∧ ((p4 → p4) ∧ (False ∨ (p1 → ((p5 → False) → (p2 → (((p2 → p1) → p2) ∧ p5))))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24780337434220152099178039624 : ((((p3 → p1) ∧ False) ∨ ((p3 ∧ (False ∨ ((p3 → True) → (p5 ∧ ((((p3 ∨ ((p3 → p3) ∨ False)) ∨ False) → p1) ∧ False))))) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166491269568043593688445878345 : ((p3 ∨ ((p3 ∨ p1) ∧ (p2 → (((p5 → False) ∨ (p3 ∧ ((True → p1) ∨ p5))) ∨ p2)))) ∨ (p1 → (False ∨ ((p1 → p4) → (False → p5))))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341752791501010649822244145501 : (p2 → ((p5 ∧ (p1 → ((p4 → p5) ∧ ((((p4 ∨ p2) ∨ p5) → (((p5 ∧ False) → ((False ∨ True) ∨ p5)) ∧ p4)) ∧ p4)))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200534752515720238673465385194 : (((p5 ∨ False) → ((p1 → (True ∨ p2)) → p3)) → (p5 ∨ ((p5 ∨ p3) → (((((p4 ∨ p2) ∧ p3) ∨ (p3 ∨ (p5 → p5))) ∧ p4) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234309157842996687411460103360 : ((p1 → (False ∧ p4)) → (((((True ∨ p4) ∧ (p1 ∧ p4)) ∧ ((False → p1) ∧ ((p4 → True) ∧ True))) → (((p3 ∨ True) ∧ True) ∧ False)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
    let h10 := h4.left
    let h11 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h6.left
    let h16 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h21 := h2.left
  let h22 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h22.left
    let h29 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h32 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h33 := h1 h32
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h24.left
    let h37 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h22.left
    let h39 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h42 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h36
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h43 := h1 h42
    -- We need to get the left conjuct of h43 based on <expert-advice>.
    let h44 := h43.left
    -- False on the left can always be used.
    apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117063921815202471934013915240 : (((p5 ∨ p4) → ((p3 ∧ ((p4 → True) → p3)) ∨ (((True ∨ (p5 ∨ p2)) → (p5 ∨ (p4 ∨ p3))) → (p1 ∨ (False ∨ True))))) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67898906004671665850468632806 : ((p2 → ((((((p2 → (p5 ∨ p3)) ∧ p1) ∨ p1) ∨ p2) → (p2 ∧ (p4 ∧ (p3 ∧ p3)))) → (True ∧ ((p4 → p3) ∨ (True ∨ p4))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192782849288497379680690957264 : (((False ∨ (((p3 ∧ p2) ∧ (False ∨ p3)) ∧ p3)) → p5) → ((True → False) → (((p5 ∨ p1) ∨ (((p3 → p2) → p4) ∨ (False → False))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199145479016232051053513445835 : ((((p3 ∧ p1) ∨ ((p5 ∨ False) ∧ p3)) ∧ p4) → (False ∨ (((((p2 → p2) → ((p2 ∨ p2) → p2)) ∨ p2) → p2) ∨ (p2 → (True ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142247054173204402280977580745 : ((p2 ∧ (((((True ∨ True) → (p3 → (((((p1 ∨ p2) → True) ∨ p5) ∧ p2) ∨ p5))) ∨ False) ∨ (True → p3)) ∨ True)) → (p1 ∨ (False ∨ p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163062120398331286265529906433 : ((((((p3 ∧ (p4 ∧ (False ∧ p1))) → True) → p3) ∨ (True ∧ p3)) → (True ∧ (p1 ∨ p3))) ∧ ((False ∧ (p5 ∧ (p2 ∧ (p5 → p3)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p3 ∧ (p4 ∧ (False ∧ p1))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159902270975937082726012048933 : (((((p2 → (p1 → False)) ∨ (((((p1 ∨ p2) → p4) ∨ True) → (p2 → False)) ∧ p1)) ∨ p4) → False) → (True → ((p4 → p2) ∨ (True → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 → (p1 → False)) ∨ (((((p1 ∨ p2) → p4) ∨ True) → (p2 → False)) ∧ p1)) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53879427569395894480028477746 : ((((p5 → p3) ∨ ((True → False) ∧ ((p4 ∨ p3) ∨ p5))) ∨ ((p4 ∧ ((p3 → (p1 ∨ (False ∨ p2))) → ((p3 → True) → p5))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327089232414346116069370352841 : (True → ((((True ∧ p3) → True) → (True → (p2 ∨ (p3 ∨ (p5 ∧ (p4 ∨ ((((p1 ∨ p5) ∨ (p2 ∧ True)) → (p5 → False)) ∨ p4))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165368555464725602070231089164 : ((((((p5 ∧ p3) ∧ ((p2 ∧ p3) → p1)) → (p4 → False)) ∨ p5) ∨ ((p4 ∨ True) ∧ True)) ∨ ((False ∧ p4) ∧ ((p2 ∨ p2) ∧ (p4 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_655035405400904775409221114342 : (((((True ∧ (True ∨ ((p5 ∧ ((p1 ∨ p3) ∧ (((True ∧ (True ∧ p5)) ∧ p3) → p4))) ∨ ((p1 ∨ p3) ∨ p3)))) → p5) ∨ (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148154497606062676244706792546 : (((True → (False → ((p4 → p5) → (p4 → (((p4 ∧ p4) ∧ p5) ∨ ((True ∨ False) ∨ p3)))))) → (p1 → p4)) ∨ (p1 ∨ ((p1 ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310673259721865684113560674373 : (p2 ∨ (((p5 ∧ p3) ∨ (p2 → p4)) → ((False ∧ p3) ∨ (p1 → ((p1 ∧ (p3 ∨ (True ∨ (True ∧ p1)))) ∨ (((p3 → p2) → p1) ∧ p5)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382394818521777285823167343005 : ((((((((p5 ∨ (p1 ∧ ((True → False) ∧ p5))) → ((True ∧ p2) ∧ p4)) ∨ p4) → (p1 ∨ (p5 ∨ (True ∧ (True → p3))))) ∨ p1) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_60458484854755683838010465457 : (((p5 → p2) → ((p4 ∨ ((((p3 ∨ (((p1 ∧ ((p2 → True) ∨ False)) ∧ p1) ∧ p3)) → True) ∧ (p1 → False)) → (p5 ∨ p1))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147030995753141446094742178452 : ((((False ∨ ((True → ((True ∧ p5) ∧ (((False ∧ p3) → p3) ∧ p1))) → p3)) ∨ (p3 ∨ (True → False))) ∧ p3) ∨ (((False ∧ p5) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299365392845404523702637088747 : (False ∨ (((p4 → p3) ∧ ((False ∨ True) ∧ (p5 ∧ ((p2 → ((p1 ∨ False) ∨ (((p3 ∨ (p5 → (p4 → p1))) ∧ p5) → True))) → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255616443458958592168907707138 : ((p5 ∧ p4) → (((((False → p1) ∨ p4) ∨ p2) → (((False → p5) → (p2 ∨ p3)) ∨ ((((p2 → p3) ∧ p1) ∨ p5) ∨ p2))) ∧ (p5 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78411396228941137006365488604 : ((((p5 → (False ∧ (p2 → (False ∨ (((True ∨ p5) ∨ ((p1 ∧ ((False ∨ True) → (p5 ∨ False))) ∧ p1)) ∨ p3))))) ∧ p5) ∧ (p4 → p2)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322582935794260283670483173454 : (p5 ∨ ((True → (((p2 ∧ (False → True)) ∧ ((p2 ∧ True) → ((False ∨ p1) ∧ ((p1 ∧ False) ∨ ((p5 ∧ (p1 ∧ True)) → False))))) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_251607912891152329674528214520 : ((p3 → p1) ∨ (((((((p4 ∨ (p2 → (p5 ∧ p5))) → p1) ∧ p5) ∧ (False → (p3 ∨ p5))) ∧ (p5 ∨ p1)) → (p1 ∨ p2)) ∧ (p5 ∨ True))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (p4 ∨ (p2 → (p5 ∧ p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806295046325462144535136682777 : (((p4 → ((((p5 ∧ p4) → (p1 ∧ p2)) ∧ ((((p1 ∧ False) → p5) ∨ (p2 ∧ ((p2 ∧ (p1 ∧ p1)) → (p4 → p2)))) → p5)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_234667662435467563592214280835 : ((p4 → (p1 ∧ p2)) → (((p2 → p3) ∨ (((True → ((p4 ∧ p2) → ((p1 ∧ p1) ∧ p1))) ∨ False) ∨ False)) ∨ ((False → p5) → (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257673634776701138133638560106 : ((p3 ∨ p3) → ((p5 ∧ ((((p1 ∨ False) ∨ p2) → p2) → ((True ∨ (True ∨ False)) ∧ (((p4 ∧ (p1 ∧ False)) ∧ p2) ∧ (False → p5))))) ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119400918003422757023142760222 : ((p4 → (((p1 ∨ (p2 ∨ (p3 ∧ (((p5 → (False ∧ p5)) ∨ (p2 ∨ p3)) ∨ (p4 ∧ (False ∧ (p3 ∧ p2))))))) → p5) ∨ True)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199271594466914485336622629418 : ((((((p3 → p4) → True) → p5) ∧ p1) ∨ False) → ((p2 ∧ (((p1 → True) ∧ ((p1 ∨ p5) → p2)) ∨ (False ∧ p2))) ∨ ((False → False) ∨ p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153747776025707322605896031842 : ((p3 → (p1 → ((p3 ∧ (((p2 → (p5 ∧ (p4 → p1))) ∧ (p1 → (p1 ∧ (False → p4)))) → p4)) ∨ p2))) → ((True → (p2 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609191896877289028158595071591 : ((((((p3 → (p2 ∨ (p1 ∨ False))) → (p2 ∧ (((p5 ∧ ((False ∧ (False → True)) ∨ (p1 → True))) ∨ (p5 → p3)) ∨ p2))) ∨ p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696735707489397641334517704337 : ((((((p1 ∧ ((p1 ∧ True) → ((True ∨ p2) ∨ p5))) → p1) → True) ∧ (p3 → (((p5 → p2) ∨ p5) ∨ (p4 ∨ ((p1 ∧ p2) ∨ p3))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_964154661313902668422966572377 : ((((p5 → p2) ∧ (p5 ∧ ((((p3 ∧ p3) ∧ p4) → (p1 → False)) ∧ ((p3 ∨ (((p2 → p2) ∧ (p5 ∧ p4)) ∧ (p1 ∨ p4))) ∧ p1)))) → p2) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h24
      -- One of the premise coincides with the conclusion.
      exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741586016256661008732832543780 : ((((p5 ∨ p5) ∨ (((True ∨ ((p3 → ((((False ∧ p4) ∧ p1) → p3) → p3)) → (p5 ∨ p2))) → False) → (p1 ∨ ((p4 → p3) ∧ p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p3 → ((((False ∧ p4) ∧ p1) → p3) → p3)) → (p5 ∨ p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177921591247123159536922032768 : ((((((False ∨ True) ∨ (p1 → True)) ∧ p4) → (True ∧ (p3 ∧ p5))) ∨ False) ∨ ((((p2 ∧ (False → (True ∨ True))) ∧ False) → (p1 → True)) ∨ p3)) := by
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
theorem thm_5_vars_218343656361192832412120887457 : (((p1 → p3) ∨ (p5 → p2)) → (((((p4 → (p5 → (p1 ∧ (p1 → (True ∧ (p3 ∨ p4)))))) ∧ (False ∧ p3)) ∨ p1) ∨ (p5 ∨ p2)) ∨ True)) := by
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
theorem thm_5_vars_262912007278308323351576778082 : (True ∧ ((True → (p3 ∧ (True → (((p5 ∨ False) → (p5 ∧ p4)) ∧ (p3 ∧ (p2 ∧ (((p4 ∧ (True → (False → p2))) → p2) ∨ p2))))))) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260045289093897571009840770789 : ((p2 → False) → (((((p4 ∨ ((((p4 ∨ p5) ∨ True) ∧ (p4 ∨ p2)) ∧ p2)) ∧ ((True ∧ True) → False)) ∨ False) ∨ (False ∨ (p3 ∧ p2))) → False)) := by
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
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h8 : (True ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h9 := h6 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h17 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h18 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h12
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h19 := h1 h18
              -- False on the left can always be used.
              apply False.elim h19
            case inr h20 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h21 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h12
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h22 := h1 h21
              -- False on the left can always be used.
              apply False.elim h22
          case inr h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h24 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h25 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h12
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h26 := h1 h25
              -- False on the left can always be used.
              apply False.elim h26
            case inr h27 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h28 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h12
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h29 := h1 h28
              -- False on the left can always be used.
              apply False.elim h29
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h31 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h32 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h12
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h33 := h1 h32
            -- False on the left can always be used.
            apply False.elim h33
          case inr h34 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h35 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h12
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h36 := h1 h35
            -- False on the left can always be used.
            apply False.elim h36
    case inr h37 =>
      -- False on the left can always be used.
      apply False.elim h37
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h43 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h42
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h44 := h1 h43
      -- False on the left can always be used.
      apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147279344014115791721226951814 : (((((p4 → p1) ∧ (((p5 ∧ ((p4 ∧ ((p1 ∨ True) ∨ (False ∨ p5))) → True)) → False) ∧ p2)) ∨ True) ∨ p4) ∨ ((p2 → (p3 → p2)) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192103084658332220401990974014 : ((p4 → ((p1 → p2) ∨ (p1 ∨ ((True ∧ False) ∨ p5)))) ∨ (p2 ∨ ((False → True) ∧ (((False ∧ (p2 ∧ (p2 → (p5 ∨ False)))) ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_95604762756166138142074834498 : ((p5 ∧ (((p5 ∧ (((p2 ∧ (True ∨ p5)) → False) ∧ p3)) ∧ p2) ∧ (((False ∨ (p5 ∧ p2)) ∧ p1) ∨ ((True → p2) ∧ (p1 → p3))))) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h19 : (p2 ∧ (True ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h20 := h10 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h24 : (p2 ∧ (True ∨ p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h25 := h10 h24
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357364719624217760995019159242 : (p5 → ((True ∧ p2) → (((p1 ∨ (p3 → ((((p3 ∧ p5) → True) ∨ (False ∧ p2)) ∧ ((p4 ∧ (True ∧ False)) ∨ p4)))) ∧ (False ∨ p3)) ∨ p2))) := by
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
theorem thm_5_vars_252310115930174942756023469051 : ((p4 → p5) ∨ (p1 ∨ ((p4 ∧ (p4 ∨ p4)) ∨ ((((p2 ∧ (p2 → p2)) ∨ (p1 ∨ ((True ∨ p2) ∨ p5))) ∨ p4) ∨ (p3 ∨ (p5 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_714548102354533378906558569482 : (((((True ∧ True) ∨ (p1 → (p2 → p3))) → (p4 → ((((True ∧ p5) → (((p1 → p4) → (True ∧ False)) ∨ p1)) ∨ (False ∨ p2)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708018298126334500051168967342 : ((((p2 ∨ (((False → p1) → (p3 ∨ p2)) ∨ p2)) ∨ ((((p1 → (p3 ∨ p1)) ∨ (((True ∨ p2) ∧ p5) → (False ∨ p4))) ∧ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166484987544586435597837374179 : ((p3 ∨ ((((((p3 ∨ p1) → False) → p2) ∨ True) → p5) ∧ (((p3 ∨ p1) ∨ p3) ∧ p3))) ∨ (p2 ∨ (p4 ∨ (p4 → ((True ∧ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305470974412858235098809071299 : (p1 ∨ ((((p4 → False) ∧ ((p2 → False) → p2)) ∨ (True → ((p2 ∧ p2) ∨ True))) ∧ ((True → (False ∧ (p4 → (p3 ∨ (p1 ∨ p2))))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



