variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636223562573325093491626553723 : (((((True ∧ ((p3 ∨ ((p2 → ((p2 → True) ∨ p5)) ∨ (p3 ∧ (False ∨ True)))) ∨ p2)) ∨ (((False → (p4 → False)) ∧ p2) → p1)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201321065326723523973061837187 : ((p5 → ((p1 → ((True → p4) → p3)) ∧ False)) → ((p1 ∧ ((True ∨ False) ∨ p5)) ∨ (p5 → (((p4 ∨ (p1 ∨ p5)) → p1) ∧ (False ∨ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610258329606423078014831341854 : (((((((p5 ∧ (p3 → (False ∨ p4))) → ((p2 → (False ∨ True)) → (True ∧ ((False ∧ (True → (True ∧ p3))) ∧ False)))) ∨ p4) → False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185586698908109363318121418509 : ((p5 ∨ ((((p2 ∧ p2) → False) → (False ∧ False)) ∨ (p1 ∨ True))) ∨ ((p4 ∧ (p3 ∨ p5)) ∨ ((((p2 ∧ False) ∨ p3) ∧ p2) → (p2 → p2)))) := by
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
theorem thm_5_vars_125509750730466272393369859073 : (((p4 ∨ True) ∧ (p5 ∧ ((((p3 ∧ False) ∨ (True ∨ (((False ∧ p5) ∨ True) → ((p3 ∨ (p5 ∨ p3)) ∨ p3)))) → p3) ∨ p3))) → (True → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((p3 ∧ False) ∨ (True ∨ (((False ∧ p5) ∨ True) → ((p3 ∨ (p5 ∨ p3)) ∨ p3)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : ((p3 ∧ False) ∨ (True ∨ (((False ∧ p5) ∨ True) → ((p3 ∨ (p5 ∨ p3)) ∨ p3)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192279896833142354040781402299 : ((((p2 → p3) ∧ (((False ∨ False) → p4) ∧ p5)) ∧ p2) → ((p2 ∨ (p2 ∨ (p3 → (p5 ∧ (p2 → True))))) → ((True → p1) → (p1 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h22 := h3 h21
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h30 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h31 := h3 h30
      -- One of the premise coincides with the conclusion.
      exact h31
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h1.left
    let h34 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h33.left
    let h36 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- One of the premise coincides with the conclusion.
    exact h38
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h1.left
      let h42 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h41.left
      let h44 := h41.right
      -- Conjunctions on the left can always be decomposed.
      let h45 := h44.left
      let h46 := h44.right
      -- One of the premise coincides with the conclusion.
      exact h46
    case inr h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h1.left
      let h49 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h50 := h48.left
      let h51 := h48.right
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- One of the premise coincides with the conclusion.
      exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709301095658564606100910548241 : (((((p3 ∧ False) → ((p4 → True) ∧ (p3 ∨ False))) → (p5 → (((p3 ∧ ((False ∧ p1) ∨ (p4 ∧ ((p2 → True) → p1)))) → p1) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665886675043210529605799587422 : ((((((((p2 → True) ∧ (p1 ∨ (p4 ∨ (p3 ∨ False)))) ∧ p1) ∨ (p3 → (p1 ∨ ((p5 ∧ True) ∨ p4)))) → p1) ∧ (True → (p4 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689555009359929269018001623153 : ((((((False ∧ ((True ∨ p5) ∨ (p2 ∨ False))) → p5) → ((False ∧ p5) ∨ (p1 ∨ p3))) ∨ ((p4 ∧ ((p2 → p5) → (False ∧ p1))) → p4)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_645463968027622205590102168019 : ((((p4 ∨ ((p3 → (True ∧ p5)) ∧ (p5 ∨ (((((p4 → True) ∧ p2) → p2) → (True → (p1 ∨ p5))) ∧ (p3 ∧ (p5 ∨ p2)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175437520200211483927857033372 : ((p1 → ((p3 ∨ (((p3 ∨ False) ∨ ((p1 ∨ p5) ∧ p5)) ∨ p1)) ∨ (True ∧ p4))) → ((((p5 → (p4 → False)) ∧ p5) ∧ (p5 ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676890259209507518564636004807 : ((((p4 ∨ (p1 ∨ ((p1 → ((p5 → ((((p5 ∨ p5) ∧ True) ∧ False) ∧ (p2 ∨ p1))) ∧ p5)) → p2))) ∧ ((p5 → (p3 ∨ p5)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199493737763026718150694059757 : (((True → ((p4 ∨ p5) ∧ (p2 ∧ False))) ∨ p1) → ((((((p4 ∨ (((p1 ∨ p5) ∨ p2) → False)) ∨ (p5 ∧ p5)) ∨ True) ∨ p2) ∨ p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137138686293142545914446994684 : ((True ∧ (p3 ∨ ((True ∧ p3) ∨ (((((p1 → (p5 ∨ p5)) → (p2 → p3)) ∨ (p4 ∨ p5)) ∨ (p4 → p3)) ∨ p2)))) ∨ ((False ∧ p5) → p2)) := by
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
theorem thm_5_vars_184878850771621736712246523025 : (((p3 ∧ (p3 → False)) ∧ (p1 ∧ ((p4 → (p1 → True)) ∧ p3))) ∨ ((((p4 → (p5 ∨ (True ∧ False))) → p1) ∧ p2) ∨ (p3 ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265866130350476003043304872025 : (True ∧ (p5 ∨ (p1 → (True ∧ ((((p5 ∧ (p1 ∧ (p1 → (False ∧ ((p5 → p1) → ((p1 ∧ p5) → True)))))) ∨ p3) ∨ (p5 ∨ p1)) ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62883096024560297139869459447 : ((p4 ∧ ((p5 ∧ p5) ∧ ((((False → p1) ∧ (p2 ∧ p1)) → (((p2 ∨ p3) → ((p1 ∨ True) ∧ p1)) ∧ ((p1 ∧ False) ∨ False))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309375961467095289541365673827 : (p2 ∨ (((p3 ∨ False) ∨ ((((p2 ∨ (p1 ∨ (p4 → (p3 ∨ p3)))) → (False ∨ ((p5 ∨ p5) ∧ False))) ∧ True) ∨ (False → p5))) ∨ (False ∨ p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103378758468638391926441923423 : (((p2 → (((((p5 ∨ p1) ∨ ((p4 ∧ (p4 ∨ False)) → (((p4 → (p5 → p3)) → p5) ∧ p1))) → False) ∧ p1) ∨ False)) ∨ True) ∧ (False → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68844160722928772949516165018 : ((p4 → ((p3 ∧ True) ∨ ((p3 ∧ (p3 ∧ True)) ∧ ((((False ∨ ((p4 ∨ ((p3 → False) ∧ False)) → p5)) ∧ p3) ∧ (p2 ∨ False)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645128275086356548108928073705 : ((((p3 ∨ (((((p5 ∨ (p5 ∨ (p1 ∨ p1))) ∧ ((p5 → p5) ∨ False)) ∨ (p4 ∧ (False ∨ p5))) ∨ p1) → ((p3 ∨ False) ∨ p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193783307134279325725061625035 : ((p4 ∧ (((p5 → (p1 → False)) ∨ p2) ∨ (False → p5))) → (True ∧ ((p1 → ((p1 ∧ (p3 ∧ (p1 → (True ∨ (p3 ∨ p4))))) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_135928972105415672274824271007 : (((p1 → (((False → p2) ∧ p3) ∨ (p3 ∧ ((p2 ∨ True) → p5)))) → ((p5 ∧ ((p4 → (p3 → p1)) ∨ p1)) → p4)) ∨ ((p1 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44593957188945399445477491294 : ((((((p2 ∨ (p1 ∨ False)) ∨ (p1 ∧ p3)) ∧ True) → ((p3 → (False → False)) ∨ (p2 ∨ ((p2 ∧ (p1 → p2)) → (p1 → p1))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136596926215763022137494924892 : (((p3 ∨ (p4 ∨ p2)) ∨ (True ∧ (False ∨ (p5 ∧ ((p4 → (((p4 → p5) ∨ ((p5 → p3) → p5)) → p4)) ∨ True))))) ∨ (p4 → (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207984683923345284204768026823 : ((((p1 ∧ True) ∨ p4) ∨ (False ∧ p3)) → (False ∨ ((((False ∧ True) ∨ p3) ∧ p4) ∨ ((True ∧ (p2 ∨ p3)) ∨ (True → ((False ∨ True) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248030816751947296456877100275 : ((p1 ∨ p5) ∨ ((p5 → (((False ∧ p5) ∨ (p5 → True)) ∧ (((False ∨ True) ∨ (True → p2)) ∧ (p4 ∨ (True ∨ p5))))) ∨ ((True ∧ p4) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343518233634698523626781971625 : (p2 → ((p3 ∧ p2) → (((p1 → p2) → ((((p5 ∧ p1) ∨ True) → p1) ∧ (((False → (p1 ∨ (True ∧ p2))) → p3) ∧ False))) ∨ (p3 ∨ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350237061923205307574135626452 : (p4 → (((p4 ∨ False) → (True ∧ (((False ∨ False) ∨ (False → ((p3 → (p2 ∧ (p2 ∨ (False → (p1 → True))))) ∧ (p4 ∨ p5)))) → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354943686508884022770907694755 : (p5 → ((True → ((((((p2 → (True ∧ p3)) → p4) → p2) ∧ (True → True)) → (((True ∨ p3) ∨ (True ∨ p5)) → (p5 ∧ p4))) ∧ False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_581849842448699620847369603740 : (((p4 → (p1 ∨ ((True → (((((p1 → p2) ∨ False) ∨ p5) ∨ (((p1 → (p1 ∧ p5)) ∨ p1) ∧ p4)) ∨ (p4 ∨ p4))) ∨ (False ∧ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134028394524466513881587911774 : (((((p3 ∨ (p1 ∧ ((((p5 ∧ ((p5 ∨ p2) ∧ ((p3 ∧ p1) → p2))) → p2) ∧ True) ∧ p3))) → False) ∨ False) ∨ True) ∨ ((p5 → True) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688623994951093742754955540596 : ((((p4 ∨ (p1 ∧ (p3 → ((p5 ∧ (p3 ∨ ((p1 ∨ True) ∨ (p2 → p1)))) ∨ p5)))) ∧ (((p1 → p4) → ((p3 ∧ True) ∨ p5)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190957886208001877715589154337 : (((p2 ∨ (p3 ∧ (p4 ∨ True))) ∧ ((p4 ∨ p5) ∨ p2)) ∨ (True ∧ ((((p5 ∧ p4) ∧ ((p1 ∧ p3) ∨ (p2 → False))) ∨ True) ∨ (p4 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64200873345587552604203111050 : ((False ∨ (p1 ∧ ((((p2 → (((((False → False) ∧ True) ∨ ((p2 ∧ p4) → (False ∨ p4))) ∨ p5) ∨ True)) ∨ p5) → False) ∨ (False → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_396385009211884136166128327495 : ((((p5 ∧ (((p4 ∧ p4) → (((((((False ∨ p2) → (False → p4)) → p4) ∧ True) → True) ∧ p5) ∨ p3)) ∧ (False ∧ (p4 → p2)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_60206903421739077418219713223 : (((True → True) → ((p1 ∨ ((p4 ∨ (False ∧ (((((p1 ∨ p5) ∧ p3) ∨ p4) ∧ p1) ∧ False))) ∧ p4)) → (((False ∧ p4) ∨ p5) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49381448257632604571577126189 : ((((((True → False) ∧ ((p2 ∧ p5) → ((((p2 ∧ (p3 ∨ (p2 ∧ p4))) → False) ∨ p3) ∧ p3))) ∧ True) ∧ True) → (p5 ∨ (p3 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135284059502010882421846753593 : (((p2 → ((((p1 ∨ p2) → ((((p1 → True) → p1) ∨ p1) ∨ p1)) → ((p1 ∨ False) ∨ p2)) ∧ p5)) → (p3 ∧ p3)) ∨ ((p3 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117237137290333248585854960807 : ((True ∧ (p4 ∧ ((p5 → ((True → p5) ∧ p2)) → (((p3 ∧ (p2 ∨ (((True ∧ True) ∧ p5) ∧ (False → p3)))) ∧ p5) ∧ False)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748291178106241898350437985413 : ((((p2 → False) → (p3 ∧ (((True → ((((p3 ∨ p5) ∧ (p3 ∨ p1)) ∧ (p1 → (p3 ∧ p5))) ∨ (p2 → (p3 ∨ p2)))) ∧ p4) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325153480612713268029123613318 : (p5 ∨ (True ∧ ((False → (p5 ∧ ((True → p4) → False))) → (((True ∧ (True ∨ False)) ∧ (p5 ∧ (False → p4))) → (((True ∨ False) → False) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704350153031555090373583649911 : (((((((p5 ∨ p1) → p1) → p5) → (True ∧ (p4 → p1))) → (((p3 → p4) → ((True ∨ (False ∨ p5)) ∧ ((p1 ∧ p4) ∨ False))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145139491043718959535568648912 : (((((False ∧ p1) → ((p2 → True) ∧ (True ∧ p2))) ∨ p1) → (((p4 ∧ (True ∨ p1)) ∧ (p2 → p3)) ∨ True)) ∧ (False → ((p3 → True) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309916936670436302279359942655 : (p2 ∨ (((((p1 ∧ p2) → p2) ∨ ((p5 ∧ ((False ∧ (p4 → p4)) ∨ p5)) ∨ (p3 ∧ p5))) → p2) ∨ (((p3 ∧ False) → (p3 → p3)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219774315162896497081371534530 : ((p2 → ((p2 ∨ p5) → False)) → (p2 → (((p3 ∧ p4) ∨ ((p5 ∧ ((p3 → ((True → p1) ∨ (False ∨ p3))) → p3)) → (p1 → False))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p2 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680729958365846356158467445442 : (((((False ∧ ((True ∨ False) ∨ p1)) ∨ (((p3 ∨ ((p1 → True) ∨ p5)) ∧ (p5 ∧ (p4 ∨ False))) ∧ p2)) → (True ∧ (True ∧ (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721664287012100838874799794351 : ((((True ∨ (False ∨ (p4 ∨ p3))) → ((p3 ∧ ((p1 ∨ (p3 ∨ ((p3 ∧ p2) ∨ p4))) ∨ (p4 → p1))) → ((p1 → False) ∨ (True ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214590460587251497094390416393 : (((p4 ∨ False) ∧ (p3 ∧ True)) ∨ ((p3 ∧ p2) ∨ ((((p3 ∧ (False ∧ p5)) ∧ (((True ∧ p3) ∨ (p4 → p1)) → (p1 ∧ True))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661409549058228486081074581821 : (((((p5 ∨ ((((((True ∨ (((p2 ∨ True) ∨ p3) ∧ False)) ∧ p3) ∨ (True ∨ p2)) → p5) ∧ p4) ∧ p1)) → (p1 ∨ p4)) → (p2 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585747063306993119277759768027 : (((((((((False → True) ∧ p4) ∧ p4) ∨ ((((((p2 ∨ (p2 → True)) ∨ p1) ∨ p1) ∨ p2) ∨ (True ∨ p5)) ∨ True)) → p4) ∧ p1) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209526476634995830684181964429 : ((p4 → ((True → p4) ∨ (False ∨ p2))) → (((True ∧ p1) → (True → ((((p1 ∨ True) ∨ p3) ∧ (True → (p2 ∧ p1))) ∨ p1))) ∧ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112467151796728646990797103749 : ((((((p3 ∨ (p1 → True)) ∨ (True ∨ False)) ∧ (p2 ∧ ((p4 → (p1 ∧ (p2 ∨ p3))) ∨ (p4 → (p1 → p1))))) ∨ True) → p5) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51275329890961719840232170760 : (((False ∧ (((p2 ∨ (((False ∧ p4) ∨ (False ∨ p1)) ∨ p5)) ∧ p4) ∧ (p3 ∧ (p2 ∨ p1)))) ∨ (p5 ∨ (((False ∨ False) ∧ p4) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311045070870710203194594554477 : (p2 ∨ ((p4 ∧ p3) ∨ (((p2 ∨ (((p3 ∧ p4) ∧ p1) ∨ ((p5 ∧ (((True ∨ p5) ∨ ((p2 ∨ False) ∨ p5)) ∨ p5)) ∧ p5))) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913839456079550333458159063309 : (((((((p4 → True) ∨ p3) → ((False ∧ ((p3 ∨ p3) ∧ (False ∧ p3))) ∧ False)) ∧ p3) ∧ ((p3 ∨ ((p3 → False) → (p3 → p2))) ∧ p3)) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : ((p4 → True) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : ((p4 → True) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67925279530500231933402793276 : ((p2 → ((p3 → (p5 ∨ ((p3 → (p3 ∧ False)) ∨ (p4 ∨ p4)))) ∨ ((((p4 → p5) ∨ False) ∧ (p1 ∧ p4)) ∨ ((p3 → p3) ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_171853893350600810429477414171 : ((((p2 ∧ False) → ((False → False) → (p3 ∨ (False → ((p5 → p1) ∧ p5))))) → False) ∨ (p5 → (((p3 ∧ p5) ∧ p1) → ((False ∨ p1) ∧ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49445736135496517747932602743 : (((((p4 → ((False ∨ p5) ∧ (p1 → p2))) ∨ (((p2 ∧ (True ∧ True)) ∨ (True ∨ p3)) → (p4 → p4))) ∨ p5) → ((p5 ∧ p1) ∨ True)) ∨ p1) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_233300359738546668113140075031 : ((True ∨ (p3 ∨ p1)) → ((((p3 ∧ (p5 ∧ p2)) ∧ p3) ∨ ((p2 ∧ p1) → (((False ∨ ((p4 ∨ False) → p3)) ∧ p1) → True))) ∨ (p4 ∧ p4))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223374196854461041592103673883 : ((True ∨ (p2 ∨ True)) ∧ (((p4 → p4) ∨ p2) → ((p3 → ((((True → p2) ∨ ((p5 ∨ p3) ∨ p3)) ∧ p5) ∨ (p4 → True))) ∨ (p4 ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119262367044697218122352389175 : ((p2 → (p1 → (p4 ∨ ((p4 ∨ ((p4 → p3) ∨ (((False ∨ ((p4 ∨ (p1 ∧ p2)) ∧ p5)) ∨ (p2 ∧ p2)) ∧ p5))) ∧ False)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338915480322525556672583240805 : (p1 → ((False ∨ True) → ((((p2 ∧ True) → p1) → True) → ((((((p4 ∧ p5) ∧ p1) ∨ p2) ∨ True) ∧ ((p5 ∨ (False ∨ p1)) ∨ p1)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138939887072420581802660365479 : (((((p4 ∧ (True ∨ ((True ∧ ((p4 → ((p5 ∨ True) ∧ False)) → (p5 → (p1 ∧ p1)))) ∨ p4))) ∨ p2) ∧ p1) ∨ True) → ((False ∨ p5) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773238913923810322005263231069 : (((False ∨ ((((p4 ∨ ((p1 → p2) ∧ (p2 ∧ p5))) → (((((p5 → p5) ∧ p5) ∧ p4) ∧ p1) ∧ p1)) → ((p2 → p4) ∨ p4)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50971549998969506740032119886 : (((((False ∨ True) → (p3 ∨ True)) → (((p3 ∧ (p1 ∧ (p3 ∧ p3))) ∧ (p3 ∨ p5)) ∨ p3)) ∧ ((p3 → (p4 ∧ p3)) ∧ (p2 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687926660554304868348794948400 : ((((((False ∨ False) → ((p5 → (p3 ∨ p4)) ∨ p3)) ∧ ((False ∧ p1) → (p5 → False))) ∧ (False ∨ (((p5 ∨ p2) ∨ (p2 ∨ False)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56697619446450486972267508063 : ((((p1 ∧ p2) ∨ True) ∧ (((p4 ∨ (p1 ∧ (False ∨ False))) ∨ True) ∨ ((((p2 ∧ (True ∧ (p2 ∧ (p2 ∧ p4)))) ∨ True) ∧ p2) ∨ p4))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47173120748187936475212286408 : (((((p2 ∨ p4) ∧ ((p5 → (p4 ∧ (p1 → p3))) ∨ (p1 ∨ (p1 ∧ p1)))) ∨ (True ∧ (p3 ∨ (p2 ∨ (p2 ∧ p3))))) ∨ (True → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60701918322668561701989250871 : ((True ∧ (((((p1 ∨ p3) ∨ (p4 ∧ p2)) ∧ p5) ∨ True) ∧ ((((False ∨ True) ∧ (p1 → (p5 ∨ ((False → True) ∧ True)))) ∨ p2) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658622518060989101884907542424 : ((((p3 ∨ (((True → p3) ∨ p3) ∧ ((((p1 ∨ p1) → (p3 ∨ p1)) ∨ (True ∨ ((False → (p1 ∧ p1)) ∨ p4))) ∨ True))) ∨ (p5 ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_245972283801883296638593107922 : ((p4 ∧ True) ∨ (((((True ∨ True) ∧ (p2 → (p3 ∧ p2))) → p1) ∧ (True ∨ p3)) ∨ ((((p1 ∧ ((p3 ∧ True) ∨ p4)) ∧ False) → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349863651734462846024097472685 : (p4 → ((False ∨ (((True ∧ (p3 → (p1 ∨ ((((p4 → (p2 ∨ (False ∨ p4))) ∨ p5) ∧ p2) ∧ p2)))) ∨ p4) ∨ ((True → p2) ∨ p1))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118341749895770795126548565610 : ((p2 ∨ ((((True ∧ True) → True) ∧ ((True → (((p4 ∧ False) ∧ (True ∧ p5)) → (False ∨ True))) → (p2 ∨ (False ∧ p4)))) ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347385029676730524641236501959 : (p3 → (((p4 ∧ p1) → (((p4 ∧ False) ∧ False) ∨ p5)) ∨ ((p5 ∧ True) ∨ ((p4 ∨ True) ∧ ((p2 ∨ ((p4 ∨ (p2 → p2)) ∧ p2)) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40057992118767923162915668625 : (((((((True ∨ ((p2 → (p2 ∨ (True ∨ p3))) → ((False ∧ False) ∧ p2))) ∨ p1) ∧ ((p2 ∨ p4) ∧ (p4 ∨ p5))) ∨ False) ∧ p3) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31754332331743108373843740015 : ((False ∨ ((((p5 ∨ (False ∧ False)) ∨ p2) ∧ p3) ∨ (p5 → (((p1 → ((p2 ∧ True) ∧ (p2 → p1))) ∨ p1) ∨ ((p3 → True) → p5))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_907579063392871054452468293372 : (((((True → p3) → ((((True → (p5 ∨ (p1 → True))) → ((False ∧ p3) → p2)) → (p4 ∨ p3)) ∨ True)) → ((p1 ∧ p5) ∨ (p5 ∧ False))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → p3) → ((((True → (p5 ∨ (p1 → True))) → ((False ∧ p3) → p2)) → (p4 ∨ p3)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41555426348577253114448761434 : (((((p3 ∧ (((p4 → p3) → False) ∧ (p1 ∧ False))) ∨ True) → (((p4 ∧ ((p2 ∧ p5) ∧ (p5 → p4))) ∨ (p5 → False)) ∧ p3)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171640683351863633355477404965 : ((((p5 ∨ p5) ∨ ((((p5 ∨ p5) ∨ (True ∧ p5)) → (p5 ∧ p2)) → p3)) ∨ True) ∨ (p5 ∨ (((True ∧ (True → True)) → (p2 ∨ p2)) ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60795430228489359151568070664 : ((True ∧ (False ∧ ((((((False ∧ p5) ∨ p3) → False) ∨ (True ∧ p3)) ∨ False) ∨ ((p5 → ((((p5 ∨ p1) → p1) ∧ False) → p2)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201344618677674250210523522407 : ((p5 → (p4 ∧ (p1 ∧ ((p1 → p5) → False)))) → ((p4 → p4) → (((p4 ∧ (False ∨ (p5 ∨ (p3 ∨ p4)))) ∨ True) ∧ (p3 → (p2 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115976333097173853859833483903 : (((((False ∨ True) ∧ p2) ∨ p2) → (p4 ∨ (((p4 ∧ p3) ∨ (p1 ∧ ((p3 ∧ p4) ∧ ((p2 ∧ p3) ∧ False)))) ∨ (p5 → True)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191254735239602584880523896024 : (((p3 ∧ p1) ∧ ((True ∧ (p4 ∧ p4)) ∧ (p1 ∨ p2))) ∨ ((p5 → ((p3 → ((p1 ∨ (p1 ∨ (p2 ∨ p2))) → p1)) → (p5 ∨ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351634354551975751694092507547 : (p4 → ((((p3 → p5) → (p5 ∨ ((p3 ∨ ((True ∨ p2) → p2)) → False))) → (p3 ∨ p2)) ∨ ((p2 ∧ False) → (p3 ∧ ((p3 ∨ p2) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775443056749704565262758960494 : (((False ∨ (p3 ∧ ((True → ((((p5 ∧ (p3 ∨ (p5 → (((True ∨ (p1 → p2)) → p4) ∧ p1)))) ∨ p1) ∨ (False → p4)) → p1)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165770904568323858171162508614 : (((((p4 → p1) ∧ p4) → p5) → (((True ∧ p5) ∧ p3) ∧ ((False ∨ (False ∧ p5)) ∨ p5))) ∨ (False → ((((p5 ∧ p3) ∨ p4) → True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51404178735154121534736383739 : ((((((((p4 → (p3 → p2)) ∧ p4) ∨ ((p2 ∨ p2) → p3)) → False) ∧ (p1 ∧ p5)) → True) → (((p4 ∧ p4) ∧ (p4 ∨ p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_364616619101929684436696176 : (((p5 ∨ p2) → (((((p1 → p3) ∧ (True ∨ (p3 → p2))) → True) ∧ ((p1 ∨ False) ∨ (p3 ∧ (False ∨ p3)))) ∨ (p4 → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340976414373143198480415256220 : (p2 → (((p4 ∧ p2) ∨ ((p3 ∧ (False ∨ p2)) ∨ ((p5 ∨ ((p2 → (False ∧ p4)) ∧ (p2 → ((p4 → p5) ∧ p4)))) ∨ (p5 ∧ False)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47489726258088835370631228274 : (((False ∨ ((False ∨ (p3 ∧ p4)) ∧ (p1 ∨ (((((p4 ∧ (p4 ∧ True)) ∧ (p5 ∧ True)) ∨ (p4 ∧ p3)) → p2) ∨ False)))) ∨ (p4 → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149390492287292900860882597657 : (((p5 → p4) → (((p4 → ((True → p1) ∨ p2)) ∧ p4) ∨ ((p1 ∨ (p4 ∧ p4)) → (True → (False → True))))) ∨ (((p3 → p2) → p3) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_184607205520566331165302558289 : ((((p1 ∧ (p2 → (False → False))) ∨ p2) ∧ ((p5 ∨ False) → p1)) ∨ (((p1 ∧ (p1 ∨ (p2 ∨ ((p2 ∨ p4) ∧ p3)))) → p3) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165709587609191883418739507279 : (((((p1 ∨ p4) ∨ True) → False) ∧ ((True → (((p4 ∧ True) → False) → (p3 ∨ p1))) ∧ p2)) ∨ ((((p5 → (False → False)) ∨ True) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173666517551979552620151239852 : ((((((((p1 ∨ p5) ∨ True) → p5) ∧ (p3 ∨ (p5 ∧ True))) ∧ p5) ∨ p5) ∨ True) → ((p3 ∧ (False ∧ p2)) ∨ ((p2 → (p1 → p2)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
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
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724164999102036018507718170139 : ((((p2 ∧ (p3 → p5)) ∧ (((p3 → ((((p4 → (((p4 ∨ (True ∨ p4)) ∧ True) ∧ True)) ∨ p5) ∨ True) ∧ (p1 → True))) ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157208145219456748720824472556 : ((((((p2 → (False ∨ p2)) → (False ∧ (p2 ∨ (p1 ∧ p1)))) → (False ∨ p2)) → (True ∨ p4)) → False) ∨ (p2 ∨ (True ∨ (p2 → (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113806515540293914328772327562 : (((True ∧ (((False → p2) → p4) → (((p3 ∨ p1) ∨ False) → (((p3 ∧ p2) → p1) → ((p4 ∧ False) ∨ p5))))) → (p4 ∨ p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307669141189252441374465456693 : (p1 ∨ (p2 → ((p2 ∧ (False ∨ ((p1 → (((((p4 → ((p2 ∧ p3) → True)) ∨ p1) ∧ (False ∧ p1)) → (p2 ∧ p5)) ∧ p1)) → p5))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168160463426531207937395455792 : ((((p4 → p1) ∨ p3) ∧ (((p1 ∨ (((True → p5) ∧ False) → (False ∨ False))) ∧ p1) ∨ False)) → ((True ∨ p1) ∧ (((p4 → p5) ∨ p1) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



