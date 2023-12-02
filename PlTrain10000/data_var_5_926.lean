variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732774960294332541410618209927 : ((((p1 ∧ p5) ∧ ((p4 ∧ ((False ∧ False) ∨ p2)) ∨ ((p4 ∧ (p2 ∨ p3)) ∨ (p4 ∨ (p5 ∧ ((p1 ∨ ((p4 → True) ∨ p3)) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113481888197103170173812293295 : ((((((p3 ∨ p4) → ((p5 ∨ p4) ∧ True)) ∧ (((p2 → p5) → ((False ∧ p4) ∧ p3)) ∨ p5)) ∨ (True → p5)) ∨ (p4 → p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158749675889960394440122967920 : ((p4 ∧ ((((p2 ∧ (True ∧ (False ∨ p1))) ∨ p1) → ((p2 → p5) ∧ (p4 ∧ (p1 ∨ p5)))) → p3)) ∨ ((False ∧ p3) ∨ (p4 ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158655323969610513045412283856 : ((p1 ∧ (True ∧ (((p1 ∧ p3) ∧ (p1 → p2)) ∧ ((p4 → ((p1 ∧ p2) ∨ p2)) ∧ (False → p1))))) ∨ ((p3 ∧ False) ∨ (p4 → (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14843392274534743110232182407 : (((((p2 → ((p4 ∧ True) ∨ ((True ∧ p5) → p4))) ∨ p2) ∧ (p1 ∧ (((p5 ∨ (p5 → p4)) → p5) ∨ (False ∧ p1)))) ∨ (p4 → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148033169920731100685818530491 : ((((p1 ∧ (True ∨ p5)) → (((((p3 ∨ p2) → p3) ∨ (p4 ∨ p2)) ∧ (p2 → p4)) ∨ p1)) ∨ (p5 ∨ p5)) ∨ (p5 ∨ (p4 ∧ (p3 → False)))) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798422181104709705693750925499 : (((p1 → ((p2 → ((p4 ∧ (True → (((p2 → False) ∧ p2) → p2))) ∨ p2)) → (p4 ∨ ((((True → p1) ∧ True) → p5) ∧ (p1 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731267532968890317881404868560 : ((((p3 ∨ (p5 → False)) → ((False ∨ ((((p4 → p3) ∨ (p1 → (p2 ∨ (((True → False) ∧ p4) → True)))) ∨ p4) → p3)) → (p3 ∧ True))) ∨ p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : (((p4 → p3) ∨ (p1 → (p2 ∨ (((True → False) ∧ p4) → True)))) ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h7
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44644186971615112292922618023 : ((((((p5 → (p1 ∧ p5)) ∨ False) ∨ p1) ∨ (((p2 ∨ (p1 → True)) → (p4 ∨ (p5 → True))) ∨ ((p3 ∧ p4) → (p3 → p4)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150638525923676845423646555658 : (((True ∨ ((p5 ∧ ((((p5 ∧ p3) ∨ p5) ∧ False) ∧ ((p1 → True) ∨ ((True → p5) ∨ p4)))) → p1)) ∧ p1) → ((p4 ∨ False) ∨ (p4 ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66092519392905680682227845177 : ((p5 ∨ (((((p2 ∧ (True ∨ ((((False ∨ p3) ∨ (p1 ∨ (p4 ∨ p4))) ∧ (p2 → (p2 ∧ p2))) → False))) ∨ p4) ∧ True) → p2) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324272956859578638944688993916 : (p5 ∨ ((p3 ∧ ((((p5 ∨ False) ∧ False) → False) → p4)) ∨ (((p3 ∨ ((p4 ∨ p4) ∧ (False ∨ p4))) → True) ∨ ((False → (p1 → p5)) → p4)))) := by
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
theorem thm_5_vars_231871698630701094617218364074 : (((True ∨ p1) → False) → (False ∨ (p3 ∧ ((p3 ∧ ((p3 ∨ ((p5 → p1) ∨ (((p1 ∨ p2) → (p3 ∧ p5)) ∧ p2))) ∨ p4)) → (False ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324172561865236745591759393341 : (p5 ∨ ((((p3 ∧ False) ∨ p1) ∨ (p4 ∧ (p4 ∧ (p1 → True)))) ∨ (p3 ∨ ((p2 ∨ p1) ∨ ((False ∨ (True → (p1 → p3))) → (p4 ∨ True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706848868929333915987098333647 : (((((p3 ∨ ((p2 ∧ False) ∨ (p2 ∧ p4))) ∧ p4) ∨ (((p5 → p5) ∨ ((p1 ∧ p1) ∧ ((p2 → p3) ∧ (p1 → (p4 → p2))))) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354856871023777007189197953178 : (p5 → (((p5 ∧ True) → ((((p3 ∨ True) → p2) → (p4 ∧ p3)) ∧ (p5 → (((p5 ∨ ((p1 ∨ (True ∧ p1)) ∨ False)) → p2) → p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148318239761767426060765600698 : (((p4 ∨ ((p1 → (p5 ∨ p5)) ∨ (((p2 → p1) ∨ ((p5 → p5) → p5)) ∨ p4))) → ((p1 → p2) → p4)) ∨ (False → (True ∧ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159078999742708221928623759169 : ((True → ((((p5 ∧ (p4 ∨ p1)) ∧ True) → ((False → p5) → ((p1 ∧ (p2 → False)) → False))) ∧ p5)) ∨ (((p5 ∨ True) ∧ (True → p1)) → p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148575132023056670689388897109 : (((((((True ∧ (p4 ∧ p2)) → True) → p1) ∧ p2) ∧ False) ∨ ((False ∧ (p2 ∨ (p2 ∧ False))) ∨ (p4 ∧ p4))) ∨ (p4 ∨ ((False ∧ True) → p3))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172318498509530494822526171122 : (((p2 → ((False ∨ (p2 ∧ False)) ∨ (p3 → True))) → ((p5 ∨ (p3 → p4)) ∨ p4)) ∨ ((p1 → ((p4 → ((p3 ∧ p2) ∧ True)) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353179635746926930826984201145 : (p4 → (p4 ∧ (((p4 → ((p2 → ((p5 ∨ ((p4 ∨ (True ∧ p5)) → False)) ∧ (True → p3))) ∧ (p5 ∨ (p3 ∧ p3)))) ∨ p2) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305535683609983121215510402590 : (p1 ∨ (((p2 → False) ∧ ((True → p3) ∧ (p4 ∧ ((p1 ∨ p4) → (p1 ∧ p5))))) → (p1 ∨ ((p5 → False) → ((False ∨ p2) ∧ (True ∨ False)))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182082627298836478948185580131 : (((p1 ∧ (p1 → ((((False ∧ p2) ∧ p5) ∨ p3) ∧ p4))) ∨ True) ∧ (((((True → ((True → True) ∨ p5)) ∨ False) ∨ (p5 → True)) ∨ p2) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228432625238549309705909113771 : ((False ∨ (p5 ∧ p3)) ∨ ((False ∧ p4) ∨ (p2 → ((p5 ∨ p2) ∨ (True ∨ (p4 ∨ (p4 ∨ ((p5 ∧ p5) → ((p1 → False) ∨ (p2 ∨ p4)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737728431564460220359484777460 : ((((p5 → p5) ∧ ((p4 → (p1 ∨ ((p1 → (p4 ∧ False)) ∨ ((p1 ∧ ((p4 → p4) ∨ False)) ∨ p1)))) ∨ ((False ∧ (p4 → p2)) → p1))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140251053230775173361757308249 : ((((((((p4 → False) → p5) → p1) ∧ ((p4 ∨ (True → p3)) ∧ (p1 → p2))) ∧ p5) ∧ p2) ∧ ((p4 ∨ False) → False)) → (p1 ∧ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (p4 ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h16 : ((p4 → False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h18 := h8 h16
    -- One of the premise coincides with the conclusion.
    exact h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h26.left
  let h28 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h29
  case inr h30 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h31 : ((p4 → False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h32
      -- One of the premise coincides with the conclusion.
      exact h24
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h33 := h25 h31
    -- One of the premise coincides with the conclusion.
    exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173867195715550314089965604061 : (((((p2 ∧ True) ∧ ((p5 → (p3 ∧ False)) ∨ (p5 ∧ (False ∧ p1)))) ∧ p4) → True) → ((((True ∨ p3) ∨ ((p4 ∨ p1) ∨ p5)) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ p3) ∨ ((p4 ∨ p1) ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216350542495442725060302575616 : ((p3 → ((p3 → False) ∧ p3)) ∨ (p1 → (((p2 ∨ (False ∧ (p2 ∨ ((p1 ∨ ((((False → p2) → p4) → p2) ∧ p5)) ∧ p3)))) ∧ p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247329347991385528626194877998 : ((False ∨ False) ∨ (False ∨ ((((p1 → (p4 → (((p1 → p1) ∨ p4) → p1))) → p1) ∧ (p2 → True)) → (((p5 → p5) → p1) ∨ (p5 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p1 → (p4 → (((p1 → p1) ∨ p4) → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140049655923658187819456692656 : ((((False → (True ∨ ((p4 ∧ p2) → ((p1 ∨ False) → p2)))) ∧ (((p5 ∧ p5) ∨ (p5 ∧ p1)) ∧ p4)) ∨ (True ∨ p3)) → ((p5 → p2) ∨ True)) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
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
theorem thm_5_vars_43040518642785013128896782497 : ((((((p1 ∨ p1) ∨ (((p5 → ((p4 → ((p1 ∧ (p1 ∨ p1)) → p4)) ∧ ((True ∨ p1) ∨ p4))) ∧ p5) → p4)) ∨ p4) ∧ p4) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318590765990437685352532708454 : (p4 ∨ ((((p5 → (p5 ∧ (((False ∧ True) ∨ ((p2 ∨ False) → (p3 ∨ p4))) ∨ p4))) ∧ p4) ∨ ((p1 ∧ p5) ∨ (False → True))) ∨ (p3 ∧ p5))) := by
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
theorem thm_5_vars_59492343909961324016831304849 : (((p1 → p5) ∨ (((((p4 → True) ∧ p4) ∧ (((p2 ∧ False) ∧ (p1 ∨ (p4 ∧ p3))) ∧ (p2 ∧ p5))) ∧ p1) ∧ ((True ∧ p2) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200118128362428260513072067393 : (((False ∨ (p4 → False)) ∧ (True ∧ (p2 → p4))) → ((((p2 ∧ ((False ∨ ((False → p3) ∨ (p5 → p3))) → p2)) ∧ False) ∨ True) ∧ (False → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200332511253719166287694399619 : (((p1 ∨ p4) ∧ ((True ∨ (p5 ∨ p1)) ∨ False)) → (((p4 ∨ (True ∧ (True ∨ p2))) ∧ ((((True → (True ∧ p5)) ∧ p3) ∨ True) → p3)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h11 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h12 := h4 h11
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h15 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h16 := h4 h15
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h18 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h19 := h4 h18
            -- One of the premise coincides with the conclusion.
            exact h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h24 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h25 := h4 h24
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h28 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h29 := h4 h28
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h30 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h31 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h32 := h4 h31
            -- One of the premise coincides with the conclusion.
            exact h32
      case inr h33 =>
        -- False on the left can always be used.
        apply False.elim h33
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h1.left
      let h39 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h43 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h44 := h4 h43
            -- One of the premise coincides with the conclusion.
            exact h44
          case inr h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h45
            case inl h46 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h47 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h48 := h4 h47
              -- One of the premise coincides with the conclusion.
              exact h48
            case inr h49 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h50 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h51 := h4 h50
              -- One of the premise coincides with the conclusion.
              exact h51
        case inr h52 =>
          -- False on the left can always be used.
          apply False.elim h52
      case inr h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h54 =>
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h55 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h56 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h57 := h4 h56
            -- One of the premise coincides with the conclusion.
            exact h57
          case inr h58 =>
            -- Disjunctions on the left can always be decomposed.
            cases h58
            case inl h59 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h60 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h61 := h4 h60
              -- One of the premise coincides with the conclusion.
              exact h61
            case inr h62 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h63 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h64 := h4 h63
              -- One of the premise coincides with the conclusion.
              exact h64
        case inr h65 =>
          -- False on the left can always be used.
          apply False.elim h65
    case inr h66 =>
      -- Conjunctions on the left can always be decomposed.
      let h67 := h1.left
      let h68 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h67
      case inl h69 =>
        -- Disjunctions on the left can always be decomposed.
        cases h68
        case inl h70 =>
          -- Disjunctions on the left can always be decomposed.
          cases h70
          case inl h71 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h72 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h73 := h4 h72
            -- One of the premise coincides with the conclusion.
            exact h73
          case inr h74 =>
            -- Disjunctions on the left can always be decomposed.
            cases h74
            case inl h75 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h76 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h77 := h4 h76
              -- One of the premise coincides with the conclusion.
              exact h77
            case inr h78 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h79 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h80 := h4 h79
              -- One of the premise coincides with the conclusion.
              exact h80
        case inr h81 =>
          -- False on the left can always be used.
          apply False.elim h81
      case inr h82 =>
        -- Disjunctions on the left can always be decomposed.
        cases h68
        case inl h83 =>
          -- Disjunctions on the left can always be decomposed.
          cases h83
          case inl h84 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h85 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h86 := h4 h85
            -- One of the premise coincides with the conclusion.
            exact h86
          case inr h87 =>
            -- Disjunctions on the left can always be decomposed.
            cases h87
            case inl h88 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h89 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h90 := h4 h89
              -- One of the premise coincides with the conclusion.
              exact h90
            case inr h91 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h92 : (((True → (True ∧ p5)) ∧ p3) ∨ True) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h93 := h4 h92
              -- One of the premise coincides with the conclusion.
              exact h93
        case inr h94 =>
          -- False on the left can always be used.
          apply False.elim h94



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139252542112222648336700366100 : ((((True ∧ p4) → (((True → p2) → p3) ∧ ((False → p5) → ((True → ((p4 → p2) ∧ p5)) ∨ (p5 → p3))))) ∨ p2) → ((p3 ∧ p5) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147255812418879656173551364559 : ((((p5 ∨ (((False ∨ (((True ∨ True) ∨ p2) ∧ p1)) ∧ p5) ∨ (True → ((p3 → p5) → p5)))) ∧ p5) ∨ False) ∨ ((p2 → p3) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117640304889344815075983435537 : ((p3 ∧ (((((True ∨ ((p3 → p2) → p3)) → (p3 → p3)) → (True → (p3 ∨ (p2 → ((True ∧ False) → False))))) → p3) → p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324196010674810777662877738646 : (p5 ∨ (((p2 → ((p1 → ((p5 → True) ∨ True)) ∨ True)) → p2) → ((((p5 ∨ p3) ∨ ((p5 → p1) ∨ ((False ∨ False) → p2))) ∨ p3) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h6 : (p2 → ((p1 → ((p5 → True) ∨ True)) ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h7
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h8 := h1 h6
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h10 : (p2 → ((p1 → ((p5 → True) ∨ True)) ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h12 := h1 h10
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h15 : (p2 → ((p1 → ((p5 → True) ∨ True)) ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h15
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : (p2 → ((p1 → ((p5 → True) ∨ True)) ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h19
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h23 : (p2 → ((p1 → ((p5 → True) ∨ True)) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h25 := h1 h23
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648914936394411191121350004026 : ((((((((p5 ∧ p2) → (p1 → ((True ∨ p1) → (True ∧ (p5 ∨ (((False → p2) ∨ p1) → p3)))))) ∨ p3) ∨ p2) → p5) ∧ (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749482108211814467928118187353 : (((True ∧ (((((p3 → p1) → p3) ∨ p1) ∨ (((p1 ∨ (p3 ∨ p5)) ∧ (p5 ∨ True)) ∨ ((True ∧ ((True ∧ p5) → True)) ∧ False))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53917753622432304378623139815 : (((p1 ∨ (True ∧ (((p1 → p4) ∧ (p5 ∧ p5)) → p3))) ∨ (p1 ∧ ((((p5 → True) ∧ (p1 ∨ (p4 ∧ False))) → p3) → (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200097027678275261660733134147 : ((((p4 ∨ False) → False) ∧ (p3 ∨ (True → p2))) → (((p1 ∨ False) → ((p4 ∨ ((p2 → (p1 ∨ p3)) → (p4 ∧ (p1 ∨ p2)))) ∨ p2)) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62425785679265834139770171646 : ((p3 ∧ ((p1 ∨ ((p2 → p4) ∧ False)) ∧ (((p5 ∨ (False → False)) ∧ p1) → (((False ∧ (p5 ∧ (p1 → (p5 → False)))) → p4) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179694021456843856153896557123 : ((((((p3 ∧ ((p2 ∧ (True ∧ p3)) ∨ p2)) → p1) ∧ True) ∨ p1) ∧ p4) → ((p4 ∨ p4) ∧ (p3 ∨ (((True → p1) → p3) ∨ (p3 ∨ p4))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47072616145790013683644428772 : ((((p5 ∨ ((p5 → (p1 ∧ ((False ∧ False) → True))) ∧ ((((p4 → True) ∧ False) → p2) → (p3 ∨ p1)))) ∨ (p4 ∧ p2)) ∨ (p4 → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219237500213743164678677942159 : ((p1 ∨ ((p2 → True) ∨ p1)) → (((p2 ∨ (p2 ∨ ((p4 → False) ∧ (p4 ∨ p1)))) → (p3 ∧ False)) ∨ (True ∨ (p4 ∨ (p1 → (True ∨ p5)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
theorem thm_5_vars_202912488346271853273269480805 : (((False ∨ p3) ∨ ((False ∧ p1) → False)) ∧ (p3 → (((p5 → ((p1 ∨ p2) ∧ (p2 → ((p5 ∧ p1) ∨ (False ∨ (False ∧ p2)))))) ∨ True) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300700065520376370701845218816 : (False ∨ ((((((p1 ∨ (((p3 ∧ (p1 ∨ True)) ∨ p2) → True)) ∨ p4) ∨ p3) ∨ (p4 ∨ True)) ∧ p2) → (((p3 ∧ p5) ∨ False) ∨ (False → p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717913161411593177004358539652 : (((((p5 ∨ (False ∧ p5)) ∧ p1) ∨ (((False ∨ (True → (((p3 ∧ True) ∨ (True → p1)) ∧ True))) ∧ ((True → False) ∧ p4)) ∧ (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47792202532246164796377734951 : (((((((p3 → p4) ∧ p3) ∧ ((p1 ∨ (((False → False) ∨ False) ∧ p3)) ∨ (((p5 ∧ p1) ∧ False) ∨ p2))) ∨ p5) → p1) → (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190015973145449203511200262137 : ((((((p2 ∨ p3) ∧ False) ∨ (False ∧ p2)) ∧ False) ∧ False) ∨ ((False ∧ p3) ∨ (((False → p2) ∨ p4) ∨ ((p5 ∧ (p2 ∧ (p2 ∨ True))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230923034021566545481532370772 : (((p3 ∧ False) ∨ p2) → (p4 ∨ (((((((True → ((p2 ∨ p4) → p5)) ∨ p1) ∨ ((p4 ∧ p5) → p2)) → False) ∨ False) → (p1 ∧ p3)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (((True → ((p2 ∨ p4) → p5)) ∨ p1) ∨ ((p4 ∧ p5) → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h8
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (((True → ((p2 ∨ p4) → p5)) ∨ p1) ∨ ((p4 ∧ p5) → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h19 := h14 h15
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115437946317530651161255945149 : (((((p4 → (p4 ∨ p1)) ∧ p4) ∧ (p2 ∨ p5)) ∨ (((p5 → p5) → (((False → (p4 ∨ p3)) ∧ p1) ∨ (p5 ∧ True))) ∨ True)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300362068288044805823244137383 : (False ∨ ((((p1 ∧ False) ∨ (True ∧ ((p2 → (p4 → p1)) → (p4 ∨ (False ∨ (p2 ∧ ((p4 → p3) ∨ p2))))))) ∨ True) ∨ ((p5 ∨ p4) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682178665099097282692216760588 : ((((((p4 ∨ (False → p2)) ∧ (p4 ∨ (((False → p1) ∧ p2) ∨ ((p1 → False) → True)))) → p3) ∧ (False ∨ (((p1 ∧ p4) ∧ p3) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44738547832425409891877553024 : (((((p5 → True) ∨ (p4 ∨ True)) ∨ ((p2 ∧ p1) ∧ (p1 ∨ (p2 ∨ ((p2 ∨ (p5 ∧ ((False ∨ p4) → True))) ∧ (p5 → True)))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721644744817618161339162627432 : ((((True ∨ ((p3 ∨ p1) ∨ p1)) → (((p5 ∧ p2) → (p3 ∨ False)) ∧ (((((p3 ∨ (p4 ∧ p4)) ∧ (True ∧ p3)) ∧ p3) ∨ p5) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314616281249496312381637098401 : (p3 ∨ (((((p3 ∧ p1) → (p5 → (False ∧ (p4 → p4)))) → (p4 ∨ p2)) ∨ (p2 → True)) ∧ (True ∨ (False → ((True ∨ p1) ∧ (p4 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56496173593850924005834298040 : (((p1 ∧ ((p4 → False) → p1)) → (((((True ∨ p4) → (p4 → (p1 ∧ False))) → (p2 ∨ ((False ∧ p3) ∧ (p5 ∨ p3)))) → p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234897416465278668837433028002 : ((True ∧ True) ∧ ((((p5 ∨ (p5 ∨ (p3 → p4))) ∨ ((((False ∨ ((True ∧ p1) ∨ p2)) ∧ (True → True)) ∨ p3) → True)) → (p3 ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_228858264855414300897059696240 : ((p3 ∨ (p4 → p1)) ∨ ((((p3 ∨ True) ∨ p4) ∧ (p2 → (False → True))) → ((p5 ∧ (p3 → p5)) ∨ (p4 → ((p4 ∧ p4) ∨ (True → p1)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219429018580330720428874527480 : ((p4 ∨ ((p2 ∧ p5) ∨ p4)) → (((((p3 → (False → False)) ∧ p5) ∨ False) ∧ (p4 → p5)) ∨ ((True ∨ (False ∧ (p4 ∧ p5))) → (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53249237528893989549631176300 : ((((p2 ∨ p1) ∧ (p5 → (p1 ∨ ((p4 ∨ (True ∧ p3)) → p2)))) ∨ (p2 → (((p3 → p2) ∧ False) ∨ (True ∨ ((True ∨ p4) → p2))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200569363398888100067376016798 : (((p5 → p5) → (p4 ∨ ((p1 → p3) ∨ p3))) → ((p1 ∧ (p2 ∧ ((p2 ∨ (p3 → (p2 ∨ (p1 ∨ p2)))) → ((p2 → p2) ∧ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41453728473144029920025223179 : ((((((((p1 ∧ False) ∨ p3) → (p5 ∨ False)) ∧ p2) ∨ (False ∨ p3)) ∧ ((((p3 ∧ p5) → p5) ∨ (False ∨ (p5 → p4))) ∧ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7729227483841137813423105788 : ((((((p3 ∨ p3) ∨ ((False ∨ p5) → ((p5 ∧ p2) ∧ ((False ∧ (p3 ∧ (False ∧ ((p3 ∨ False) ∨ p2)))) ∨ p3)))) → p5) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200965119346724826993438738685 : ((p2 ∨ ((p1 → p3) ∨ (p4 → (p2 ∨ p1)))) → (((False ∧ p2) ∨ ((p3 → False) → (p2 → p2))) ∨ (p3 ∨ (((p5 ∧ True) → p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200103087739468648088429149014 : (((True ∧ (p1 ∨ p4)) ∧ ((False → p2) ∨ True)) → ((((((p3 → p2) ∨ False) ∨ (p3 ∧ p2)) ∨ True) ∨ (True ∨ p3)) ∨ (p5 ∧ (p1 ∧ p2)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207070230796001173032081001447 : (((p3 ∧ ((p5 ∧ p5) ∧ p3)) ∧ p3) → (((p4 ∧ ((p5 ∧ (((p1 ∨ ((p4 ∨ p5) → p4)) ∧ True) → (p5 ∧ p4))) ∧ p5)) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49278313110833095220299750931 : (((p3 ∧ (p3 ∨ (True ∧ (((p1 ∨ p2) ∨ ((True ∨ (p5 ∨ True)) → (((p2 ∨ p1) ∨ p3) ∨ True))) → False)))) ∨ ((False ∧ p3) → p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_748185920568234358847802460386 : ((((p1 → p5) → (((p3 → (True ∧ (((p1 → False) → (p3 → p1)) ∧ (((((p1 ∧ p2) → p4) → p3) → True) → p2)))) ∧ p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166807892244033766495541615230 : (((((False → (p1 ∧ p3)) ∧ ((True ∧ p3) ∧ ((p5 ∧ (p1 ∨ p1)) ∧ p5))) ∧ p4) ∧ True) → (((p1 ∧ p1) ∨ p4) → (False ∨ (p3 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h13.left
    let h17 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h30.left
    let h34 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h33.left
    let h36 := h33.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h32
      -- One of the premise coincides with the conclusion.
      exact h37
    case inr h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h32
      -- One of the premise coincides with the conclusion.
      exact h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178470503737350099902667467296 : (((((p1 ∧ p4) ∨ (p1 ∨ (False ∧ False))) ∧ True) ∨ (p2 → (p3 ∨ p2))) ∨ (((((True ∨ p1) → (p4 ∨ False)) → (p1 ∨ True)) ∧ p3) ∧ p1)) := by
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
theorem thm_5_vars_111154864258816915068372529957 : (((((((True ∨ False) ∧ p2) → p3) ∨ p1) → ((p5 ∨ ((p4 ∨ (p3 ∨ (p5 ∧ p5))) ∨ p1)) → ((p2 → p3) → p3))) ∧ False) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244710667108908233313205094535 : ((p1 ∧ True) ∨ ((True → False) → ((p3 ∨ (p2 ∨ (p2 ∨ (p1 ∨ (p4 → (p5 → ((False ∧ (p3 ∧ p4)) → (p1 ∨ p5)))))))) → (p1 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h13 := h1 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h18 := h1 h17
          -- False on the left can always be used.
          apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h19 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h20
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h25 := h1 h24
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h29 := h1 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h32 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h33 := h1 h32
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h36 := h1 h35
          -- False on the left can always be used.
          apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927885364589681986112342269321 : (((((True → (p2 ∧ (p3 → p5))) ∧ (p5 → (p1 ∨ p4))) ∧ (p4 → (True ∧ (p2 ∧ ((p4 → (False → p1)) ∧ (p5 ∨ (p1 → p1))))))) → p2) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247320217765966718165498952134 : ((False ∨ False) ∨ ((p2 ∨ p4) ∨ (p5 ∨ ((p2 ∨ (True → (((p2 ∨ p2) ∨ p1) ∧ (True ∨ (p5 ∨ (False → (p5 → p2))))))) ∨ (p2 ∨ True))))) := by
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
theorem thm_5_vars_336215384525088093705243237271 : (p1 → (((p4 ∨ ((p2 ∨ (((p4 ∨ p1) ∨ p1) ∧ p1)) ∧ (p5 → ((p5 → p2) → (p2 ∨ ((p4 ∧ p2) ∨ p1)))))) → (p5 ∨ p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
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
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255921607644495787492981096593 : ((True ∨ p2) → (((p3 ∧ (((p5 ∨ p1) ∧ p2) ∧ False)) ∨ (((p3 ∧ (p1 ∧ (p2 ∨ True))) ∨ p4) → (True ∨ (False → p4)))) ∨ (p3 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65662261747962639546425736594 : ((p4 ∨ ((((p1 ∧ (True ∧ p4)) ∨ ((((p3 ∨ p4) ∨ p2) ∨ ((p5 ∧ ((p5 ∨ True) → False)) → p2)) → (True ∧ True))) ∧ True) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46878978118357298742399882690 : ((((((p2 → (True ∧ ((p3 → (((False → ((p2 → p5) → True)) ∨ (False ∨ p5)) → p1)) ∧ False))) → p3) ∧ p2) ∨ p5) ∨ (p4 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40644526771728774656321157417 : (((((p4 ∧ ((((p4 → p1) ∨ False) ∧ (False → (p2 ∧ False))) ∨ (p5 ∧ (p1 ∧ (p3 ∧ ((True → p4) ∧ p2)))))) → p2) → p5) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135165945898260535541396025529 : ((((((True ∧ (True → ((p3 → p1) → (True → p2)))) ∨ False) → ((p1 ∨ False) ∨ (p2 ∧ False))) ∧ p1) → (False ∨ p5)) ∨ ((False ∧ False) → False)) := by
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
theorem thm_5_vars_258694532113908978374248403920 : ((p5 ∨ p5) → (p4 → ((p3 ∨ (((p1 ∧ True) ∨ (((p4 → (False ∧ True)) → p3) → False)) ∧ (((True ∧ p4) → True) → p5))) ∨ (p5 ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588687741257148996728013894348 : (((((p2 ∧ (((p5 ∨ (False ∧ (((p1 ∧ (p5 ∨ p2)) ∧ p1) ∨ (True ∨ p1)))) ∨ (p3 ∧ (p5 ∧ False))) ∨ (p5 → p3))) ∨ p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200187924828932594870611530710 : (((p5 ∧ (p1 ∧ p4)) ∨ ((p1 → p2) ∧ True)) → ((True ∧ p4) → (((p2 → (True → False)) → ((p5 ∨ p3) → (p2 ∨ (p2 ∨ True)))) ∨ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111505987234377147418706094538 : (((p4 → ((p4 ∧ ((p2 ∨ p2) → (False ∨ (p2 ∧ p4)))) ∧ ((p2 → ((p4 ∨ (True ∧ p1)) ∧ (p3 ∧ True))) ∨ p2))) ∧ p2) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180247039660528615177385183573 : (((True ∨ (True ∨ ((((p3 ∨ (p5 ∨ p5)) ∨ p2) → p3) ∨ p4))) → False) → (((p4 ∨ p3) ∧ p3) ∧ ((p3 ∨ True) ∧ (False ∧ (p1 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (True ∨ ((((p3 ∨ (p5 ∨ p5)) ∨ p2) → p3) ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (True ∨ ((((p3 ∨ (p5 ∨ p5)) ∨ p2) → p3) ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ (True ∨ ((((p3 ∨ (p5 ∨ p5)) ∨ p2) → p3) ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (True ∨ (True ∨ ((((p3 ∨ (p5 ∨ p5)) ∨ p2) → p3) ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341075255627510042868637806028 : (p2 → ((True → ((p1 ∨ (False ∧ (p5 ∧ ((p1 ∨ ((p2 ∧ (p3 → ((False ∧ p1) ∨ True))) → False)) → ((p2 → p4) ∧ False))))) ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199350231661306301540640634700 : ((((p5 ∨ ((p2 ∨ p5) → p5)) → p4) ∨ p1) → ((p5 ∨ (p4 ∧ (p3 ∧ ((p5 ∧ ((True → p4) → p1)) ∧ ((p4 → p2) ∨ True))))) ∨ True)) := by
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
theorem thm_5_vars_258795087839012359453146163161 : ((True → False) → (((p4 ∨ p2) ∨ p5) → ((False ∨ ((p2 ∨ p4) → (p5 → (((False ∧ (p2 ∧ p4)) ∨ ((p1 → p4) ∨ p4)) → p1)))) ∨ p3))) := by
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55139697109726026597136300931 : ((((((p1 ∧ True) → False) ∧ p2) ∨ p5) ∨ (((((True → True) → p3) ∧ (p1 ∨ (p3 → (p3 ∧ p4)))) → p1) ∨ (True ∨ (p2 ∧ p4)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745630166061215393892588640664 : ((((True ∨ p3) → ((p1 ∨ (((p3 ∨ ((p5 ∨ False) → False)) → (((p1 ∧ (p2 → False)) ∧ p4) ∨ p3)) ∨ (True ∧ (p3 ∨ p3)))) ∨ True)) ∨ False) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2094182595000139566056292487 : ((False ∧ ((((p2 ∧ p1) → (p1 → ((False ∧ True) → (p5 ∧ (p1 ∨ False))))) → False) ∨ p2)) ∨ ((False ∧ (True ∨ p4)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111807436272241933423658915659 : ((((((p5 → (p3 → ((True → (p5 ∧ True)) → True))) ∨ p5) ∧ ((p2 → (True ∧ (p3 → p4))) ∧ p4)) → (p5 ∧ p4)) ∨ True) ∨ (False → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123219110578633986260954232594 : ((((p5 ∨ ((((p2 ∧ p5) ∧ p4) ∨ (p4 → ((p2 ∧ p5) → p3))) → p1)) ∧ (True → False)) ∧ ((False ∧ True) → (p2 ∧ True))) → (p2 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7954147455164311774972821999 : ((((((False → p2) → (False ∨ (p4 ∧ ((((False ∨ False) → (p2 ∨ (p4 ∨ False))) → (False → p5)) ∨ (p3 → p1))))) ∧ p5) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_184812683493755418634274448361 : (((((p2 ∧ p5) ∨ p3) ∧ p3) → ((p5 ∨ p1) → (p5 ∨ p4))) ∨ (((p3 ∧ (p2 → (p2 ∨ True))) ∧ False) ∨ (((True → p3) ∧ p1) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656590587526415128257023924970 : ((((((p5 ∨ ((False → p5) ∨ p2)) → (p1 → False)) ∨ ((((p2 ∧ p5) ∨ p3) ∨ ((False ∧ p5) ∨ (p4 ∨ True))) ∧ p2)) ∨ (False ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



