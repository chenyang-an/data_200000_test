variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52609902375934882346377313971 : ((((True ∧ (p1 ∧ (True ∧ False))) ∨ ((False ∧ p3) ∨ ((p1 → p5) → p5))) ∨ (p1 ∨ (((p3 ∧ ((p4 ∧ p4) ∧ p1)) ∨ False) → True))) ∨ p1) := by
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
theorem thm_5_vars_618339260350910825493191435227 : (((((p4 ∧ ((False ∨ p4) ∧ p1)) ∨ (((((p2 → p5) → (True → p1)) ∨ (p5 → p5)) → (p2 ∨ (p3 ∨ True))) → (True → p5))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_161795710511327521633782164741 : ((p5 ∨ (((p3 → ((p5 → False) ∧ (p4 ∨ (p4 ∨ p2)))) ∨ (False → (p1 ∨ (p1 ∨ p3)))) → p2)) → ((p3 → p2) ∨ ((p3 ∨ False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329272410275398618795674671060 : (True → (((p3 ∨ False) ∨ p2) ∨ ((False ∧ p1) ∨ ((p2 ∨ (((p3 ∧ (((p5 ∨ ((True → p2) ∧ p2)) ∧ p3) ∧ False)) → p4) ∧ False)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347405366274089365652552663432 : (p3 → (((((p3 → True) ∨ p5) ∧ (p3 → True)) → p1) → (((p4 → ((p1 ∧ p2) ∧ False)) → False) ∨ ((True → (p1 ∧ p2)) → (p3 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114787483962597266212307453545 : (((((p1 → p2) ∧ (p3 ∧ (((p3 ∨ True) → (False → p1)) ∨ p5))) → p5) ∧ (p2 ∨ (((p2 → False) → False) ∧ (p5 ∨ p1)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117865383885264249220652986659 : ((p5 ∧ ((((p5 → ((p5 → p4) → ((((p4 → p5) ∧ p5) ∨ p1) ∨ p3))) ∨ ((p5 ∧ False) ∧ (True ∧ p5))) → p5) ∨ True)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618948044723278877792052644637 : ((((((True ∨ p5) ∧ p5) ∨ ((((p2 → ((True ∧ (True ∨ p4)) ∨ True)) ∨ p3) ∨ (p2 ∨ p4)) → ((p3 ∧ p2) ∨ (p4 → p4)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_137220162397082271494578815753 : ((p1 ∧ ((((((p4 → (p1 ∧ (p1 ∨ p5))) ∧ False) → ((p3 → p1) → (p2 → True))) → (True ∧ p4)) ∨ p2) ∨ False)) ∨ (True ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69109383010927999530141357937 : ((p5 → ((False ∨ ((((p3 ∧ (((False ∧ p4) ∧ p1) ∨ ((p4 ∧ True) ∨ p3))) ∨ p3) ∨ p2) → (True → (p1 ∧ p2)))) ∧ (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589878174184937520091607027560 : ((((((((True ∧ p2) ∧ ((p4 → (p4 ∧ p3)) ∧ p3)) ∨ (False → ((p4 ∧ (True ∨ p5)) ∨ p5))) ∨ ((False ∧ p2) ∨ p5)) → False) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49287952737027247836199473275 : (((p5 ∧ (((p1 ∧ (((p4 ∨ (p4 ∨ p1)) ∧ p1) ∨ p2)) ∧ (p4 → True)) ∧ (p2 ∨ ((p1 → p1) → p1)))) ∨ ((False → False) ∧ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258824126629191126344281569965 : ((True → p1) → (((((((False ∨ p4) ∧ ((p2 → (False ∧ False)) ∧ p2)) ∨ (p1 ∨ False)) ∨ (p2 ∧ (p5 → (p1 → True)))) → False) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111571606067842401461312334756 : (((((True ∧ p2) ∧ (((((False ∧ p5) ∨ (((p1 → (p2 ∧ p3)) ∨ p4) ∨ p5)) → False) ∧ (p1 ∧ p4)) ∨ p3)) ∧ p1) ∨ p5) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190991874651970803635827206996 : ((((p1 ∨ p2) ∧ (p4 → p2)) ∨ ((p4 ∨ p2) ∨ p4)) ∨ (p5 → (p2 ∨ (True ∨ ((p2 ∨ ((p1 ∧ True) → p4)) ∨ (False → (p1 ∧ True))))))) := by
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
theorem thm_5_vars_755671724322717368072955338934 : (((p1 ∧ (((((False ∨ ((False ∨ p4) ∧ (p1 ∨ p3))) → (p3 → p5)) ∨ (p4 ∧ False)) ∧ ((p2 ∧ ((True ∧ False) → p2)) → p3)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216748647516222647679147271398 : ((((True → p5) → p4) ∧ p2) → (False ∨ ((p5 ∧ ((p2 ∨ True) ∨ (True ∨ False))) → (((p1 ∧ (p1 → False)) ∧ p2) → ((p1 → p5) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h4.left
  let h12 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h5.left
  let h20 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h4.left
  let h24 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h27 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h28 := h22 h27
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h30 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h31 := h22 h30
      -- False on the left can always be used.
      apply False.elim h31
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h34 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h35 := h22 h34
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- False on the left can always be used.
      apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260054599185286466292505945403 : ((p2 → False) → (((((p4 ∧ ((True → False) → (p2 → ((p1 → p2) ∧ p5)))) ∨ (True → (False ∨ p3))) → p1) → p1) ∨ (p4 → (p4 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61372539125000165925272697609 : ((p1 ∧ (((p5 ∧ (False ∨ ((p1 → ((False ∨ (((p5 → (p3 → p2)) ∧ (p2 ∨ p2)) ∨ (p4 ∨ False))) → p3)) ∧ p3))) ∧ p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115734154134663255952213228824 : ((((True → (p1 ∨ True)) ∨ (p2 → p2)) → ((p1 ∨ p2) → (p5 ∨ (((p4 ∧ ((p3 → p5) ∧ (p1 ∨ False))) ∧ True) ∧ p5)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68854484145701635230970732332 : ((p4 → ((p1 ∧ p4) → ((((True → p4) → (((p4 → p1) ∧ p5) ∨ ((True ∧ (p5 → p3)) → False))) ∧ (p3 ∧ p1)) ∧ (True ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650721602140802375019387897717 : ((((((p3 ∨ p1) → (((p3 ∨ p2) → p4) → (p2 ∨ p1))) → (p2 ∨ ((False ∨ ((p2 → p3) ∧ p5)) ∧ (p2 → p5)))) ∧ (p5 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748258545022079258944317812502 : ((((p2 → True) → (p2 → (((p2 → (((p4 ∧ (True ∨ p3)) ∨ True) ∧ ((p3 ∨ (p2 → ((True → p3) → p2))) → p5))) ∨ True) ∧ p2))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324167695804895287153616732917 : (p5 ∨ (((((p5 → p3) ∧ p3) ∨ (p5 ∧ p2)) ∨ (p5 ∨ p1)) ∨ (((True ∧ p1) → ((p5 ∧ False) ∨ True)) ∨ (True ∧ (False ∧ (p3 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_151141232478548826511851182420 : ((((((p2 ∧ p2) → ((p2 → (((p1 → True) ∨ p1) ∧ False)) ∧ p3)) ∨ (False ∨ True)) → (p3 ∨ False)) → p5) → (((p1 ∨ False) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38635021882108552416378257311 : ((((p2 ∧ ((p2 ∧ (p1 ∨ (p1 → False))) ∧ True)) ∨ ((((p5 → p4) → p1) → ((p1 → p5) ∨ False)) ∧ ((p4 ∨ False) → False))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149855922212228590109488206241 : ((p1 ∨ (p1 → (True ∧ ((p4 → (p3 ∨ (p2 ∧ ((p4 → (p2 ∨ p5)) ∨ p4)))) ∧ (p2 ∨ (p2 ∨ p3)))))) ∨ ((p2 → p2) → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352672587704552016670828672457 : (p4 → ((p1 ∨ False) ∨ ((((((False ∨ (p5 → p4)) ∧ p5) → True) → (False ∧ ((False → False) ∨ ((True ∧ p2) ∧ p1)))) ∧ (True ∨ False)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190804630714038030805891448613 : ((((True ∧ p4) ∨ ((True → p2) → False)) ∨ (p5 ∨ p3)) ∨ (p1 → ((((((p4 ∧ True) ∨ (p1 ∨ p1)) ∧ p5) ∧ p1) ∧ False) → (p3 ∨ p2)))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685783596678921214310331872874 : (((((((p3 → ((p1 → p2) ∧ p5)) → (p5 ∨ (p2 ∨ (p5 ∨ (p4 → p3))))) → p2) → p3) → ((False ∨ (p3 ∧ False)) ∧ (p4 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61795987397674569661083162085 : ((p2 ∧ ((((p4 ∧ (((((p3 ∨ False) → p1) ∨ p2) ∨ ((p4 ∨ p2) ∧ ((p2 ∧ p2) → p3))) → p3)) → (p3 ∧ p3)) ∧ p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183986415321040422602697714004 : ((((((p5 ∨ (p3 ∨ p1)) ∨ p4) ∨ (p1 ∧ p3)) ∧ p3) ∨ p2) ∨ (((p1 → p2) ∧ p2) → (((p5 ∧ (p2 ∨ p1)) ∨ (p4 → p1)) ∨ True))) := by
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
theorem thm_5_vars_611285324864125926422068505579 : ((((((p2 ∨ p3) ∨ ((((((p3 ∧ False) → p2) ∧ ((False ∨ True) ∨ p3)) ∨ ((p3 ∧ p3) ∨ False)) ∨ True) ∧ (p2 ∨ p4))) → False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_158646412776228679549254876010 : ((p1 ∧ ((((p3 ∧ (False → (False → False))) ∧ True) → p1) ∨ (p4 ∨ (p4 ∧ (True → (p2 → False)))))) ∨ (True ∨ ((p4 ∨ (p4 → True)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303900058873234696049091918724 : (p1 ∨ (((((p3 → p3) ∨ p4) → (((p4 ∨ (p3 ∧ p5)) ∧ p5) ∨ (True → True))) ∧ ((((False → p4) ∧ False) → p5) ∨ (False → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745943188096800739625952325219 : ((((False ∨ p4) → (((True → ((p2 ∨ p2) ∧ ((p4 → ((p3 → (False ∧ (p3 ∧ (p5 ∨ p1)))) ∧ p2)) ∨ p5))) ∨ (p2 ∧ p4)) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680318041150956909471486867879 : ((((((p5 → (p2 ∧ ((False → (p1 ∨ False)) ∨ (p1 ∧ (p4 ∨ p4))))) ∧ True) ∨ (False → (False ∨ False))) → ((p4 → p4) → (p5 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53851431175091365006650818478 : (((((p5 → p4) → True) ∧ (p3 ∧ (p2 ∨ (p1 ∧ p1)))) ∨ (((p1 ∧ p2) ∨ ((((False ∧ p2) ∨ (p5 → p3)) ∨ p1) → True)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791365042579394000508379664355 : (((True → ((((p1 ∨ (p1 ∨ p3)) ∧ ((p4 ∧ p4) → ((((False → p4) ∨ p2) → (p2 ∨ p2)) ∧ False))) ∨ ((True ∧ p1) ∧ p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42559738606233205440760571643 : (((p1 ∨ (p4 ∨ (((((p3 → (p2 ∧ ((p2 ∧ True) ∧ (p5 ∨ (p2 → False))))) ∧ p5) → ((p4 → False) ∧ p5)) → p4) ∧ p2))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52784110275733272457177837478 : ((((False ∨ ((True ∧ p5) ∧ (p4 → (p5 ∧ (True → p3))))) ∨ (p1 ∧ p5)) → ((False ∧ p5) ∧ (((p5 → p2) → p5) ∨ (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233039362325192435336814820569 : ((p4 ∧ (p5 ∧ p5)) → (((((((p1 → p2) ∧ p2) ∨ p1) ∨ (p3 ∧ p2)) ∨ ((p5 ∧ p3) ∧ False)) ∧ p2) ∨ (False ∨ (True ∨ (p2 ∨ False))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346330763397332759227928994343 : (p3 → (((((p4 ∨ (p5 ∧ True)) ∨ (False → ((p5 ∨ p2) → False))) → (p2 ∧ (True → False))) → ((False ∧ (p3 ∨ p5)) ∨ p2)) ∨ (p4 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ (p5 ∧ True)) ∨ (False → ((p5 ∨ p2) → False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145126688569860353829504402220 : (((p4 ∧ (((p4 ∨ (p1 → (False ∧ p1))) ∧ p1) ∧ p5)) ∨ (p5 → (p5 ∨ (True → (p5 ∧ (True ∨ False)))))) ∧ (p2 → ((p4 → p1) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655468658008209971784703665723 : (((((p4 ∨ (((((p2 ∧ ((p4 ∨ ((p1 → True) ∨ False)) ∧ p1)) ∧ (p1 ∧ p4)) ∧ False) ∧ p2) ∧ p4)) ∨ (False → p5)) ∨ (p2 ∨ False)) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774866227301024671938081132596 : (((False ∨ (((p3 → (p4 ∧ p5)) → p5) ∨ (((False → ((False ∨ p2) ∨ (p3 ∨ ((p3 ∧ p3) ∨ p3)))) ∨ p2) → ((p1 ∧ p3) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717109114260966557046566523804 : ((((False ∨ ((p1 ∨ p3) ∨ False)) ∧ ((p2 → (p3 ∧ p5)) → ((p3 → p2) ∧ (((True ∨ ((False ∧ p2) → p5)) → (p4 → True)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148085522265644257947993888764 : ((((p1 ∨ (p5 → (((p3 ∧ (p1 ∨ ((p1 ∧ p1) → p3))) ∨ p3) ∨ (False ∧ p2)))) ∨ p4) → (p5 ∧ p2)) ∨ (False → ((p1 ∨ False) ∧ p5))) := by
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
theorem thm_5_vars_175531942496527905134402907022 : ((p4 → (((p5 ∨ (p5 ∨ p1)) ∨ p3) ∧ (p3 ∨ (p4 ∨ (p4 ∧ (p5 → p1)))))) → (((False → p2) → (p2 ∨ ((p1 ∨ True) → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648336270124769992247761179992 : (((((((((False ∧ p5) ∨ (p2 → (((True → False) ∧ p2) ∨ (p3 → p4)))) ∧ True) → ((True ∧ p4) ∧ False)) ∧ True) ∨ False) ∧ (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337340117756063136231178632298 : (p1 → ((((p3 ∨ True) ∧ (p4 → ((True → ((False → p2) ∨ (((p4 ∧ p4) ∨ p4) ∨ p5))) → (False ∧ p1)))) ∧ False) ∨ (False → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691631361792699837425470747438 : ((((p3 ∧ (p2 → ((True → (p3 ∨ (False → p5))) ∧ (p4 ∨ (False ∧ (p5 ∧ p5)))))) → (False ∨ ((p2 → p4) ∨ ((False → p5) ∨ p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112239448171022196434374181786 : (((p3 ∨ (((p1 ∨ (p4 → p4)) ∧ ((False ∧ (True ∨ False)) ∨ (p5 ∨ (p4 ∨ ((False ∨ True) → (True ∨ False)))))) ∧ True)) ∨ p2) ∨ (p2 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303936800375939658991188089132 : (p1 ∨ (((((True → p3) → p4) ∨ (True ∧ p2)) ∧ (p4 → ((p3 → (((p4 ∧ (p1 ∧ (False → p4))) ∨ False) ∧ (p3 → p3))) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217990600051829202577805334514 : (((p4 ∧ p3) ∧ (False → p2)) → ((p5 ∨ ((True → (((p4 → (p5 ∧ True)) → True) → (p1 → (p3 ∧ p1)))) → (p1 → (p5 ∧ p3)))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147412075484041443954930112333 : (((((p4 ∨ (p5 ∧ p1)) → p2) ∨ ((p1 ∧ ((p3 ∧ (True → p3)) ∧ ((p1 ∧ p4) ∨ p5))) ∨ True)) ∨ True) ∨ ((p4 ∧ True) → (p2 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323244139990250837505531926441 : (p5 ∨ (((p3 ∧ p3) ∨ (p2 ∨ ((((p2 → p1) ∧ p3) → (p3 ∧ ((True → p5) ∨ p4))) → (p4 ∧ ((p1 ∨ p1) → True))))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776715936429644811963497363257 : (((p1 ∨ (((((p4 → (True ∧ (((True ∧ p5) ∧ p3) ∨ (p4 ∧ (p1 ∨ True))))) ∨ (p5 ∧ (p1 → p4))) ∨ (False ∧ False)) → p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342278200253852461388310937441 : (p2 → (((((p5 → True) ∨ True) ∧ ((p3 ∨ True) ∧ (((p3 ∨ (True → False)) ∧ p2) ∨ p1))) → p3) ∨ (((p3 ∧ False) ∨ p3) → (p2 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127912216800270082802677028070 : ((False → (((False ∧ False) ∧ p5) ∧ ((((((p2 ∨ p5) → p4) → (p1 → (p4 → ((p3 ∧ p4) ∨ p1)))) → p5) ∧ p2) → p1))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136054107002191041335870034537 : (((((p5 ∧ (p3 ∨ p5)) ∧ (p1 ∨ p3)) ∨ p5) ∧ (p4 ∨ (False ∨ ((True → (((p4 ∧ True) ∨ p5) ∨ False)) → False)))) ∨ (True → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133562390041667309934427234081 : (((((((p3 ∨ ((True → (p1 ∧ (((p3 ∧ True) ∧ p5) ∨ p1))) ∨ (p3 ∨ False))) → p4) ∨ p3) → p2) ∨ True) ∧ False) ∨ ((True → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244690742552488039749255831360 : ((p1 ∧ True) ∨ ((((p2 → (p3 → p2)) → ((((p3 ∧ (p2 ∧ (p4 ∧ True))) ∧ (p2 ∨ p1)) ∧ p4) ∧ p1)) ∧ p4) → (p4 → (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → (p3 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (p2 → (p3 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h18 := h13 h15
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- We need to get the left conjuct of h20 based on <expert-advice>.
  let h21 := h20.left
  -- We need to get the left conjuct of h21 based on <expert-advice>.
  let h22 := h21.left
  -- One of the premise coincides with the conclusion.
  exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134202567536170540905613723727 : (((((True ∧ p3) ∧ ((p3 → p4) → ((p2 ∧ True) ∨ p4))) → ((p2 ∨ (p4 ∧ p1)) ∧ (p1 ∧ (p2 ∨ p1)))) ∨ p1) ∨ ((p2 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174016795864462442342268998147 : (((p4 ∧ ((((p3 → p2) ∨ p3) ∨ (p3 ∨ (False ∧ (p5 → p3)))) ∧ p5)) → p1) → ((p5 ∨ p5) → (((p5 → (True → p3)) ∧ p1) → p1))) := by
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
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166117983735063497003097458243 : ((True ∧ (((p1 → (False ∨ ((False ∧ False) ∧ (p5 ∨ (p3 ∧ p5))))) ∨ (p5 ∧ p3)) ∨ p3)) ∨ (True ∨ ((True ∧ (False ∨ (p1 ∨ p1))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117420584968132803908845527211 : ((p1 ∧ (((True ∨ ((p4 ∧ p3) ∨ False)) → (True → ((((p4 ∧ (p2 ∧ True)) ∧ p2) → (True ∧ True)) ∨ p3))) → (p1 ∨ False))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622377668666926818788067226364 : ((((p3 ∧ ((((True ∧ p3) ∨ False) → (False ∧ ((((p2 → p4) ∨ (p5 ∨ p5)) → p1) ∧ p3))) ∨ (False ∨ ((p2 ∧ p4) ∨ p2)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_40648283188700225136433420995 : (((((p1 → ((((p5 → ((p3 ∨ p1) ∧ (p3 ∨ p5))) → False) → ((p5 → p3) ∧ (p3 ∨ p2))) → (True ∧ p4))) → p2) → p1) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206362583963373679838366570907 : ((p2 ∨ ((p4 → False) → (p5 ∨ p1))) ∨ (((p4 → (p4 → (p4 ∧ (True → (p5 ∨ (True → (True → p5))))))) ∧ True) ∨ ((p2 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62427871961910262214960128065 : ((p3 ∧ (((p5 ∨ (p3 ∨ p1)) ∨ False) ∨ ((p3 ∨ False) → (((p1 ∨ (False → (p2 ∨ ((p3 ∧ (p2 ∨ p4)) → p4)))) → True) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124122418871387898385973927030 : ((((p4 ∧ (p2 ∧ True)) → ((p3 ∧ p5) ∨ (p5 ∧ p5))) ∧ ((p1 → (False ∨ (((p2 ∨ p3) → True) → p1))) → (p5 ∧ p1))) → (p3 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (False ∨ (((p2 ∨ p3) → True) → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43868496012863133809559488021 : (((((p3 ∨ (True ∧ (p5 → p2))) ∨ ((((p3 → (p3 → p4)) ∨ p3) → p5) ∨ ((True ∧ (True ∧ p4)) → p4))) ∧ (p4 → False)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241614301970185609782875933808 : ((False → p4) ∧ (True ∧ ((((p2 ∧ False) ∧ p1) ∧ (True ∧ (False ∧ (((p1 → False) ∧ (False ∨ p3)) ∨ True)))) ∨ ((p5 → p2) → (p5 → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65301212631185505724430447578 : ((p3 ∨ ((((((((p1 ∧ p4) ∨ False) → p4) ∨ (True → p4)) ∧ p1) ∨ p2) ∧ (((p1 → False) → (p4 ∧ p4)) → p5)) → (p3 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51138359022405690083976960801 : ((((((p4 ∧ (p1 → ((((p5 ∧ p2) → True) → p3) → p5))) → (p3 → p1)) ∨ False) → False) ∨ ((p2 ∨ p1) ∨ ((p5 → p5) → True))) ∨ p5) := by
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
theorem thm_5_vars_244161819320509033312804027955 : ((True ∧ p4) ∨ ((p3 ∧ p4) ∨ ((p2 ∧ (p3 ∨ (((p2 → p4) ∨ True) → (p4 ∧ (p2 → (p3 → p1)))))) ∨ (((p5 ∧ False) ∨ False) → p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150040650177639011123085698253 : ((p5 ∨ (p5 ∨ (((p1 ∧ ((p5 ∧ ((((p2 ∨ False) ∧ p3) → p3) ∨ True)) ∧ p1)) → False) ∨ (p5 → p3)))) ∨ (p3 → ((True → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258217029551326195109380532716 : ((p4 ∨ p5) → (((((True → p3) ∨ p2) ∨ ((True ∨ p5) ∨ ((p4 ∨ (p5 → p3)) ∨ ((p2 ∨ (p5 → (p2 ∨ p1))) ∧ p3)))) → p1) ∨ True)) := by
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
theorem thm_5_vars_174405262279809408275724659309 : ((((((False ∧ p1) ∨ (p3 ∧ p2)) → p2) ∨ p1) ∨ (True → ((p2 → False) → p1))) → (((p5 ∧ True) → p1) ∨ ((False → (False ∨ p2)) ∨ p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51960372292737431981936130695 : (((((p5 ∧ (p3 ∨ p4)) ∨ True) → (p4 ∧ (((p2 ∧ p1) → p5) ∨ (p2 ∨ False)))) ∨ (p2 ∧ ((True ∧ ((p1 ∨ p4) ∨ p5)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635152187882193095676333196747 : (((((((p2 ∨ True) → p4) → ((p3 ∧ (((p5 ∧ ((p4 ∨ False) ∨ (False → p3))) ∧ True) ∧ p3)) ∧ False)) → (p4 → (p4 ∧ p2))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253836625339005244260903534427 : ((p1 ∧ p2) → (p4 → (True → ((p5 ∨ ((False ∨ (((p3 ∧ (p3 ∨ ((p4 → p5) ∨ p3))) ∨ p2) ∨ p4)) ∧ p1)) ∨ (True ∨ (False ∨ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649837435311618733227189875965 : (((((p5 ∨ (((p3 ∧ (((p3 → (True ∨ (p2 ∧ p2))) ∧ p3) ∧ (p4 ∨ p4))) ∨ (p2 → p2)) ∨ p1)) → (False ∨ p1)) ∧ (True ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62368857861520537632599385637 : ((p3 ∧ (((((True ∧ p1) ∧ (True ∧ p4)) ∧ (p4 → False)) ∨ (((True ∧ p5) → p1) ∨ p4)) ∨ ((((p2 ∨ True) ∨ p4) ∧ False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160650377637804057385678838640 : (((((p5 → p2) → (p2 → ((p5 ∨ False) → p5))) → False) → (p2 ∧ (False ∧ ((False → p2) ∨ p4)))) → ((p2 ∨ p4) ∨ ((p1 → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114355990031516278834869381784 : (((((((((p5 ∧ p1) ∧ (p2 ∧ (p1 ∧ (p1 ∧ True)))) → p3) → False) ∨ p1) ∧ p1) ∧ False) ∨ (((False ∨ p4) ∨ p2) → p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143328730165283410471904323500 : ((p4 → ((False → ((p5 → (False ∨ (p1 ∨ p3))) ∨ (p3 ∨ p4))) ∧ (((p3 ∧ p4) ∧ p2) ∨ (p3 → (p4 ∨ False))))) → ((p4 → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177868398489979707977480490386 : ((((p3 ∨ ((p4 → p5) → (((p4 ∨ p3) ∨ p3) → p2))) ∨ p1) ∨ p2) ∨ (((p4 ∨ ((p5 → (True ∨ p5)) ∨ p1)) ∧ True) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764773262318528440260628100210 : (((p4 ∧ (((p3 ∧ (((True → ((True → p3) → p1)) ∨ p3) → (p1 ∨ (((p4 → ((p5 ∧ p3) → p4)) ∧ p3) → True)))) ∧ p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764229599618492810021417934050 : (((p4 ∧ (((((p5 ∨ p1) → (((p4 ∨ p1) ∧ ((p3 ∨ p5) → (((p4 → (p5 ∧ p4)) → p2) ∨ p5))) ∧ p3)) ∧ False) ∨ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192021647088319954568303670743 : ((p2 → ((p5 → (((p1 → p5) → p3) ∨ p2)) ∧ p5)) ∨ (((p2 ∧ (p1 ∧ p2)) → True) → (p3 ∨ (False → ((p3 ∧ (p4 ∨ False)) ∨ True))))) := by
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
theorem thm_5_vars_317768893076325548186839252253 : (p4 ∨ ((((p4 ∨ ((True → True) ∨ (p4 ∧ True))) → (p5 → (True → (p3 ∨ p4)))) ∧ ((p2 → True) ∨ ((False → (True ∨ True)) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98809804869561457877402071230 : ((True → (((((p1 ∨ (p2 → (p2 ∨ (p4 ∧ p4)))) → p5) → (p5 → (True ∧ (p5 ∧ False)))) → (p2 ∨ (p2 ∨ (p5 ∧ p1)))) ∧ p5)) → p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66623945345270262099975952302 : ((True → ((((p2 ∨ False) ∨ p2) ∧ ((p5 ∧ (p2 ∧ True)) ∨ (p3 → ((p2 ∧ p4) ∧ False)))) → ((((p2 → False) ∨ p1) ∨ True) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172790701611329308280815922884 : (((p1 → p1) → (p3 ∨ ((p5 ∨ (p2 ∧ (True ∨ ((p3 → p4) ∧ p2)))) → p3))) ∨ (((p3 ∧ p2) → ((True → True) ∧ (p2 → p3))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111730045040607819151186998928 : (((((True ∧ p1) → ((((p5 → p3) → True) ∨ (True ∨ (p2 ∨ ((p3 ∧ p2) ∧ ((p1 ∧ True) ∧ p4))))) → p3)) → p5) ∨ p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254020489324406908883271879114 : ((p2 ∧ True) → ((((p1 → ((False ∨ (True ∨ (True ∨ p4))) ∧ True)) → ((p1 ∧ (p3 ∨ p1)) ∧ ((p3 ∨ True) → (p4 ∨ p4)))) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114343992228256992290102087629 : (((p3 ∨ (p3 ∧ ((p3 → (True → p4)) ∧ (False ∧ ((((True → p2) ∧ p3) ∧ False) ∨ p2))))) ∧ (True ∧ (True → (p2 → p4)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130617156769574714865590061764 : (((((((p5 ∨ (True ∧ (True ∧ p4))) ∧ False) → (p5 → p5)) → (p1 ∨ False)) ∨ True) ∨ (((p3 → False) ∨ p1) ∧ p3)) ∧ ((p2 → True) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



