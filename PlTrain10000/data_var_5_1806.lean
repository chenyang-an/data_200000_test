variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118391698531744915015585239178 : ((p2 ∨ ((p3 ∨ ((p5 → p3) → p4)) ∧ (p2 ∧ (((((p4 ∧ p2) → p3) → (((p2 ∨ True) ∧ p2) ∨ p1)) ∨ p2) → p4)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777952618689128260821935981671 : (((p1 ∨ (((p5 ∧ p5) → p1) ∨ ((p5 → (p4 → p3)) ∧ ((((((p1 → p2) ∨ (p4 → True)) ∧ p4) ∧ True) → (p5 ∨ p5)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252512133877837432681857382740 : ((p5 → p2) ∨ ((p5 ∨ (((True → (p4 ∧ (p4 ∨ p5))) ∨ p2) → ((p3 ∨ (((p2 ∧ False) ∨ p1) → ((p1 ∨ p4) → p5))) ∨ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61281006923100549182486932344 : ((False ∧ (p4 ∨ (((p3 → p5) ∨ (((((((p4 → p2) → False) ∨ p1) ∨ False) → False) ∨ p1) ∨ ((False → (True ∨ p1)) ∨ p1))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586557921137454462253685006834 : ((((((False → False) ∧ ((p4 → p3) ∨ (p1 → (((p3 → (p2 ∨ (p2 ∨ ((p3 ∧ (p5 → False)) → p2)))) → False) → p4)))) ∧ p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148600652094646128952153340595 : (((p1 ∨ (p2 ∨ (((p5 → (p5 ∧ True)) ∧ p2) ∧ True))) ∨ (((p1 ∧ False) ∨ (True ∨ False)) ∨ (True ∧ p1))) ∨ (p4 ∧ (p3 ∨ (p2 ∨ False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47375512490026993425719870304 : ((((p1 ∧ p1) → ((((p5 → (False ∧ p2)) → p3) ∧ (False ∨ ((True → (p1 → p3)) → ((False ∨ p2) ∨ p2)))) ∧ p5)) ∨ (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626247929480485956583518728317 : ((((p3 → (((p3 → ((False ∨ p2) ∨ p4)) → (p3 → ((p3 ∧ p2) ∧ p2))) ∧ (((True ∨ p5) → (False ∨ p5)) ∨ (p3 ∨ p1)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_261075042572755946210394957266 : ((p4 → p3) → ((p5 ∨ (p2 ∨ ((p5 ∧ (((True ∧ ((p5 ∧ False) → (p3 ∧ False))) → (p3 ∨ p2)) → False)) ∧ (p1 ∨ (p2 → p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147256406848351734863738008263 : ((((True → (p1 ∨ (((p5 → (p2 → p1)) ∧ ((p1 → (p4 ∨ p4)) ∧ p2)) ∨ (True ∧ True)))) ∧ p5) ∨ p2) ∨ ((True → p3) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783572166581801624286729402387 : (((p3 ∨ (((p3 → ((((p2 ∨ p4) ∨ False) → True) ∨ True)) → p1) ∨ ((p3 ∨ p1) ∨ (p1 ∨ (True ∧ ((p1 → p3) → (p3 ∨ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699762367862221510742999806395 : (((((((False → p1) ∨ (p3 ∧ (p4 ∧ p2))) ∨ p3) ∨ (p4 → p4)) → ((p2 ∧ ((False ∨ p1) ∨ (True ∨ p5))) ∨ ((p1 ∧ p5) → p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614215877615511163509400068416 : ((((((p4 ∨ ((p5 → (p4 → False)) → ((((p5 → (p5 ∨ p2)) ∧ True) → p3) ∧ (p1 ∨ p1)))) → True) → ((True ∧ p3) → p3)) ∨ False) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157939068482181339842042234385 : ((((p2 ∧ p1) ∧ (p3 → ((p2 ∨ p4) ∧ p2))) ∧ (p5 → ((((p3 ∨ p1) → False) → p3) → p1))) ∨ (((False ∧ p4) ∧ (False → p2)) → p4)) := by
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
theorem thm_5_vars_66087251351974675527394254033 : ((p5 ∨ ((((((False ∨ p4) ∨ False) → p5) → (p1 → ((((p1 ∨ p2) → False) → (p4 ∧ ((False → p4) ∧ p5))) ∧ False))) ∧ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60651526377211398803798128925 : ((True ∧ ((((((True ∧ p1) ∧ False) ∧ (p1 → p5)) ∨ ((p4 ∨ p2) ∧ p4)) ∧ ((True → p3) ∧ p2)) ∧ (((p2 ∨ p4) → p3) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192812270493388744789268236267 : (((p1 → ((True ∨ ((p5 → p5) ∨ p5)) ∨ p2)) → False) → ((p3 ∨ False) ∧ ((p5 ∧ ((p1 ∨ (p1 ∧ (False → (p4 → True)))) ∧ True)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((True ∨ ((p5 → p5) ∨ p5)) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p1 → ((True ∨ ((p5 → p5) ∨ p5)) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787688303563851197022316177621 : (((p4 ∨ (p4 ∨ (p3 ∨ ((False → (((p1 ∨ p3) ∨ ((p2 ∨ (False → True)) ∧ p2)) → (p1 ∨ True))) → (p5 → (True → (p5 ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138578443558917692415055455351 : ((((((p5 ∨ ((p3 ∨ p2) ∧ (p3 → p4))) ∨ False) ∨ ((((p5 ∨ True) → (False ∨ False)) → p5) ∨ p2)) → p2) ∧ p2) → (p4 ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187858095440103850316267651815 : ((p5 → (p1 ∨ ((p1 → ((False → p3) ∨ False)) ∧ (p2 ∨ p2)))) → (((((p3 ∧ p1) ∨ (p5 ∨ p5)) ∧ p2) ∧ p5) ∨ (True ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172920569996590160390151881552 : ((p2 ∧ (p3 ∨ (p2 ∨ (((False → (p1 → p2)) ∨ p1) → ((p4 ∨ p5) ∨ p2))))) ∨ ((p3 → True) ∨ (((p2 ∨ p5) ∨ (p4 ∧ True)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55656421232839212051827478120 : ((((p3 ∧ (False ∧ p5)) ∧ False) ∧ (p5 → ((True ∨ (True ∨ p3)) → ((False ∨ ((((True ∨ (p3 ∨ False)) ∧ False) ∧ p3) ∨ p5)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694582482673664927285509967009 : ((((p3 ∧ ((p2 → ((p4 ∧ p5) ∨ False)) ∧ (((p4 ∨ True) ∧ p2) ∧ False))) ∨ (p1 ∨ ((((p1 ∨ p5) ∧ p2) → p4) ∧ (p1 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633262184952114398556868378022 : (((((p4 → ((p5 → p3) ∨ ((p5 ∨ (p2 ∧ p2)) → ((p1 → (p4 ∧ (p4 → (p3 ∨ p3)))) ∧ (p5 ∧ p4))))) ∧ (p2 ∧ p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48635731796935350967518516474 : ((((((p2 ∨ (((((p3 ∨ True) ∨ False) ∧ p1) ∨ (p4 → p1)) ∧ p3)) ∨ False) ∧ p5) → ((p4 ∨ p1) ∨ True)) ∧ (p1 → (p3 → p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
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
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207469211207199246084712073372 : (((False → (p3 ∧ (p5 ∧ p3))) ∨ p1) → ((p4 → ((True → (p2 ∨ p5)) → (False → (True ∨ ((p2 → (True → p2)) ∨ p2))))) → (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_337606204868174962039514211850 : (p1 → ((p2 → ((p2 → ((True ∧ (True ∧ ((p1 → (False → p5)) → (False ∧ True)))) ∧ True)) → (p2 ∨ p5))) → ((p5 ∨ p5) ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115373742827263516693694986404 : (((((p1 → (p2 ∧ p4)) ∧ p2) ∨ (p1 ∨ p4)) ∧ (((((p1 ∨ p3) → p3) ∨ p4) ∨ p5) ∧ (((p5 → p3) ∨ p4) → p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60799250633392392744910383768 : ((True ∧ (p1 ∧ ((p5 ∨ ((((p4 ∧ p4) → (False ∨ ((p4 ∨ (p4 → (p2 ∧ True))) ∨ (False ∧ (p1 ∨ p4))))) → p5) ∧ p2)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147484280414112150471696548372 : (((p4 ∧ (((((False ∧ ((p3 → (p1 ∨ (p3 ∨ p5))) ∨ (True → p2))) ∨ p3) → p3) → p4) ∨ p3)) ∨ True) ∨ (((False → p1) ∨ p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201030832353176377893448591021 : ((p4 ∨ ((False → ((p4 ∧ p3) ∧ p3)) → p1)) → ((p1 → p1) ∧ (((p3 → (((p5 ∨ (p4 ∨ True)) → p2) → (p3 → p2))) ∨ p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p5 ∨ (p4 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : (p5 ∨ (p4 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340050308532812443080642686314 : (p1 → (p2 → (((True ∨ p4) → ((((p4 ∧ p1) ∧ True) ∧ (p5 → p3)) → False)) ∨ ((p3 ∧ p5) ∨ ((p1 ∧ (False ∨ (p5 ∧ True))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41528618089472058816501203960 : ((((True → (False → (((p5 ∨ p4) ∨ (p4 ∧ p2)) → p5))) ∧ ((False ∧ ((False ∨ (False ∨ (True → p4))) ∨ p2)) ∧ (p3 ∧ p3))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45777747381642956089641329399 : (((p1 → ((((p3 ∨ p3) ∧ ((((((True ∨ p5) → (False ∨ p1)) → p5) ∨ p4) ∧ p2) ∧ p3)) ∧ ((p2 ∨ p1) → p5)) ∧ True)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352116691854919731772401241338 : (p4 → ((p3 ∧ (p2 ∧ (p3 ∨ (p5 ∧ p1)))) ∨ ((p2 ∨ ((p4 ∧ p1) ∨ (p3 → ((p3 ∨ p4) ∧ False)))) → (p4 ∨ ((p3 → False) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64089331006688882321055743413 : ((False ∨ (((p1 ∨ p4) ∨ ((((p5 ∨ False) → p4) ∧ (p2 ∨ p5)) ∨ p2)) ∨ ((((False → p5) ∨ ((p5 ∨ p1) ∧ p2)) → p3) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_958332537876965611573895092117 : ((((p3 → (p4 → True)) → (((False ∧ p5) ∨ ((p5 ∨ (p1 ∧ ((p1 ∧ (p2 ∨ (p5 ∧ p5))) ∨ (True → (p5 ∨ p3))))) ∧ p4)) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p4 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325793328463104449890515105072 : (p5 ∨ (p3 ∨ ((((p2 ∧ ((p2 ∨ p5) ∧ (False → ((p1 → (((p3 ∧ p2) ∨ p4) ∧ p4)) ∨ (True → p4))))) → (p1 ∨ p3)) ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42315267972020540845565650769 : (((p2 ∧ ((False ∧ p4) ∨ ((p4 → (((False → (((p3 → p2) ∧ (p1 ∨ p1)) → (p4 ∧ p5))) ∨ (True ∧ False)) → p3)) ∨ p3))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253906891897979544172618562986 : ((p1 ∧ p4) → ((((p3 ∧ p4) ∧ ((True ∨ p4) → False)) ∧ (((((True ∨ p3) ∧ ((False ∧ p4) → True)) → (p2 ∧ p3)) ∧ False) ∧ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261141174876718055868881388956 : ((p4 → p4) → ((p2 ∨ (True → (p2 ∧ (p4 ∨ ((((((p2 ∨ p4) ∨ p1) ∨ p2) → p2) ∨ ((False ∨ (p2 ∧ p3)) ∨ p4)) ∨ False))))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53333962517877658800986524855 : (((((((((False ∧ p2) ∧ p3) → p3) ∨ p1) → p2) → True) ∧ p4) → (((p4 ∧ p5) → (p4 → (True ∧ ((p1 → p3) → True)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609755033972769071469305676950 : (((((p4 ∨ ((((p5 → True) ∧ (p1 → p4)) ∧ False) ∨ (((p3 → p3) ∨ False) → (False ∧ (((p4 ∨ p3) ∧ True) ∨ p3))))) ∨ True) ∨ p1) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_113236890248962614468105976288 : ((((p5 ∧ (p4 → (((((True ∨ ((p2 ∧ False) ∨ p4)) ∨ p3) ∨ (True ∧ p3)) ∧ (p3 ∨ True)) ∧ p1))) → p2) ∧ (p2 ∧ p3)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150700016989433912285678898322 : ((((((((p5 ∨ p3) ∧ ((p5 ∧ p3) ∧ (p5 → (True ∧ False)))) ∨ (p5 ∧ p3)) ∨ p5) ∧ p5) ∧ p4) ∨ p3) → (p1 ∨ ((True ∧ p5) → p5))) := by
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
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h16 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h17 := h13 h16
          -- We need to get the right conjuct of h17 based on <expert-advice>.
          let h18 := h17.right
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h10.left
          let h21 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h20.left
          let h23 := h20.right
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h24 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h25 := h21 h24
          -- We need to get the right conjuct of h25 based on <expert-advice>.
          let h26 := h25.right
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h34
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- One of the premise coincides with the conclusion.
      exact h36
  case inr h37 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h38
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- One of the premise coincides with the conclusion.
    exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175283300320341409549119325881 : ((p3 ∨ ((((p2 ∧ p1) → (p3 ∧ (((p3 → p4) ∨ p5) ∨ p1))) ∨ p4) → p3)) → (((p2 ∧ (p3 ∨ (p1 → p5))) ∨ p2) ∨ (True → True))) := by
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
theorem thm_5_vars_149225165105415907625030470879 : (((p3 ∧ p3) ∨ ((False → (((False ∨ True) ∨ (p5 ∧ p1)) ∨ ((True ∧ p1) ∨ True))) → ((p5 ∧ p1) ∧ p3))) ∨ ((True ∨ p3) ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37789974090714592668263745900 : (((((p4 ∧ p1) → (p1 ∨ ((((p3 → (((p3 ∨ False) ∨ p1) ∧ p3)) ∨ ((True → (p4 ∧ False)) → p3)) → p5) ∨ p1))) → p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305420741712605877632910077358 : (p1 ∨ ((p5 ∨ (((p3 ∨ (p5 ∨ (p4 ∧ ((False ∧ p5) ∧ p1)))) ∧ True) ∨ (p2 → p4))) ∨ (p2 ∨ ((True ∨ ((p4 ∨ True) ∧ p4)) ∨ True)))) := by
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
theorem thm_5_vars_232270672547604276476875651848 : (((p2 → p2) → False) → ((((True ∨ (((p4 → p5) → p2) ∨ p3)) ∧ True) ∧ p5) → (False ∧ ((p3 → (((False ∧ p2) ∧ True) ∧ False)) ∨ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : (p2 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h13
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : (p2 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h17
      -- False on the left can always be used.
      apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h2.left
  let h21 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349407949687305871956451705054 : (p3 → (p4 → ((True → (((False ∨ p4) → False) ∨ ((p2 ∧ p4) ∧ (False ∧ ((False ∨ (((p1 ∧ p3) ∨ p5) ∧ p5)) ∧ True))))) ∨ (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_400202267524374608008225367907 : ((((p5 → ((((p3 → ((((p3 → p2) ∧ ((p1 ∨ True) ∧ p4)) ∧ (False ∧ p1)) ∧ p4)) ∧ p3) → (True → (True ∧ True))) → p4)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_194091879574968128119127296541 : ((True → (True → ((p3 ∧ (p4 → (True ∨ p3))) ∧ p5))) → ((False ∧ p2) ∨ (p2 → (True ∧ ((p1 ∨ (((p2 → False) ∧ True) ∧ p3)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671207170420276564237796123687 : ((((p3 ∨ ((True → True) ∧ (p3 → (((True ∨ (p4 ∧ ((p1 → False) ∧ p2))) ∧ (p2 → (p4 → p5))) → p4)))) ∨ ((p4 → p2) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_137618656358881279540787329929 : ((False ∨ ((((p4 → ((p1 ∨ p2) ∧ (((p3 → p2) → p3) → p1))) ∨ (p1 → p3)) → ((True → p1) ∨ True)) ∨ p1)) ∨ ((p1 → p5) → False)) := by
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
theorem thm_5_vars_355696503908365029254148954025 : (p5 → (((p4 ∧ ((p5 ∧ (p1 ∨ (p2 → (p1 → (p4 ∧ p4))))) → (p4 → False))) ∧ ((p3 ∨ ((True ∧ p3) ∧ p1)) → p3)) → (False ∧ p4))) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∧ (p1 ∨ (p2 → (p1 → (p4 ∧ p4))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h7
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727492810716360737112628593820 : ((((p4 ∧ (True ∧ p4)) ∨ ((((p3 ∨ p5) → ((p5 → (p2 ∨ p1)) → (p4 ∨ (p5 ∨ ((p2 ∨ (p3 ∧ p2)) ∨ True))))) ∧ p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691898936639131393345384580285 : ((((p1 → (p3 → ((p2 ∧ ((False ∧ (p2 → (p5 ∧ p3))) → True)) ∧ (False ∧ False)))) → (p2 ∨ (False → ((True ∨ (p1 → p2)) ∨ p2)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40254171511548380743016831154 : ((((p1 ∨ (((p4 → (p4 → ((p5 ∧ p1) → ((p5 ∨ (p2 ∨ p4)) → (p3 ∨ (p3 ∨ p5)))))) ∧ p5) ∧ (p1 ∨ p3))) ∧ p5) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135988322383641690811182047427 : (((((p5 → p1) ∨ (p1 → p2)) ∨ (p4 ∧ (p4 ∨ p5))) ∨ ((p5 ∧ (p1 → p3)) → ((False → p1) ∧ (p2 ∨ p3)))) ∨ ((p1 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258936909619637917778207957086 : ((True → p2) → (p3 → ((p3 ∨ p3) ∧ (p4 ∨ (((p1 ∨ (((p5 → (False → ((p3 → p2) ∧ p4))) → (p1 ∨ p4)) ∨ p4)) ∧ p1) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172343854882280833792794600729 : (((p2 ∨ ((p1 ∨ p3) ∧ (False → False))) ∧ (p4 ∨ ((p5 ∧ False) ∨ (p5 → p5)))) ∨ ((p5 ∨ p4) ∨ ((p4 ∨ False) → ((True ∧ False) → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55486206084930639733612982898 : ((((p3 → (True ∧ True)) ∨ (p2 → p1)) → ((False ∧ ((p5 → ((True ∨ (p3 → p2)) → False)) ∧ ((p3 ∨ p4) → (False → p5)))) ∨ True)) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191592382425885281955788526356 : ((p2 ∧ (p5 ∨ (p4 ∧ (((p5 ∨ p2) → p3) ∨ p2)))) ∨ (((p4 ∨ (((p2 ∧ (p1 → True)) → False) → p1)) ∨ (p4 ∨ (False ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61384474583766404985059162864 : ((p1 ∧ ((((((p1 → (p3 → (False ∧ (False ∨ p1)))) ∨ True) → (True → (p4 ∧ p2))) ∧ (p4 → p5)) ∨ ((p1 → p5) → p5)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347319529440928934900397425279 : (p3 → (((True ∨ False) ∧ (((p5 → False) ∧ p4) ∨ (p1 ∧ p1))) → ((((p3 ∨ p1) → (p5 ∨ (p2 ∧ (p2 → False)))) ∨ True) ∧ (True ∨ p2)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338283262244849814467224781457 : (p1 → ((p1 ∧ (((False ∨ False) → p5) ∧ p3)) → (((p5 → False) ∧ (False ∨ (p5 → p2))) ∨ (p5 → (p3 ∨ (p4 ∨ (True ∨ (True ∨ p3)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62317638272518303138838942267 : ((p3 ∧ ((False ∧ ((True ∨ (p4 ∨ (((p5 ∨ (False → True)) → p4) ∧ ((p3 ∧ p4) → p2)))) ∧ ((p3 ∧ p5) ∧ p4))) ∨ (True ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263704235000844627560860900634 : (True ∧ ((False ∧ (((p2 ∨ p5) ∧ ((((p2 ∨ p5) → p2) ∨ p5) ∧ ((False → p2) → False))) ∧ True)) ∨ ((p5 ∨ p4) ∨ (p1 → (p1 ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241818691451794520474260127236 : ((p1 → p1) ∧ ((((p1 → (((False → True) → p1) ∧ ((True → (p5 ∧ p5)) → (p3 ∧ (((p1 ∧ p3) ∧ False) ∧ p4))))) ∧ False) ∧ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610782244611662305892773970508 : ((((((((p4 ∨ p4) ∧ ((((p1 ∧ p1) ∧ p4) ∧ p4) ∨ p1)) ∨ ((True → p4) → p4)) ∨ ((p1 → p5) ∨ (p3 ∨ p1))) → p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190267912574160215167871692381 : (((((p5 ∧ (p2 ∨ True)) ∧ (p4 ∧ p2)) ∨ p2) ∨ True) ∨ (p5 → ((((((((True → p2) → False) ∧ p5) ∨ p3) ∨ True) ∨ p2) ∧ True) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124537931436728157590877091239 : (((p2 ∨ ((True ∨ (p5 ∨ p1)) ∧ p1)) ∧ ((((p4 ∧ ((True ∨ p5) ∨ p3)) ∨ p5) ∨ (p1 → p5)) ∧ ((p2 → p5) ∧ p2))) → (True → p5)) := by
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
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h7.left
            let h15 := h7.right
            -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
            have h16 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h15
            -- We have shown the premise of h14, we can now drive its conclusion.
            let h17 := h14 h16
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h7.left
            let h20 := h7.right
            -- One of the premise coincides with the conclusion.
            exact h18
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h7.left
          let h23 := h7.right
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h24 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h25 := h22 h24
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h7.left
        let h28 := h7.right
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h7.left
      let h31 := h7.right
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h32 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h33 := h30 h32
      -- One of the premise coincides with the conclusion.
      exact h33
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h4.left
      let h39 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- Disjunctions on the left can always be decomposed.
            cases h44
            case inl h45 =>
              -- Conjunctions on the left can always be decomposed.
              let h46 := h39.left
              let h47 := h39.right
              -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
              have h48 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h47
              -- We have shown the premise of h46, we can now drive its conclusion.
              let h49 := h46 h48
              -- One of the premise coincides with the conclusion.
              exact h49
            case inr h50 =>
              -- Conjunctions on the left can always be decomposed.
              let h51 := h39.left
              let h52 := h39.right
              -- One of the premise coincides with the conclusion.
              exact h50
          case inr h53 =>
            -- Conjunctions on the left can always be decomposed.
            let h54 := h39.left
            let h55 := h39.right
            -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
            have h56 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h55
            -- We have shown the premise of h54, we can now drive its conclusion.
            let h57 := h54 h56
            -- One of the premise coincides with the conclusion.
            exact h57
        case inr h58 =>
          -- Conjunctions on the left can always be decomposed.
          let h59 := h39.left
          let h60 := h39.right
          -- One of the premise coincides with the conclusion.
          exact h58
      case inr h61 =>
        -- Conjunctions on the left can always be decomposed.
        let h62 := h39.left
        let h63 := h39.right
        -- We want to use the implication h62 based on <expert-advice>. So we show its premise.
        have h64 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h63
        -- We have shown the premise of h62, we can now drive its conclusion.
        let h65 := h62 h64
        -- One of the premise coincides with the conclusion.
        exact h65
    case inr h66 =>
      -- Disjunctions on the left can always be decomposed.
      cases h66
      case inl h67 =>
        -- Conjunctions on the left can always be decomposed.
        let h68 := h4.left
        let h69 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h68
        case inl h70 =>
          -- Disjunctions on the left can always be decomposed.
          cases h70
          case inl h71 =>
            -- Conjunctions on the left can always be decomposed.
            let h72 := h71.left
            let h73 := h71.right
            -- Disjunctions on the left can always be decomposed.
            cases h73
            case inl h74 =>
              -- Disjunctions on the left can always be decomposed.
              cases h74
              case inl h75 =>
                -- Conjunctions on the left can always be decomposed.
                let h76 := h69.left
                let h77 := h69.right
                -- One of the premise coincides with the conclusion.
                exact h67
              case inr h78 =>
                -- Conjunctions on the left can always be decomposed.
                let h79 := h69.left
                let h80 := h69.right
                -- One of the premise coincides with the conclusion.
                exact h78
            case inr h81 =>
              -- Conjunctions on the left can always be decomposed.
              let h82 := h69.left
              let h83 := h69.right
              -- One of the premise coincides with the conclusion.
              exact h67
          case inr h84 =>
            -- Conjunctions on the left can always be decomposed.
            let h85 := h69.left
            let h86 := h69.right
            -- One of the premise coincides with the conclusion.
            exact h84
        case inr h87 =>
          -- Conjunctions on the left can always be decomposed.
          let h88 := h69.left
          let h89 := h69.right
          -- One of the premise coincides with the conclusion.
          exact h67
      case inr h90 =>
        -- Conjunctions on the left can always be decomposed.
        let h91 := h4.left
        let h92 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h91
        case inl h93 =>
          -- Disjunctions on the left can always be decomposed.
          cases h93
          case inl h94 =>
            -- Conjunctions on the left can always be decomposed.
            let h95 := h94.left
            let h96 := h94.right
            -- Disjunctions on the left can always be decomposed.
            cases h96
            case inl h97 =>
              -- Disjunctions on the left can always be decomposed.
              cases h97
              case inl h98 =>
                -- Conjunctions on the left can always be decomposed.
                let h99 := h92.left
                let h100 := h92.right
                -- We want to use the implication h99 based on <expert-advice>. So we show its premise.
                have h101 : p2 := by
                  -- One of the premise coincides with the conclusion.
                  exact h100
                -- We have shown the premise of h99, we can now drive its conclusion.
                let h102 := h99 h101
                -- One of the premise coincides with the conclusion.
                exact h102
              case inr h103 =>
                -- Conjunctions on the left can always be decomposed.
                let h104 := h92.left
                let h105 := h92.right
                -- One of the premise coincides with the conclusion.
                exact h103
            case inr h106 =>
              -- Conjunctions on the left can always be decomposed.
              let h107 := h92.left
              let h108 := h92.right
              -- We want to use the implication h107 based on <expert-advice>. So we show its premise.
              have h109 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h108
              -- We have shown the premise of h107, we can now drive its conclusion.
              let h110 := h107 h109
              -- One of the premise coincides with the conclusion.
              exact h110
          case inr h111 =>
            -- Conjunctions on the left can always be decomposed.
            let h112 := h92.left
            let h113 := h92.right
            -- One of the premise coincides with the conclusion.
            exact h111
        case inr h114 =>
          -- Conjunctions on the left can always be decomposed.
          let h115 := h92.left
          let h116 := h92.right
          -- We want to use the implication h115 based on <expert-advice>. So we show its premise.
          have h117 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h116
          -- We have shown the premise of h115, we can now drive its conclusion.
          let h118 := h115 h117
          -- One of the premise coincides with the conclusion.
          exact h118



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27203762309751641895366505973 : (((p3 → p4) ∨ (((False ∧ p4) ∨ ((p1 → (p1 → ((p1 → p2) → ((False ∨ (p3 ∧ True)) ∧ p5)))) ∨ (p3 → True))) ∧ (False → False))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_844689834970296083278107388679 : (((((True → (False ∧ (p4 ∧ p4))) ∧ (((p2 ∧ ((p1 ∨ ((True ∧ False) ∧ p3)) ∨ p5)) → (False ∧ (p5 ∧ p1))) ∧ (False ∨ p4))) ∨ p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593457880684825329105687791722 : (((((((p5 ∨ False) → ((True ∨ (p3 ∨ p1)) ∧ p5)) → (p2 → ((p5 → p2) ∨ (p4 → (p2 ∨ p5))))) → ((p5 ∨ p2) ∧ p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88112711403500643378788145320 : ((((p3 ∨ (p3 ∨ p3)) → False) ∧ ((((p4 → True) → p5) ∧ (((False → p4) → (p1 ∨ True)) ∧ p5)) ∧ (p3 ∧ ((p5 → p1) ∧ p5)))) → p2) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h14 : (p3 ∨ (p3 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115103989280970608832292605275 : ((((((p4 ∨ (p3 ∨ p4)) → ((p3 ∧ p1) ∧ p2)) ∨ p2) ∨ p4) → (((p2 ∧ ((p1 ∧ p1) → p4)) ∧ p5) ∨ (p2 → p1))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258840950730702109371398414638 : ((True → p1) → (((p4 ∨ ((p4 → p1) → (p5 → (((p4 ∨ ((p3 ∧ (p3 ∨ True)) ∨ p1)) ∨ False) ∨ p4)))) → False) → (p2 → (p5 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ ((p4 → p1) → (p5 → (((p4 ∨ ((p3 ∧ (p3 ∨ True)) ∨ p1)) ∨ False) ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : (p4 ∨ ((p4 → p1) → (p5 → (((p4 ∨ ((p3 ∧ (p3 ∨ True)) ∨ p1)) ∨ False) ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h10
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194266159082203157761778057567 : ((p5 → (((p3 ∨ ((p3 ∧ p5) → p1)) → True) → True)) → (((p1 ∧ ((((p5 → p4) ∨ True) ∧ p3) → (p1 ∧ (p4 → p5)))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137249599490120376425746068067 : ((p1 ∧ (((p2 → p4) ∨ ((p2 ∨ p3) ∧ p1)) → (p4 ∧ ((p1 ∧ True) ∧ ((p2 → (p4 ∨ True)) → (p3 ∨ True)))))) ∨ (p4 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116710846357014566783960417173 : (((p1 ∧ p4) ∨ (((p1 → (True ∧ (p3 ∨ p5))) → ((p3 → (p3 ∧ p1)) ∧ (False → ((True → True) ∧ p3)))) ∨ (p1 ∧ p4))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61230354621946222048788487287 : ((False ∧ (p2 ∧ (((False → (False → p4)) ∧ (((p4 → p4) ∧ ((p4 → ((False ∧ True) → False)) ∨ ((p3 → False) ∨ p4))) → p4)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150286791425395547896991190061 : ((p4 → ((True ∧ (p4 ∧ (((((((False ∨ True) → p5) ∨ p2) ∨ p2) ∨ False) ∧ p2) ∨ (p5 ∧ p5)))) ∨ p2)) ∨ (p1 → (True ∨ (p2 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355925623276595073941982177427 : (p5 → (((p3 ∨ ((False → p4) ∨ (((p2 ∨ (p4 ∧ p2)) ∧ False) ∧ p4))) → ((True ∨ (True → True)) ∧ (p4 ∨ p5))) → ((p5 → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65683655571989580240438731576 : ((p4 ∨ ((((False ∧ False) → p4) ∧ ((True → ((((p5 ∨ p1) ∧ p5) → (False ∨ p1)) ∧ (True → False))) ∨ ((p3 ∧ True) → True))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44903077852434134650587117365 : ((((p1 ∨ (False ∨ True)) → ((True ∨ (((((p3 ∧ ((p2 ∨ p3) ∧ p3)) ∧ ((p1 ∨ p5) ∧ p3)) ∨ p1) ∧ p4) ∨ p2)) → p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198458150462798249670745308102 : ((p5 ∧ ((p4 ∧ p2) ∧ ((p2 ∨ p5) ∧ p2))) ∨ ((p2 ∨ p1) → ((True ∨ (((p1 → p4) ∨ p1) ∧ (False → (p3 ∧ (p1 → True))))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175374247219261838395419472120 : ((True → ((((True ∧ p2) → (False ∨ p5)) ∧ ((True → p2) ∨ (p3 → p4))) → p3)) → (((p5 → ((True ∧ (p5 ∧ p4)) ∨ p1)) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610487121913143778738437994418 : ((((((p2 ∨ ((((((p2 → True) → (p2 ∨ p1)) → p5) ∧ p2) ∧ (p4 ∨ False)) ∨ (((False ∨ p2) → p4) ∨ p2))) → p4) → p3) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136704236733342738229144443621 : (((p1 ∧ p2) ∧ (p3 ∧ ((True ∧ False) → (((p2 → ((p5 ∨ (p4 ∨ False)) ∨ (p1 → False))) ∨ p4) ∧ (p1 ∨ False))))) ∨ ((False ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781049094788119500815843017360 : (((p2 ∨ ((p5 ∨ p4) ∧ (((p4 ∧ (((((p1 ∨ p1) ∨ (((p5 ∧ p5) ∨ False) → (False ∧ False))) ∧ False) ∨ p2) ∧ True)) ∧ p2) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64992982881003624362266271823 : ((p2 ∨ (((False ∨ p1) ∧ p5) ∨ (p5 → ((((p4 ∧ p5) ∨ ((p3 ∨ (p4 ∧ p4)) ∨ p3)) ∨ p2) → (((False ∨ p4) → p4) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590367498829620250626410821375 : ((((((p4 ∧ (p2 ∧ p2)) → (((p5 ∧ (p5 ∧ p3)) → (((True ∧ ((p4 ∧ p3) → (p2 ∨ True))) ∨ p2) ∧ p2)) → p2)) → p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179144915873745607167283363797 : ((p1 ∧ (p3 → (p4 → (p5 ∨ (p1 ∧ ((p1 → (False → p1)) ∨ p1)))))) ∨ ((p2 → ((((False ∨ p5) ∧ p3) ∧ p5) ∨ (p3 ∨ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45448584740536165271807007396 : (((True ∨ ((p3 ∧ True) ∨ (((True ∨ (((p2 ∧ p4) → p2) ∧ (False ∨ True))) ∨ p4) ∧ ((((p2 ∨ True) ∧ False) ∧ True) → False)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302757728160367705578616391280 : (False ∨ (p4 ∨ ((((False → (p3 ∨ p4)) → False) ∧ (p3 ∧ ((False ∨ (p4 → (False → (p4 ∧ p1)))) ∨ False))) ∨ ((p2 → p2) ∨ (p2 ∧ p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2324085154919721061661743774 : ((p1 ∨ ((p2 → (True ∧ ((p5 → p5) → (p3 → (p5 ∨ False))))) ∧ p3)) → ((((p1 → (p1 ∨ p4)) → p1) ∨ p3) ∨ (True ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593487196873312112070184782073 : ((((((True ∧ (p1 → p5)) ∨ (((p3 → ((p4 ∧ (True ∨ p5)) → p4)) ∧ (p5 ∨ (False ∧ p3))) ∧ p4)) → (p4 ∨ (False ∧ p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782449067297235784063761057005 : (((p3 ∨ (((p5 ∧ (p1 → ((p1 → (p5 ∧ (((p2 ∧ True) ∧ p4) → True))) ∨ (p2 ∨ p3)))) ∨ (p5 → (p4 → (True ∧ p4)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



