variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194278930991290249206473965931 : ((p5 → ((p5 ∨ p4) → ((p1 ∨ (p4 ∨ p1)) ∨ p5))) → ((False → (False ∨ ((p2 ∨ p2) ∧ ((p3 → p2) ∧ False)))) → ((True → False) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802752097203201087678285781714 : (((p2 → (p2 → ((p2 → ((p5 ∨ False) → True)) ∧ (((p3 ∨ p3) ∧ ((p3 ∨ p5) → (False → p2))) → (((p3 ∨ p1) → False) ∨ True))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810944856123658328496766417243 : (((p5 → ((p1 ∨ p1) → (((p3 ∨ ((((p5 → p5) ∨ p2) ∨ False) → p3)) ∨ (True ∨ p3)) ∨ ((False ∧ p5) ∧ (p5 → (p3 ∧ p1)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191013511925368811632904174721 : (((p4 ∨ ((p3 ∨ p2) ∧ p5)) ∨ ((p4 → p3) ∨ p1)) ∨ ((p3 → p3) → ((((False ∨ p5) → (p2 ∧ p3)) ∧ (p2 → (p2 ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714106435014622271013665792988 : ((((((p5 ∨ p3) → (True → p4)) → p2) → ((p5 ∧ True) ∧ (p2 → ((((True ∨ True) → (p2 ∨ False)) ∨ (True ∨ True)) ∧ (False ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135567477800983656466201972718 : (((p3 → (((p4 ∧ p1) ∨ ((p1 → (p1 ∧ False)) ∨ (p1 → True))) → (p5 → p3))) ∧ (p4 ∨ ((p4 ∧ p1) ∧ p5))) ∨ ((p5 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635007677565718988430199885620 : (((((((p4 → ((True ∨ False) ∧ p1)) ∨ (((((p5 ∨ p5) ∨ p1) → p5) → (p3 → p4)) ∨ p3)) ∨ p5) → ((True ∨ p5) ∨ p4)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164595133747442893710379132428 : ((((p1 ∧ p4) → (((False ∧ p4) ∧ (p3 → ((True → (p2 → p3)) → False))) ∨ p1)) ∧ p1) ∨ ((((False ∨ p4) ∧ False) ∨ p4) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619311867074225204354796501110 : ((((((p3 ∨ False) ∨ False) → (((((p2 ∨ p5) ∧ (p1 ∧ ((p2 ∨ p5) → p5))) → (p4 ∨ (p5 → True))) ∧ p4) ∨ (p2 ∨ p2))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312655119652574559464619792798 : (p3 ∨ ((((False ∨ ((p5 ∨ p4) → (p5 ∨ (((p3 → (((p1 ∧ False) ∨ p1) ∧ p4)) ∧ p1) ∨ (p5 ∨ p3))))) ∧ p5) ∨ (True → True)) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198743357312746279979352664370 : ((True → (((True ∧ (p4 ∧ p3)) ∨ False) ∨ p5)) ∨ ((True ∧ (((((True ∧ (p5 ∨ True)) ∧ (p5 → p4)) ∨ p1) ∨ (p2 → p2)) ∨ p3)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166260579842301158258872034988 : ((p3 ∧ (((p3 ∨ p4) ∧ (p3 ∨ p3)) ∧ (((p4 → p1) → (p1 → (p4 ∧ p4))) ∧ p1))) ∨ (((p4 → False) → False) → ((False ∧ p5) → p3))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606919681222358747755597321201 : (((((((False ∧ ((False → (((False ∧ True) ∧ True) ∧ False)) ∧ ((p3 ∨ False) ∨ p4))) ∨ p1) ∨ ((True ∨ (True ∧ p3)) ∧ False)) ∧ True) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185743986167648252634192922761 : ((p3 → ((True ∧ p4) ∨ (((p4 ∨ (p5 ∨ p2)) → p3) → p4))) ∨ (((p3 → p2) ∨ (p2 → (p2 ∨ p2))) ∨ (False ∧ (p1 ∧ (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49197397457996947261551628159 : (((((True ∧ p4) ∨ p2) ∨ ((((False → p1) ∨ False) ∨ p5) → ((((p2 ∨ (p4 → p2)) ∧ p1) → p5) ∨ True))) ∨ (p5 ∧ (p3 ∧ False))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55454626109210385447128822234 : ((((False ∨ ((p5 ∨ p2) ∨ True)) → p2) → ((p2 ∧ (p4 ∧ (p3 ∨ ((p3 → p1) ∧ (True → False))))) ∨ (p2 ∧ ((p5 ∧ True) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p5 ∨ p2) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191787296849958749158674039313 : ((p1 ∨ (True → (((p3 → (p5 ∧ p4)) → p2) ∧ p3))) ∨ (((p2 → True) ∨ ((((p1 ∧ p1) ∧ p4) ∧ p5) ∧ p5)) ∨ (p2 → (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47136312803817423649208560832 : (((((((False → p1) → p2) → (((p3 ∨ (p3 ∨ False)) ∨ (True → p5)) ∨ p2)) → p3) ∧ ((True ∧ (p5 ∧ p1)) ∧ True)) ∨ (p5 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246023065708087297229844794312 : ((p4 ∧ False) ∨ ((p4 ∧ (p3 ∧ (((((((p1 ∧ (p5 ∨ p2)) ∨ ((p2 ∧ p1) ∧ False)) → p2) → False) → p2) → False) ∨ p2))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480841855013376229382526985587 : ((((((p5 ∧ (p4 → p3)) ∨ p2) → (p5 → p4)) ∨ (p4 → (((((p4 ∨ False) → (p2 → (p5 → p5))) ∨ False) ∧ p1) ∨ (p4 ∨ p1)))) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157474347742831865292587831017 : ((((p5 → ((p4 ∨ (p1 ∧ p1)) → (p4 ∨ (((p3 ∧ p3) ∨ p3) → False)))) → False) ∨ (p3 ∨ True)) ∨ (p3 ∨ ((p4 ∧ (p2 → False)) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350342913409153854194038043570 : (p4 → ((p3 → (((False ∨ ((p1 ∧ (((False ∨ p5) ∨ p4) ∧ (p3 ∨ ((p2 ∧ p2) → (p4 → p2))))) → (False ∨ p3))) ∧ p5) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810463446539585557768753720625 : (((p5 → ((((p1 ∧ p4) ∧ (p2 ∧ p5)) → True) ∧ ((p2 ∨ (p5 ∧ (((True ∨ p3) ∨ p3) → ((False ∨ p1) ∨ (False → p3))))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704037312125553324497180967372 : ((((((p5 → (p4 ∨ p4)) → ((p2 ∧ p5) ∧ p3)) → p2) → (((p2 ∧ p4) ∧ (((True → p4) ∨ (p5 ∨ True)) ∨ (p1 ∨ p1))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45446743930295695297235193303 : (((True ∨ ((p5 → (False ∨ p3)) ∨ ((p5 ∧ (p3 → ((p4 → (p1 ∨ p1)) → p2))) ∨ (False ∨ ((p4 → p3) → (p3 ∨ True)))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118829949182870593608293268633 : ((True → (((((p2 ∧ p1) → (p1 → (((p2 ∧ (p5 ∨ p4)) → p4) → ((p3 ∨ p5) ∧ True)))) → False) ∨ True) ∧ (p2 ∨ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643815445367075219279029019752 : ((((p5 ∧ (((p5 ∧ p5) ∧ p3) → (p3 → (((False ∧ (p5 ∨ ((p2 → ((p2 → False) ∧ False)) ∨ (p2 ∨ False)))) ∨ p4) ∨ p3)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84027834176173690287938392244 : (((((True ∧ p2) ∨ (p2 → (p2 ∨ ((False ∧ p3) ∧ (False ∧ (p1 ∨ p2)))))) → p3) ∧ ((((p2 ∨ p1) ∨ True) ∧ p1) ∨ (p1 → p4))) → p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : ((True ∧ p2) ∨ (p2 → (p2 ∨ ((False ∧ p3) ∧ (False ∧ (p1 ∨ p2)))))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h9
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : ((True ∧ p2) ∨ (p2 → (p2 ∨ ((False ∧ p3) ∧ (False ∧ (p1 ∨ p2)))))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h12
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : ((True ∧ p2) ∨ (p2 → (p2 ∨ ((False ∧ p3) ∧ (False ∧ (p1 ∨ p2)))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h16
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : ((True ∧ p2) ∨ (p2 → (p2 ∨ ((False ∧ p3) ∧ (False ∧ (p1 ∨ p2)))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h20
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358707843262884539110835420525 : (p5 → (p5 → (((p4 ∨ ((False → p5) ∨ (((((p2 ∧ (p3 ∨ p1)) ∧ p5) → (p5 → (p3 → p2))) ∨ p5) ∨ p2))) ∧ (True → False)) → False))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
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
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h17 := h5 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h19 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h20 := h5 h19
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h23 := h5 h22
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38981473226860846095160615036 : ((((p3 ∧ p4) ∧ (p5 → (p2 ∨ (((p1 → ((((p3 ∧ p1) ∧ p2) ∨ ((p1 ∧ p3) ∧ p4)) ∧ p3)) ∨ (p3 → p1)) → False)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192457429002849842834160874030 : ((((p5 ∧ (True ∨ (p4 ∨ p1))) ∧ (p5 ∧ p3)) ∨ True) → (((False → ((p4 ∨ p2) ∧ ((p1 ∨ p4) ∨ ((p3 ∨ p2) → True)))) → p3) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h4.left
        let h13 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h4.left
        let h16 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793558069197327550268267795575 : (((True → (p2 ∨ (p4 ∧ ((p5 → p1) ∨ ((((p5 ∨ False) ∨ (p5 ∨ p1)) → p2) ∧ ((p4 ∧ ((p3 → True) ∧ (False ∧ p3))) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_482306023083368606767383631970 : ((((((p5 ∧ (p3 ∨ p2)) ∨ p2) ∧ (p5 → p5)) → (((((False → False) → (p4 ∨ p3)) → p3) ∨ p2) ∨ ((False ∧ True) → (p2 → p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341671140397063226347553582776 : (p2 → (((((((p2 ∧ p3) ∨ True) → p4) ∨ ((p1 ∨ False) ∨ ((p4 ∧ (p2 → p4)) → (p3 ∧ p3)))) ∧ (p5 → p1)) ∨ p5) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245619815694627619925169195019 : ((p3 ∧ False) ∨ ((p3 ∨ False) ∨ ((True ∧ (p3 ∨ True)) ∨ (((p2 ∨ p5) ∧ p2) ∧ ((((p4 → (True ∧ True)) ∨ p4) ∧ (p4 → p1)) ∨ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38240873643112914628690149636 : ((((((((True ∨ p1) ∧ (((p1 → (p5 ∧ p3)) → (False ∨ p5)) → p5)) → False) ∧ True) → True) ∧ (p4 ∨ ((p3 → p1) ∧ p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262144302608116140165567407705 : (True ∧ (((((((p5 ∨ (p2 → (((True ∨ p3) ∨ p3) → p4))) ∧ p5) → ((((p2 ∧ p1) ∨ False) ∨ p4) ∧ p1)) → p1) → p1) ∨ True) ∨ p1)) := by
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
theorem thm_5_vars_42257542719834586293158636270 : (((p1 ∧ (((p1 ∨ (p1 ∧ (((False → (((p2 ∧ p3) ∨ p1) → p3)) ∧ True) ∨ ((p4 → p1) → (True → p4))))) ∨ p1) → False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353523231588159315129730981710 : (p4 → (p2 ∨ (p3 → ((True → ((p5 ∧ (True ∨ (p1 → p5))) → ((True ∧ True) → (p3 ∧ False)))) ∨ (p2 → ((p2 → (True → False)) → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251582458919191676755937153424 : ((p3 → False) ∨ (p2 ∨ (p5 → (((((p4 ∧ p4) → False) → p2) ∨ ((p2 ∧ (p5 ∨ (p1 ∧ (p5 ∨ False)))) → (p5 ∨ (p3 ∨ p1)))) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793091414574445923498499220542 : (((True → ((p1 ∨ p3) → ((p3 → (p1 → ((p5 ∧ (p3 ∧ p3)) → p2))) → (True ∧ (((p2 ∨ p2) → (p2 ∧ True)) ∧ (p2 ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343247862787319832249195728690 : (p2 → ((False → (p4 ∧ p2)) → ((((p5 → False) → False) ∨ (((p4 → p4) ∨ ((True ∧ p5) ∧ ((p1 ∨ p5) → p4))) ∨ p4)) ∨ (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680002560719294789435602429601 : (((((((p1 ∧ p2) ∧ p5) → (((p5 → (p3 ∧ False)) → ((True → p5) ∧ p5)) ∧ (p4 → False))) → p5) → (((p5 ∧ p3) → p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135552486642167399777910604900 : ((((p5 ∧ p5) → ((p4 ∧ p1) ∨ (p1 ∧ (p3 ∨ (p1 → ((False ∧ p2) → True)))))) ∧ (p3 ∧ ((p3 ∨ p1) ∨ True))) ∨ (p1 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38111250097334725960395343863 : (((((p2 ∧ ((((((((p1 ∨ (False → False)) → True) ∧ p4) → True) → p4) ∨ False) → p4) ∨ p4)) ∨ p1) ∧ (p1 → (p4 ∨ p4))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165544881073339699389234823153 : (((((p2 ∧ (p3 → p4)) ∨ p3) ∧ (p3 → True)) ∧ ((p2 ∨ (p1 → p3)) ∧ (p5 ∨ p2))) ∨ (p4 → ((p1 ∨ ((False ∧ p4) ∧ p3)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149292258866693904451321009387 : (((p4 → p3) ∨ (p4 → ((((p3 ∧ False) → p4) → (((p3 ∧ ((p1 ∨ p5) → p1)) ∨ False) ∧ False)) ∨ p4))) ∨ (p5 ∧ (p2 ∨ (True ∧ p5)))) := by
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
theorem thm_5_vars_166919573665378319468836244509 : ((((p5 ∨ (p1 → (p4 ∨ p2))) ∨ (((p5 → p3) ∧ p5) → (p3 ∨ (False → p1)))) ∧ p5) → (((False → (p5 ∧ True)) → (False ∧ True)) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (False → (p5 ∧ True)) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h7
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (False → (p5 ∧ True)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h17 : (False → (p5 ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h17
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754664690734877381880792112798 : (((False ∧ (p4 ∧ ((((p3 ∨ ((p3 ∨ p1) → (p1 ∨ p1))) ∨ False) ∨ False) ∨ (((p1 → p4) ∧ p3) ∧ (p3 ∨ ((False → True) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178776977615636885194823931006 : (((False ∨ (p4 ∨ p5)) ∧ (((p5 ∧ True) ∧ ((True → p4) → False)) ∧ p1)) ∨ (p4 ∨ ((False → (False ∧ (p1 ∨ ((False ∨ True) ∧ True)))) ∧ True))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212142020187440914722392915919 : ((True ∨ ((True ∧ p1) ∧ p1)) ∧ (((p3 ∨ (((p3 ∧ (p4 → ((p2 ∨ p1) ∨ p1))) ∧ (True ∨ ((p4 ∧ p3) ∧ True))) ∧ p2)) → p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40850937655254797603959311557 : ((((((False → (p3 ∧ ((True ∧ p5) → (p2 ∨ (((p2 ∧ p5) → p4) ∨ (p1 ∧ True)))))) → (p1 → False)) ∧ p3) ∧ (p2 → True)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208717765512863424769993216225 : ((p1 ∧ ((False ∧ (p5 ∧ False)) ∨ p1)) → ((((p2 → (p5 ∨ p2)) → (p2 → (p5 ∨ (False ∨ (p4 ∧ p3))))) ∨ p1) ∨ (p2 → (p5 → False)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19226269484871063418762008988 : (((False → ((((p5 ∨ p4) ∧ ((False ∨ (p2 → p5)) ∧ p5)) → p3) → ((p5 ∨ False) → p2))) → (((p4 → (p4 ∨ p2)) → p2) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134361590744399779024934007967 : (((p1 ∨ ((p5 → (((p1 → (p5 → ((p3 ∨ p4) → p2))) ∨ p1) ∨ (((False → p5) ∧ p3) ∧ False))) ∧ p1)) ∨ True) ∨ ((p1 → p1) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210154719340720811304035752560 : ((((p4 ∧ True) ∨ p4) ∨ True) ∧ ((p3 → True) ∧ (p1 ∨ (((p3 → p2) → (p5 → True)) ∧ (p5 ∨ (p5 ∨ ((p3 → p2) → (p5 → True)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66234783801515164808804128969 : ((p5 ∨ ((((True → ((True ∧ p2) ∧ False)) → p5) ∨ p2) → (p1 → ((p5 ∧ (((p5 → False) ∨ p1) ∧ True)) → ((p1 ∧ p5) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698519331540943203241405264089 : ((((((p3 ∧ False) ∧ (p1 ∧ p2)) ∧ ((p4 ∨ p1) ∨ (p3 ∨ True))) ∨ (((True ∨ (p1 ∨ ((p2 ∨ p4) ∧ (True ∧ p3)))) → p2) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60011914047222508831127689273 : (((p1 ∨ True) → (p1 ∧ (True → (p1 ∧ (((((((p3 → False) ∨ ((True → p3) ∨ p1)) ∧ p4) → (True ∧ p2)) → p4) → p1) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63270995647132790195315674429 : ((p5 ∧ (((False ∨ p3) ∨ ((p2 ∨ p1) ∨ True)) → ((p5 → False) → ((p4 ∧ False) ∨ (False ∧ (p1 ∨ (p5 → (p3 → (p3 ∨ p3))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48039334201503988009272916845 : (((((True → ((p1 ∨ p2) ∨ False)) ∧ (False ∨ (p2 ∨ p2))) ∨ (((p5 → False) ∧ ((True → p4) ∨ p4)) ∧ (p2 ∨ p4))) → (p5 → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h18 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h19 := h13 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h23 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h24 := h13 h23
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40040458573540562287923616214 : (((((True ∧ (p3 → ((p1 ∨ (((p1 ∧ (p4 ∨ False)) ∧ (True → p4)) ∨ (p1 ∧ (p5 ∧ p4)))) ∨ (False → p4)))) ∧ p2) ∧ True) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208639522984632620512458953978 : ((True ∧ ((p4 → p4) ∨ (False ∨ True))) → (False ∨ (p2 ∨ (p4 ∨ (p4 ∨ ((True ∨ p2) ∨ ((p1 ∨ False) ∧ ((True ∨ (True → p5)) → p4)))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199292084485831621087901646270 : ((((p5 → ((p1 ∨ p4) → p1)) ∧ p5) ∨ True) → (((((True → p4) ∧ (p5 ∧ p1)) ∧ ((True → p1) → p1)) ∨ (True → True)) ∨ (p2 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98815306360886498728681244865 : ((True → (((True ∨ (p3 ∧ (p4 → p5))) ∧ (((p3 → (((True → False) → True) ∧ p5)) ∧ ((p4 ∧ p4) ∧ p4)) ∨ (False ∧ p4))) ∧ True)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122093354156511088674645497320 : (((p5 → (((True → ((((True ∨ (p5 ∧ False)) ∨ p1) ∧ False) ∧ ((False ∧ p4) ∧ False))) → (p3 ∨ (p3 ∧ p3))) ∨ p1)) → p1) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51595221973671121629319386949 : (((p2 → ((((p2 ∧ True) ∨ p2) ∨ False) ∨ (p3 ∧ (p1 ∨ (p5 → ((True ∨ p3) ∧ p4)))))) → (((p4 ∧ (p1 ∨ p4)) ∧ p4) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114767948665301353399572483461 : (((p4 → ((True → ((((False ∨ p4) → (p4 ∨ p4)) ∧ (p4 ∧ p1)) ∨ True)) ∧ False)) → ((p5 ∧ False) ∧ (True ∧ (p1 ∧ p1)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61695299275307263646477394634 : ((p1 ∧ (p2 ∨ ((p5 ∧ ((p5 → (((True ∧ p1) → (True → p2)) ∨ (p5 ∧ ((True ∨ (p4 ∧ p4)) ∨ p5)))) → False)) ∨ (p4 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301436298741438237396220004377 : (False ∨ ((p3 ∧ ((p4 ∧ p4) → True)) → (((False ∧ p2) ∧ ((((p4 ∧ (p4 ∨ (p3 → (True ∨ (p2 ∧ p1))))) → p2) ∧ p3) ∧ p5)) ∨ True))) := by
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
theorem thm_5_vars_66763087684638391422337766224 : ((True → (p3 ∧ (((False ∧ p4) ∨ ((p4 → ((True → ((True ∧ p3) → True)) ∧ True)) ∧ ((p3 ∨ p2) → p1))) ∧ (False ∨ (p5 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164884571093997670311147327688 : (((p2 → (False ∧ (p4 → ((p3 → (p4 ∨ True)) ∧ ((p3 ∧ (p1 ∧ True)) ∧ p4))))) ∨ False) ∨ (((((False → p5) ∧ p4) ∧ True) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609599546322151362836787034232 : (((((p5 ∧ ((p1 → (True → ((p3 → ((p5 → p2) → p4)) ∧ True))) ∨ ((((False → p4) ∨ (p3 ∧ p3)) → p1) ∨ p2))) ∨ True) ∨ p1) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_336093685191048931204659212227 : (p1 → ((((p3 → True) → (((((True ∧ (p5 → (p4 ∨ (((p5 ∨ True) ∧ (False → p1)) ∧ p2)))) ∨ True) ∧ p2) ∧ p2) ∨ p5)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48998685653624819086044972795 : ((((p5 ∨ (((p2 → True) ∨ p4) ∧ (((p3 ∨ p2) ∧ (p5 → (p4 ∧ p5))) ∧ (True ∧ (p3 → p4))))) ∨ True) ∨ (False ∨ (p1 ∨ p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86674286241343647688984891642 : ((((False → p2) → (p4 ∧ (p3 ∧ (False → p3)))) ∧ (((p4 ∧ False) → True) ∧ ((p1 ∧ ((((p4 ∨ p4) ∧ False) ∨ p1) ∧ p1)) → True))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199334460445748381473339445808 : (((((p4 ∧ (True ∧ p2)) → p3) → p3) ∨ p5) → (((p5 → (p5 ∨ False)) → p5) → (((p2 → (p5 → (p3 ∨ p5))) ∧ p2) → (p3 ∨ p2)))) := by
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
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115284719633787634836706957715 : (((p5 → ((p2 ∧ ((True ∨ (False ∨ p4)) ∧ p2)) ∨ p2)) ∨ ((True ∧ (p4 → (p1 → ((p3 ∨ False) ∨ (True ∨ p4))))) ∨ p3)) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58554656175011864862449478471 : (((True → True) ∧ ((p1 ∧ (True → True)) ∧ ((True → False) → ((True ∧ (((p1 ∨ p1) ∨ ((p5 → False) → p4)) ∧ (p1 ∨ p1))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179703423886503897040216973245 : (((((((p1 → True) → p3) ∨ True) → (True ∧ (p5 ∧ p1))) ∨ False) ∧ p2) → (p3 → (p1 ∧ (((p2 ∨ p1) → p3) ∨ ((p2 ∧ True) ∧ p2))))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p1 → True) → p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h12
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328304221421991066069827799230 : (True → ((p1 ∧ (p2 → (((((p2 ∨ (p3 ∧ (True ∨ True))) ∨ p5) ∧ p3) ∧ (True ∨ p4)) → (p4 ∧ p4)))) ∨ (((p2 → p4) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42619005143930693948472129081 : (((p3 ∨ ((p4 ∧ ((((((p5 → True) ∧ (p3 ∧ ((p3 → p4) ∧ p3))) ∨ p5) ∨ p4) ∨ p1) ∨ p4)) ∨ (p5 ∨ (True ∧ True)))) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_167253541307314901621497612604 : (((((False ∧ (p5 ∨ ((p1 → p3) ∧ (True → ((p3 ∧ False) → p3))))) ∨ False) ∧ p2) → p2) → (p4 ∨ (p4 ∨ (p5 → ((p2 → p1) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193454944903827299721557373188 : (((p5 → p1) ∧ (p3 ∨ ((False → (p4 ∧ p3)) → False))) → (((p3 → (p4 → p4)) → p3) → (p3 ∨ (((p2 ∧ (p2 ∨ p5)) ∨ p1) → False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (False → (p4 ∧ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150440433094271848774257547891 : (((((p2 ∨ ((((p4 ∧ False) ∧ True) ∨ ((p3 → p3) ∨ p2)) ∧ (p2 ∨ (p4 → True)))) ∨ p2) → p4) ∧ p3) → (((p1 → p4) ∧ p3) → p4)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 ∨ ((((p4 ∧ False) ∧ True) ∨ ((p3 → p3) ∨ p2)) ∧ (p2 ∨ (p4 → True)))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42639316414358786672443723164 : (((p3 ∨ (p5 ∨ ((p1 ∨ p4) ∧ (((p2 ∨ False) ∨ (((p3 ∨ p5) → p2) → ((False → (True ∧ (p3 → p2))) ∧ p4))) ∧ p5)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58253579185931881720815060886 : (((p5 ∧ p2) ∧ (((p1 → p5) ∧ (((((p3 ∨ p1) → ((p4 ∨ p4) → (p5 ∨ p2))) ∨ p2) ∨ p5) → ((p2 ∧ True) ∨ p3))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149897848495767228028504875142 : ((p2 ∨ (p1 ∨ ((p5 ∧ ((False → ((p2 → p2) → p3)) → ((p5 ∨ (False ∧ (p4 → p3))) ∧ p2))) ∨ p3))) ∨ ((p5 ∧ p1) → (p4 → p4))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696278441399717767917126953131 : ((((False → ((((p4 → (False ∧ (p4 → True))) ∨ False) ∧ (True ∨ False)) → p4)) → ((False → ((p4 → True) → True)) ∧ (p2 ∨ (False ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64992883003105017547737239257 : ((p2 ∨ (((p5 ∧ p1) ∧ p5) ∨ (((((((p2 → (p2 → p5)) → True) → (p5 → p5)) ∧ p2) ∧ (False ∨ (False ∧ p4))) ∧ p4) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137043366012398583488132248807 : (((True → p5) → (p2 ∨ ((((p4 ∨ ((True ∧ (False ∨ p2)) ∧ p5)) ∨ p1) ∨ p2) → (p2 → (p4 ∧ (p4 ∨ True)))))) ∨ (True ∨ (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241864198872848085317413461742 : ((p1 → p1) ∧ (p1 ∨ ((((True ∨ p1) → (((p2 ∨ (p1 ∧ (False → (p5 ∨ p5)))) ∧ p4) ∨ ((p1 → p5) ∨ (True ∨ p3)))) ∨ True) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134581852499997786826690945793 : ((((((p3 ∧ (True ∨ ((p3 → False) ∨ (p2 ∧ ((False → True) ∧ True))))) ∨ (True → True)) → p1) ∨ (p5 ∨ p2)) → p2) ∨ (True ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338274985086814185921455214123 : (p1 → ((((p2 ∨ p2) ∧ True) → (False ∧ p3)) → (((p2 → (p4 → ((p4 → ((False ∧ p4) → p1)) → False))) → p4) ∨ (False → (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41364094784454035622388417316 : (((((p3 → ((((p2 → (True ∨ p2)) ∨ (False → p5)) ∨ p3) ∨ p2)) → (p5 ∨ p5)) → (False ∧ ((p5 ∧ (p2 ∨ p1)) → False))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234523031534223471039470052401 : ((p2 → (p3 → p4)) → ((((p4 → (False ∧ ((False → True) ∨ (((p4 ∧ p2) ∧ p5) ∧ (True → p1))))) ∧ p2) → p1) ∨ ((p5 → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604783820816961525135284028672 : ((((p1 → ((p5 ∧ ((p5 ∧ ((p5 ∧ (True ∧ (((False → (p4 ∨ (p4 ∧ p2))) ∧ p2) → (p2 → p4)))) ∧ p5)) ∧ p5)) ∨ p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167343338950399831667844386360 : (((((p3 → p3) ∨ ((p3 ∨ (p3 ∧ (p2 ∨ True))) ∨ False)) ∨ (p2 ∧ (True ∨ p5))) → p5) → (False ∨ ((False ∨ p5) ∨ ((False ∧ True) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → p3) ∨ ((p3 ∨ (p3 ∧ (p2 ∨ True))) ∨ False)) ∨ (p2 ∧ (True ∨ p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179392530744535374362313896287 : ((p3 ∨ (((False → ((p5 ∧ p1) → p4)) → p3) ∨ ((p2 → p4) → p4))) ∨ (((p4 ∨ ((p3 ∨ False) → p4)) ∨ ((p1 → p3) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134047424278703364972889960376 : (((((p2 → p3) → (p5 ∨ ((((False ∨ (p1 → True)) → (False ∧ (p5 → p4))) ∨ (True ∧ p3)) ∧ p3))) ∨ p3) ∨ p1) ∨ ((False ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



