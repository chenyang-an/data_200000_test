variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66567149657125686645975933015 : ((True → ((((p2 ∨ p5) ∨ p2) ∧ (((p1 → (p4 → p2)) ∧ p3) ∧ (p5 → ((p2 ∧ True) ∧ (p4 ∧ (p5 → p1)))))) ∨ (p1 → p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68290303652591211326335942637 : ((p3 → ((((p3 → False) ∨ (((p4 → (p1 → (p4 ∧ (p1 ∧ p3)))) → p4) ∨ (p4 ∧ (True ∨ p4)))) ∨ p1) ∨ (p5 ∨ (p4 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57642405255581569142305513843 : ((((True ∨ p3) ∨ False) → (p5 ∨ ((p1 → ((p2 ∨ (((p1 → True) → ((p5 ∨ (p5 → False)) ∨ p2)) → True)) ∨ p3)) ∧ (p1 ∨ True)))) ∨ p5) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338291252053026875786757708229 : (p1 → ((True → (False ∧ ((p1 ∧ p1) ∨ p1))) → (False ∨ (((p5 ∨ p4) → (p4 ∨ p5)) ∧ ((((p1 → p1) ∧ p2) ∧ p3) ∧ (p1 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626174797326969671226608785959 : ((((p3 → (((p1 ∨ ((False → (p4 → ((p3 ∧ p5) ∧ (True → (p3 → p2))))) ∧ (((p2 ∧ True) → False) → False))) ∨ p3) → p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776754517222833455745727601222 : (((p1 ∨ (((p5 ∨ (p3 → (((p1 ∨ False) ∨ (p4 ∨ (p1 ∧ ((False → p5) ∨ (p1 ∨ (p1 → p4)))))) ∧ p1))) → (True ∧ p5)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45686069825462646023750894994 : (((p5 ∨ ((p1 ∨ p3) → ((False ∧ (True ∨ ((p5 → p4) ∧ (p2 ∧ p1)))) → (((((True → False) ∨ p5) → True) ∧ p5) ∨ False)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164659479782186452510343645546 : (((p3 → (((p5 ∨ (p5 → (p1 → (p4 ∧ p5)))) ∧ p3) ∧ ((p5 → p3) → p4))) ∧ False) ∨ ((p2 ∨ (p1 → p2)) ∨ (p3 → (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150808812579016495437811241048 : ((((p1 ∧ (p1 → (((p3 → True) → p1) ∨ (p3 ∨ (True ∨ ((p5 ∧ p3) ∨ True)))))) ∨ (True ∨ False)) ∨ p1) → (((True → False) → False) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h12 := h2 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198650548776485399466843914936 : ((p3 ∨ (False ∧ (((False ∧ p3) ∧ p5) ∧ p3))) ∨ ((((p3 → (p3 ∨ True)) ∨ ((True ∧ p1) ∧ p5)) ∨ True) ∧ (True ∨ (p4 → (p1 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193544746532859776700315115564 : (((p2 ∧ p1) → ((((p1 ∧ False) ∧ True) ∨ p1) ∨ p2)) → (((p1 ∨ (p4 ∧ (False ∧ p2))) ∧ ((False ∨ p4) ∨ (p5 ∨ p5))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214795050593729790644337109203 : (((p1 ∨ p4) ∨ (p1 ∧ p5)) ∨ ((((((p5 → (p5 → (p2 ∧ (False → (True → (p3 ∨ True)))))) ∨ p4) ∨ False) → p4) ∨ (True ∨ False)) ∨ p5)) := by
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
theorem thm_5_vars_41996122850850690990072744685 : ((((False → p2) ∧ (((((p1 → True) ∨ p3) → ((p5 ∨ (True → p5)) ∨ (p5 ∧ (p5 → ((p3 ∨ p2) ∨ True))))) ∨ True) ∨ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179655215384070962021215622451 : ((p5 → (((p5 → (p1 ∧ p5)) ∧ (p5 ∨ p2)) ∧ ((p3 → True) → p1))) ∨ (True → (((p4 ∨ ((p5 ∧ p3) ∧ (p2 → p2))) ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206300932207500804688905979165 : ((p1 ∨ (((True ∨ p3) ∧ p5) → False)) ∨ ((p4 → p3) → ((((((p3 ∧ p5) ∧ p1) ∧ (p1 ∧ False)) ∧ True) ∨ True) ∧ ((p5 ∨ p1) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_46883058706244195596825936796 : (((((p1 ∨ ((p5 ∨ ((((False ∨ True) ∧ p4) ∧ p4) ∧ (p5 → p1))) ∨ ((p4 → p3) ∨ (p5 ∨ p5)))) ∧ True) ∨ True) ∨ (p2 → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52317026028772039266673314023 : ((((((p4 ∨ ((p1 ∨ True) ∨ (p3 ∧ p1))) → p3) ∧ (p3 ∧ False)) ∨ p4) ∧ ((p5 ∧ p1) ∨ ((False ∧ p5) ∨ ((p3 → p2) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164726753243791681478446685138 : (((((p5 ∧ p1) ∨ ((p2 → p3) ∨ ((p5 ∧ p5) → ((p2 ∨ p2) ∨ p2)))) → p1) ∨ p3) ∨ ((True ∨ p3) ∧ ((p1 → (True ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47523815136902513289695467520 : (((p3 ∨ ((p1 ∧ p2) → (False ∨ (((p4 ∨ ((p4 → p4) → (p1 ∧ p1))) → (p3 ∧ (p2 ∨ (p4 ∧ True)))) ∨ p4)))) ∨ (p3 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135910148500660518826937575200 : ((((p4 ∧ ((False ∧ (p3 ∧ False)) ∨ True)) → ((p5 ∨ p5) ∨ p1)) → (((((p5 ∨ True) → p2) → p4) → p5) ∨ p3)) ∨ (p3 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64603179366048474077624031124 : ((p1 ∨ ((p1 ∧ p1) → ((True ∨ (((p2 ∨ (((True ∧ (p5 → p4)) ∨ (p2 → p3)) → (p5 ∨ p4))) → False) → (p4 ∧ False))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586837008478580673377357447353 : (((((p5 ∧ (((p3 ∧ p3) ∧ (p2 → ((((p5 ∨ (True → p2)) → True) → p5) → (p5 ∧ (p1 ∨ p3))))) → (True → False))) ∧ p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706358411921956293431547687806 : ((((True ∨ ((p1 ∨ (False ∧ p3)) ∨ (p3 ∨ True))) ∧ (False ∨ (((True ∨ p1) → p2) → (((p4 → False) ∨ (p1 ∨ (True ∨ p3))) ∨ p1)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351221495512672018028896415096 : (p4 → ((((False ∨ (p3 ∧ p5)) ∨ ((p5 ∨ ((((p4 ∧ True) ∧ (p1 → (p2 → False))) ∧ p5) → False)) ∨ p5)) → p1) ∨ ((False ∧ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354742996801520941953195185729 : (p5 → (((((p4 → p4) → False) ∨ (((p2 → (p1 ∨ (True ∨ False))) ∧ (True ∨ p4)) ∨ p2)) ∧ (p1 → ((p4 ∨ p4) ∨ (p4 → p1)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709421020675146007053823757949 : ((((p1 ∧ (p5 ∧ ((True → (True → p3)) → True))) → ((p2 ∧ (p1 → (((False → p5) → (p1 ∧ (p3 ∧ (False → p5)))) ∨ False))) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307666343583925486331088027376 : (p1 ∨ (p2 → (((False → (p2 ∨ (((p2 ∨ (True ∧ ((p4 ∨ (p3 → ((p3 ∧ p4) ∧ True))) ∨ False))) ∧ (p1 → False)) ∧ True))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178207337329441162884664464939 : (((p2 ∨ ((((p2 → False) ∧ p2) ∧ p1) → (p3 → (p3 ∧ p4)))) → p3) ∨ ((False → ((p3 ∨ (False ∨ True)) ∨ p3)) ∨ (p2 ∨ (False ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116588265404564743309445555816 : (((p4 ∨ p3) ∧ (((p4 → p4) ∧ ((True → (False → (p3 ∨ (False ∧ False)))) ∨ True)) → ((p1 → ((p5 ∧ p1) ∧ p3)) ∧ p1))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112440059500612385708917812369 : (((((True → (((((False → False) → (p1 ∧ p5)) ∧ (p2 → False)) ∨ (((False ∨ p3) → p1) ∧ p3)) → False)) ∨ False) ∨ p2) → p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606551653630542103980750023903 : ((((((((((p5 → False) → (p2 ∧ p3)) → (p1 → ((True ∨ p2) ∨ p1))) → True) ∨ (True ∨ ((False ∨ False) ∨ p5))) → p4) ∧ p5) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_37701713084619538572113039425 : ((((((False → (((((p3 ∧ p2) → (p5 → False)) ∨ False) → p4) → True)) ∧ (p4 → (p3 → p4))) ∨ (p3 ∧ (True ∨ p3))) → p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67756620861498322287815597578 : ((p2 → (((p1 ∨ (((p1 ∧ (((p1 ∨ ((p2 ∨ (p1 ∧ p2)) ∨ (True ∨ (False ∨ p2)))) ∨ p2) ∧ p5)) ∧ p2) → False)) → p5) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667166717851436748982766359532 : ((((((True ∨ p4) → p3) → ((p4 ∧ (((p2 ∨ ((p4 → p1) ∧ p5)) ∧ p5) → p4)) ∨ (True ∨ (p2 → p1)))) ∧ ((p2 ∧ True) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173127231907981265207366805402 : ((p2 ∨ (p2 ∧ (p5 → (p2 ∧ ((p2 → (((True ∧ p1) ∧ p1) → p3)) ∧ p5))))) ∨ (((False ∧ p2) ∨ False) ∨ (((p5 ∧ p1) ∧ p5) → p5))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57658036062872871401353081383 : ((((p3 ∨ p5) ∨ True) → ((p4 ∨ ((p2 ∨ (((((True → p3) ∨ p3) → (p4 → False)) ∧ p4) ∨ True)) ∨ False)) ∧ (True ∧ (p1 → p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
  case inr h5 =>
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389072071665354987360884708226 : (((((p4 ∨ (p3 ∨ (True ∧ (((p5 ∧ (p3 ∧ (p5 ∨ p1))) ∧ (p3 ∨ p2)) ∧ p5)))) → ((True → ((p5 ∧ p1) ∧ p4)) → p4)) ∨ p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h21 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h23 := h2 h22
          -- We need to get the right conjuct of h23 based on <expert-advice>.
          let h24 := h23.right
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h26 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h27 := h2 h26
          -- We need to get the right conjuct of h27 based on <expert-advice>.
          let h28 := h27.right
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h30 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h31 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h32 := h2 h31
          -- We need to get the right conjuct of h32 based on <expert-advice>.
          let h33 := h32.right
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h36 := h2 h35
          -- We need to get the right conjuct of h36 based on <expert-advice>.
          let h37 := h36.right
          -- One of the premise coincides with the conclusion.
          exact h37
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137203028928829570068395775667 : ((False ∧ (p1 ∨ ((p1 → p5) ∧ (p2 ∧ ((p1 ∧ (p5 ∧ (p2 ∨ (p4 ∨ False)))) ∨ ((p1 ∧ (p5 ∨ p1)) ∧ p4)))))) ∨ ((False → False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81017286918982047504688014335 : ((((((p4 → p2) → ((p5 ∨ False) ∧ p2)) ∨ ((p1 → (p4 → False)) ∨ p1)) → ((False ∨ (p5 ∨ p2)) ∧ p4)) ∧ (p1 ∨ (p3 ∧ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p4 → p2) → ((p5 ∨ False) ∧ p2)) ∨ ((p1 → (p4 → False)) ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696567293689054348637471810352 : (((((((((p2 → False) → p2) ∧ p4) ∧ (True ∨ p3)) ∨ p2) ∨ p3) ∧ ((p5 ∧ p3) ∨ ((((p2 ∨ p4) ∨ (True → p5)) → p4) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241595554669648008169306918203 : ((False → p4) ∧ ((p3 ∨ (((True ∨ p1) → p3) → (p1 ∨ ((p5 ∨ (p4 → p3)) ∨ ((p3 ∨ p2) ∧ p2))))) ∨ ((False ∧ p3) ∨ (False ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196742429165733444262270870379 : (((((p5 → True) ∨ p4) ∧ (p4 ∧ p2)) ∧ p1) ∨ (p1 ∨ (p5 → ((True ∧ (False → (p5 → p1))) → ((p5 → (p3 ∨ False)) ∨ (p2 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147922056853932381946729612062 : (((((((p3 ∨ True) ∨ (True ∨ (p1 → p2))) ∨ p1) → p4) ∧ (False ∨ (p3 ∨ (p3 ∧ True)))) ∧ (p2 ∧ p2)) ∨ (True → (p3 ∨ (False → p1)))) := by
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
theorem thm_5_vars_654697343041662818860942539420 : (((((((True → ((p4 ∨ (True ∨ ((p3 ∨ p5) ∧ False))) ∧ ((((p1 ∨ p2) → True) ∨ p4) ∧ p3))) ∧ True) ∨ False) → False) ∨ (p1 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737617576454595345894714681149 : ((((p5 → p2) ∧ ((p3 → (False ∧ p3)) ∧ ((((p1 ∧ (p1 ∧ (p3 ∧ ((p1 ∧ p5) ∨ False)))) ∧ p1) ∨ p5) ∨ ((p3 ∧ p5) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57228161204412050709969903259 : ((((p5 → p4) ∨ p5) ∨ (p4 ∧ (p2 ∧ (((p2 → ((p1 ∨ (((p5 ∧ p2) ∧ p2) → (True ∨ (p3 → p1)))) → p3)) → p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44618305167223994708374660521 : (((((((True ∨ p1) → p3) ∧ p1) ∨ p3) ∧ ((((p1 → p5) → True) → ((p5 → p2) ∧ p3)) → (p3 → (p4 ∨ (p4 ∧ p4))))) → p3) ∨ p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115636490135356213605439781025 : ((((((False → p4) ∨ True) → False) ∨ False) ∨ (((False ∨ ((((p2 → p5) ∧ p3) ∧ p3) → (True → p4))) → (False → p5)) ∨ p4)) ∨ (p1 → p3)) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691864035566486906763958300787 : ((((False → ((((((p3 ∨ p1) → p4) → p1) → False) ∨ p4) ∧ (p3 → (p5 ∧ p5)))) → ((True ∧ (False ∧ (p2 ∨ p1))) ∨ (False ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230707976640367623151274360815 : (((p4 → p4) ∧ p1) → ((p2 ∧ (True → ((((p5 ∧ (True → p1)) → (p3 ∨ (((True → (True ∧ True)) → p2) ∨ p3))) ∨ p1) → False))) ∨ p1)) := by
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
theorem thm_5_vars_352121175224177191453747173651 : (p4 → ((p3 ∨ (p5 ∧ (p1 ∧ (p1 ∨ p1)))) ∨ (True → (((p4 ∧ (True → ((p1 ∨ p2) ∨ (p3 ∨ (True ∨ True))))) → False) ∨ (False → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803224844060721700052656205012 : (((p3 → (((((p1 ∧ (p4 ∧ (False ∨ (((p2 ∨ p5) ∧ p3) ∨ (p3 ∨ True))))) ∨ p4) ∨ ((p5 ∨ p5) ∨ (p3 ∧ p1))) → p2) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299307408326573910114080262747 : (False ∨ (((((p5 → True) ∧ False) ∨ ((p1 ∨ p5) → p5)) ∨ ((p4 ∧ p5) ∧ (p2 ∧ ((p1 ∧ p4) ∧ (p3 ∧ ((p4 ∨ p4) → True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116426660313863128238339215444 : (((p5 ∨ (p2 → p2)) → (p4 → (p5 → (((p2 ∧ p5) → p3) → ((p5 ∧ p1) ∧ (p1 → (p5 ∨ (True ∧ (False ∧ True))))))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219282079455464402780258909872 : ((p1 ∨ (p4 → (p5 → p5))) → ((((True ∨ True) → False) ∧ p1) → ((True → ((p3 ∨ (p4 ∨ p1)) ∨ (p2 → (p3 ∨ p3)))) → (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255135937318710003885088985328 : ((p4 ∧ p3) → (((p2 → p4) → ((((True → (p4 ∧ (((True ∨ False) → (p1 ∨ p5)) → False))) → False) ∨ p5) ∨ p4)) ∨ ((p4 ∨ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208211417785705634516685602081 : (((p2 → (p2 ∨ p1)) → (p2 → p4)) → ((((((p2 → (p3 → p2)) ∨ p2) ∧ (p2 → p3)) → (p3 ∧ p2)) ∨ p4) → ((True → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137288509220985116031258275243 : ((p2 ∧ ((((True ∧ (p1 → (p5 ∧ (False → p1)))) ∧ p2) ∧ ((p4 → True) → ((False → p3) → (p4 → p5)))) ∨ p4)) ∨ (p3 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109577106697749261434610768787 : ((p3 ∨ ((p5 ∧ ((p5 → (True ∧ (p1 ∨ p5))) → False)) ∨ (True ∨ ((p4 ∧ p2) → (p5 → ((p3 ∨ (True ∨ p3)) ∨ p1)))))) ∧ (False → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159828771967569962106583923532 : (((p3 ∨ (True ∨ (((p5 ∨ p5) ∧ ((p5 ∨ (((False ∧ p2) ∧ p2) → p1)) ∧ p3)) → True))) ∨ p3) → (((p2 → False) ∨ (False → p2)) ∨ True)) := by
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
theorem thm_5_vars_787188345144265502493440266952 : (((p4 ∨ (True ∧ ((False ∨ (((False → (((True ∧ p4) → p4) → False)) → False) → ((p3 → False) → (((p1 ∨ p5) ∧ False) ∧ False)))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55328742200741848637843008440 : (((p4 ∨ (((p3 ∨ p1) ∧ p3) ∧ p1)) ∨ (p4 → ((p5 ∨ (p3 → p4)) → (((p1 ∧ False) ∧ (p5 → p1)) ∨ ((True → p5) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119116274080753907941801652597 : ((p1 → ((p3 ∨ p1) → ((((((p3 ∨ p3) → False) ∨ p3) ∨ p5) ∧ p2) ∨ (p1 ∧ ((False → p3) ∨ (p1 ∨ (False → p4))))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40140678440961320533040273547 : (((((((p2 → (p5 → p4)) → p3) ∧ ((False ∧ ((p3 ∧ False) ∧ p5)) → (p2 → p4))) → ((p2 → (p3 ∨ p5)) ∧ p2)) ∧ p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639354426634315331364342702645 : ((((((p2 ∧ p2) → (True → p5)) → ((((((True ∨ p4) ∧ False) ∨ p4) ∨ p2) → ((p4 → (p5 ∨ (p3 ∧ False))) → p2)) ∧ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148328220190296717041691951062 : ((((True → ((True ∧ p1) ∨ ((((p5 → False) → True) ∨ p4) → p2))) ∧ p1) ∧ ((p4 ∨ p3) ∧ (p5 ∨ p2))) ∨ (p4 ∨ (p2 → (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164790515535554239049725651649 : (((((p3 → (p5 → False)) → p5) ∨ ((p4 ∨ ((p1 ∧ p4) ∨ p5)) ∨ (False ∧ True))) ∨ True) ∨ ((((False ∨ p1) → (True ∧ p4)) ∧ p3) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107098818057160054818006617051 : (((p2 ∧ (p1 → (p1 → p2))) → (((p1 ∨ ((p5 → p5) → (p3 ∧ p5))) ∨ (p2 ∨ (p5 ∧ False))) ∨ ((False ∨ p1) ∨ p1))) ∧ (p1 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115930573614506659998981432320 : (((p1 ∧ (p2 ∨ (True ∧ p1))) ∨ (p5 → ((((p3 ∨ (p5 → True)) ∨ (p1 ∧ p5)) → p2) → ((p1 ∨ p2) ∧ (True ∨ False))))) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (p5 → True)) ∨ (p1 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49475047415713295361959128176 : ((((((p5 ∨ (((((p5 ∨ (p5 ∨ (p1 ∨ p2))) → p3) ∧ p2) ∧ True) ∧ (p4 → p3))) ∨ True) → p2) → True) → (False ∧ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115036537381190120746796736589 : (((((((p3 → p1) ∨ p4) ∧ p1) → ((p5 ∧ False) ∨ p2)) ∧ p2) ∨ (False ∨ (((p3 → False) ∧ p5) ∨ (True → (p3 → p3))))) ∨ (p4 ∧ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345386740735170027650789579007 : (p3 → (((True → (((((((((False ∧ p5) ∨ (False → ((p5 → p1) → p3))) ∨ p4) ∧ True) ∨ p2) ∧ p5) ∨ p1) ∨ p4) → p4)) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64166639417508557896434655103 : ((False ∨ ((False ∧ p2) ∨ (p4 ∧ ((((p1 → p1) → (True ∧ p5)) ∧ ((((p2 → (False ∨ p5)) ∧ p3) ∨ (p4 → p3)) → p3)) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190194422524068374023072593510 : (((p2 ∨ ((p5 ∨ (p2 → (p2 ∧ p1))) → False)) ∧ p3) ∨ (((p1 ∧ (p5 ∧ (((False ∨ (p5 → True)) → (p4 ∨ p1)) → p2))) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157604982463412526754426128728 : ((((((((p3 ∨ p3) → p3) ∧ (False → False)) ∨ True) ∧ (p2 ∧ p2)) ∧ False) ∧ ((p5 ∨ False) ∨ p3)) ∨ (((False → p1) → (p3 → p3)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119250030342801220025904124321 : ((p2 → (p1 ∨ (((p4 ∨ (((((p1 ∧ p3) ∧ True) → False) ∧ p1) → p5)) ∨ ((p3 → p2) ∧ ((p4 ∨ p4) ∨ p5))) ∧ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117377230338319772264413984836 : ((False ∧ (p4 → ((((False → p3) ∨ p5) ∧ p1) ∨ (True ∧ (((((p2 ∨ (p3 → False)) → True) ∧ p1) ∨ p1) → (p3 ∧ p4)))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135243554590308700502782479797 : ((((p2 ∧ p4) ∧ (((((((p4 ∨ p1) ∧ False) ∨ False) ∧ p1) ∧ (p2 ∨ p1)) ∧ p2) ∨ (False → True))) → (False ∨ False)) ∨ (p4 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136393877285182844350642608968 : (((p4 ∧ ((p1 → p1) ∨ p5)) ∨ (((p3 ∧ p2) ∨ ((((p5 ∧ False) ∨ True) ∧ (p1 ∨ p2)) → False)) ∨ (p1 ∧ True))) ∨ ((False ∧ p2) → p5)) := by
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
theorem thm_5_vars_116590069550250403195439019660 : (((p4 ∨ p4) ∧ ((p5 ∧ (p5 ∧ p1)) ∨ (p4 → ((((p5 ∨ False) → p4) ∨ (p5 ∧ (p3 → p3))) ∧ ((p1 ∧ p5) ∨ p1))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261330049678814107314052341411 : ((p5 → False) → ((((p1 ∨ (p5 ∨ (p1 → p4))) ∧ (((False → p3) ∧ (p1 ∧ (p2 → p1))) ∨ p2)) → (p5 → False)) ∨ ((p4 → p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227598145976543224962077303367 : ((False ∧ (p4 ∧ False)) ∨ (p2 ∨ ((p2 → (p4 → ((False → p4) → (((p5 ∨ (p2 ∨ p5)) ∨ p4) → False)))) ∨ (p4 → (True ∧ (p5 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776285301018872199236894793259 : (((p1 ∨ (((p2 ∨ False) ∧ (((((p5 ∧ ((True → False) ∧ p2)) ∧ (p3 ∧ p3)) ∧ p3) ∨ ((p5 ∧ p3) ∧ p2)) ∧ (p5 ∨ p2))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69054386093700656357368183471 : ((p5 → ((False ∨ ((p1 ∨ p2) ∧ (((p3 ∧ p3) → p5) ∧ (((p1 ∧ (True ∨ True)) → ((False ∨ (p2 ∨ p2)) ∧ p5)) ∧ p4)))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157707630863424203733367440461 : ((((((True ∧ (p3 ∧ (p3 ∨ p3))) ∨ (p2 ∨ p4)) ∨ p1) ∨ (p1 → p1)) → ((p5 ∧ False) ∧ p4)) ∨ ((True ∧ False) ∨ ((p4 ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64461824568471532371449462931 : ((p1 ∨ ((p2 ∧ ((((p5 → (True ∧ (p1 → False))) → True) → (p5 ∨ ((p4 ∧ (p3 ∧ p5)) ∨ p5))) ∨ False)) ∧ ((p4 ∨ p5) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801305097827719199408736435652 : (((p2 → (((True ∧ p1) ∧ (((p4 → p3) → ((p1 → p2) → p4)) ∨ (p1 ∨ True))) ∨ ((p3 ∧ False) → (False → (False ∧ (True ∧ p4)))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752320823517050132257942714944 : (((False ∧ (((p1 ∨ ((((p4 ∨ (((p2 ∧ True) ∨ (p3 ∧ (p3 → False))) → (p3 → p4))) ∨ p1) → p2) ∧ (True ∨ p2))) ∧ p2) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50166328043306761073200163254 : (((p5 → ((p2 → ((((p1 ∨ True) ∧ True) → p3) → (True → True))) → (p1 ∨ ((p4 ∨ p1) ∨ p3)))) ∧ (p5 ∨ ((p3 → False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668092304421189395148703551438 : ((((True → (((((p4 ∨ p1) → p2) → False) ∧ False) ∨ (((p4 → False) ∨ (((p5 ∨ p5) → p5) ∨ p3)) ∨ p2))) ∧ (False ∧ (p5 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47175272257530095568692481871 : ((((True → (p1 → ((((p1 ∧ False) ∨ (p2 ∨ True)) → (p2 ∨ p5)) ∧ p1))) ∨ (p3 ∨ (((p3 → p2) → p1) ∨ p3))) ∨ (True ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51909481222128426757177487709 : (((((((False ∨ p2) ∨ p1) ∨ ((p2 ∨ p4) → (p5 ∨ False))) ∨ True) ∨ (p1 ∧ p2)) ∨ ((((True → p3) ∧ (False ∧ False)) → p5) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232217030026627231579669851248 : (((p1 → True) → p3) → (True ∧ ((True ∧ (((p1 → (p5 ∨ p2)) → p1) ∨ (True → p3))) ∨ ((((p2 → p4) ∧ p3) → p3) ∧ (False ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45885052371617950903807149272 : (((p3 → (p2 ∧ ((p2 ∧ (((p1 ∧ (p2 ∨ (p5 ∧ p1))) ∨ (p2 ∧ ((False ∧ ((False ∨ p2) ∨ p3)) → p1))) → p1)) ∧ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186207161996448420132577652914 : (((p4 ∨ (((p4 → (True ∧ (p3 ∨ p2))) → p4) ∧ True)) ∨ p3) → ((p1 → p4) ∨ ((((False ∨ p1) ∨ (p2 ∧ p2)) ∨ p4) ∨ (p1 → p1)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201096001908197744887140883664 : ((True → ((p5 ∧ (p4 → (True → p1))) ∧ False)) → (((((p5 ∧ True) ∧ ((True → True) ∧ (p1 ∨ p1))) ∨ p4) ∨ (p5 ∧ p1)) → (p2 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h14 := h1 h13
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h18 := h1 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h25 := h1 h24
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354777613900752981449689989971 : (p5 → (((((p1 → (p3 → p5)) → p2) ∨ (p2 → (True → p3))) → (((((p1 → p1) ∧ p4) ∧ p1) ∨ (False ∨ p3)) ∧ (True ∨ p5))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324375085713029810823779717495 : (p5 ∨ (((p1 → p4) → (True → (p5 ∧ False))) ∨ ((False → p4) ∧ ((p3 → ((p3 ∨ ((p5 ∧ p5) ∨ p3)) ∧ (p2 → (p1 ∨ True)))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60888812523501690014984828557 : ((True ∧ (p3 → (((((p3 → ((p2 ∨ True) ∨ ((((p5 ∧ p2) ∧ (p1 ∧ True)) ∧ False) ∧ p5))) ∨ (p1 → p5)) → p1) ∨ True) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117130951595918997146985150111 : (((p4 → p5) → (((p5 ∧ (p4 → (True → p5))) ∨ (p5 ∨ ((p1 → p3) ∨ ((p4 ∨ (p4 ∧ p3)) ∨ (p2 ∧ p3))))) ∨ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



