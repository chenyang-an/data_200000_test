variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111517918567904057910934939981 : (((p5 → ((p3 → ((p1 ∧ p1) ∨ True)) → ((((p5 → p4) ∨ ((p3 → True) ∨ p5)) ∧ ((p1 → p3) ∧ p4)) ∨ True))) ∧ True) ∨ (p5 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37184224699254938468292217060 : (((((p3 ∧ ((p2 ∧ ((p3 ∨ p2) ∨ p2)) → (True → False))) ∨ (((False → ((False ∨ p5) → p5)) → (p5 → p2)) ∨ p1)) ∧ p1) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66639757379362291436252261266 : ((True → (((p5 ∨ (False ∨ p3)) ∨ ((False ∨ p2) → ((False ∧ p1) ∨ True))) ∨ ((p4 ∨ p3) ∧ ((p2 → ((p4 → True) → p5)) ∨ False)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187121898084095303940775837211 : (((p5 ∧ p5) ∨ (p2 → ((False → ((p3 → p3) ∧ p2)) ∨ p1))) → (p2 → ((True → (p4 ∨ p4)) ∨ ((False → p3) → (p2 ∨ (p3 ∧ True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688827833216671720256706190428 : (((((((True ∧ (((p1 ∧ True) ∧ p4) ∧ ((False ∨ p3) → False))) → p4) ∨ p2) ∧ p4) ∨ ((((p4 ∨ p5) ∧ (p1 ∨ False)) ∨ p2) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353715949230285842432609782238 : (p4 → (True → ((((True ∧ False) ∨ (False → ((p5 → p3) → (False ∧ True)))) → ((True → ((False ∧ p3) ∨ ((False ∧ p3) ∧ False))) ∨ True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39295697227891666233551698777 : (((p1 ∧ (((((False → p1) ∨ p1) ∨ False) → True) → (((p4 → ((((p2 ∧ (p4 → p5)) → p5) ∧ p3) ∨ p1)) ∨ p5) ∨ p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182978895424873296178461775278 : (((p5 ∨ True) ∧ (((p2 ∨ p2) ∧ p2) ∨ (True ∨ (False ∧ p4)))) ∧ (True ∧ ((p1 ∨ (p4 → p2)) ∨ (True ∨ (((p1 → p3) ∨ True) ∧ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_171704815713113821259264241566 : (((p3 → (((False ∨ (p1 ∧ p5)) ∧ p3) ∨ (p1 ∨ ((False ∧ False) ∧ p1)))) ∨ p3) ∨ ((p5 ∨ p5) → (p5 ∧ ((p4 ∧ True) ∨ (p5 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98913361968225086336244555479 : ((True → (((((p4 ∨ (p3 ∧ p2)) → (False ∧ (p3 → ((((p2 ∨ True) ∧ p1) → p2) ∨ p3)))) → (p2 ∨ p1)) → p2) ∧ (False ∧ p3))) → p1) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658593072109081988558782528013 : ((((p3 ∨ ((((p5 ∨ p2) → ((False ∨ (p4 ∨ ((p5 → True) → (False ∧ p3)))) → (p3 ∨ (p3 ∨ p4)))) → False) → p1)) ∨ (p5 ∧ p1)) ∨ p4) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ p2) → ((False ∨ (p4 ∨ ((p5 → True) → (False ∧ p3)))) → (p3 ∨ (p3 ∨ p4)))) := by
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
        cases h3
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h11 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h12 : (p5 → True) := by
            -- Implications on the right can always be decomposed.
            intro h13
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h14 := h10 h12
          -- We need to get the left conjuct of h14 based on <expert-advice>.
          let h15 := h14.left
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h17 : (p5 → True) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h19 := h10 h17
          -- We need to get the left conjuct of h19 based on <expert-advice>.
          let h20 := h19.left
          -- False on the left can always be used.
          apply False.elim h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h2
  -- False on the left can always be used.
  apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789600411136038199813961883926 : (((p5 ∨ ((p3 ∨ (p3 ∨ ((True → p1) → (p3 → p5)))) ∨ ((p4 → (True ∧ ((((True ∨ p5) → p3) → (p2 → p3)) ∨ p4))) → True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208268463881379372382127604305 : (((True ∨ p1) ∧ (True → (p2 ∧ False))) → ((p1 → (((p2 ∧ p2) → ((p4 → False) ∧ (p2 ∨ False))) ∧ (False → (p2 ∧ p1)))) → (p4 ∨ False))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42680847630099853101065973649 : (((p4 ∨ (p2 → (p3 ∧ (p1 ∨ (True → (((p1 → p4) → p5) ∨ (p1 ∨ (((False ∧ ((False → True) ∧ p4)) ∧ p4) ∧ p4)))))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245678044452846502205854804928 : ((p3 ∧ p1) ∨ ((p2 → (True ∧ p1)) → (((p1 ∨ ((p2 ∨ False) ∨ ((p3 ∨ ((p4 ∨ (p4 ∨ p4)) ∨ p5)) → True))) ∨ (p1 ∧ p1)) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118182883845859580675930955539 : ((False ∨ (p5 ∧ ((p5 ∧ (p1 → ((False ∧ (p5 ∧ ((((p2 → True) ∨ False) ∧ (p2 ∧ p4)) ∨ (True ∧ p5)))) → p4))) → p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37344057317897192843844131341 : (((((p4 ∨ ((((((((p1 → p3) ∨ False) ∧ (p2 ∧ p4)) ∧ True) → (p5 → False)) ∨ (p4 ∧ p5)) ∧ p1) ∧ p2)) ∧ p4) ∨ True) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749626420332483093660041007009 : (((True ∧ ((((False ∧ ((p5 → ((p5 ∧ (p3 ∨ (p1 → (p1 → (((p2 ∧ p2) → False) ∧ p3))))) ∧ False)) ∧ p1)) ∧ p4) ∨ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116630414392218650987775983786 : (((p1 → p2) ∧ (((((p2 → True) → p2) ∧ p2) ∧ (((True ∨ ((True → False) ∧ p1)) ∧ False) → (False ∨ (False → True)))) → p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64307994051327715590811794556 : ((p1 ∨ ((((p3 ∨ ((True ∧ p2) ∨ (True → p4))) → (p2 ∧ (p3 ∨ (p4 → ((p3 ∧ ((p4 ∨ False) → True)) ∧ p4))))) ∧ p5) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184850503064813690764632150821 : (((p4 → (p4 ∨ (True → False))) → (((p2 ∧ False) ∧ p2) ∧ p3)) ∨ (p5 ∨ (p5 → ((((p4 → (p5 ∧ p1)) ∨ p2) → p3) → (p5 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767484712108845783741116484770 : (((p5 ∧ (((((p4 → (((((p2 ∨ (p3 ∨ p1)) ∧ (p1 → (p5 → False))) ∧ p4) ∧ (p5 ∧ True)) ∧ p1)) → False) → p5) ∨ False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740935149444988480170751349059 : ((((p3 ∨ p2) ∨ (p5 ∨ (((False → (((True ∧ p3) ∨ p4) ∨ (p3 → ((True ∧ ((True ∧ p1) ∨ False)) → (p3 → p1))))) → p3) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226123129795323599251053411799 : (((False ∨ False) ∨ p5) ∨ ((False ∧ p3) ∨ (True ∨ (p1 ∧ (p4 ∧ ((p5 ∧ p1) ∧ (((p4 → ((p2 ∨ p4) ∨ (p4 → p2))) → p1) → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315833175137338146288461919651 : (p3 ∨ ((p5 ∨ p5) → ((p3 ∨ ((p4 ∨ p2) ∧ p5)) ∨ (p3 → (p3 ∨ (p1 ∧ (p1 ∧ ((((p4 ∨ p3) ∧ p5) ∨ p5) ∧ (p2 ∨ p3))))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161280291032453048177915914112 : (((False → False) → (p2 → (((False ∨ (True → p3)) ∧ p4) → ((p3 ∧ p5) ∨ ((p5 → False) ∨ p1))))) → ((p3 → True) ∧ ((p4 ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219727299943342962706580704023 : ((p1 → (False ∨ (p1 → False))) → ((p1 ∨ (((((p3 ∨ p4) ∨ False) → (True → (p1 ∨ (p3 → p4)))) ∧ p4) → p1)) ∨ (False → (p4 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22259377403172833288908448752 : (((((p3 ∨ ((p1 ∨ p2) → p3)) ∧ p2) ∧ p3) → ((p5 ∧ ((p5 ∧ p2) ∨ (((p5 ∧ (p2 ∨ p5)) ∧ True) ∧ p2))) ∨ (p4 → p4))) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641964501187773306459774492950 : (((((p5 → True) → ((p5 ∧ (p5 → ((p5 ∧ (((True ∨ (p3 ∧ (p3 → p2))) → p4) → (p4 ∧ (True ∨ p4)))) ∧ p3))) ∨ p3)) → p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587530898172187351977505521527 : ((((((p2 ∧ ((p2 ∧ ((True ∨ p2) ∨ ((False ∨ ((p2 ∧ True) → (p5 ∨ p1))) ∧ (p3 ∧ p2)))) ∨ (p4 → False))) ∨ False) ∨ False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768660145243528715026925498248 : (((p5 ∧ ((p1 ∧ ((p3 ∨ False) ∧ ((p4 ∧ p1) ∨ (p4 ∨ (False ∨ p3))))) → ((p2 ∧ p4) ∧ ((((p1 ∧ p5) → False) ∨ True) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324179479076962684990389780702 : (p5 ∨ ((p4 ∧ ((p2 → (p2 ∧ ((p2 → p4) ∨ p1))) ∨ p5)) ∨ ((((False ∧ p5) ∧ p3) ∧ False) → (p5 ∧ ((p3 ∨ p2) → (p1 ∧ True)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327153147898448480926274578929 : (True → ((p3 ∧ (p1 ∧ ((False ∨ ((p5 ∧ (False → (p2 ∧ (p2 → p1)))) ∧ p2)) ∨ ((False ∨ p1) → (((p3 ∨ p5) ∧ False) ∧ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751208536662343925930368908920 : (((True ∧ (((p2 ∨ p5) ∨ True) → ((p5 ∧ False) ∧ (False → ((p1 ∨ (True → (p3 ∧ (p2 ∧ (True → ((p5 ∨ p1) ∨ False)))))) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105146135846470509679755236721 : ((((p4 ∧ ((p2 ∧ p4) ∨ True)) ∧ ((p5 → (((False → p3) → p3) ∨ p1)) ∨ ((p2 ∨ p4) ∨ p3))) ∨ ((p1 → p3) ∨ True)) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221124088323379970857160138659 : (((True ∨ False) ∨ p5) ∧ (((p1 ∧ True) ∨ ((True ∨ p2) → p2)) → ((((False ∨ p3) ∧ (p5 → p4)) ∨ ((p4 ∧ p1) → (True ∧ True))) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253964715552231263508437325084 : ((p1 ∧ p5) → (((((p4 ∨ p3) → (p5 ∧ ((p4 → (True ∨ False)) ∨ (((p4 ∨ p2) → (p4 → p1)) ∨ (p1 → False))))) → p2) ∧ p3) ∨ p1)) := by
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
theorem thm_5_vars_758551826495442166050236755368 : (((p2 ∧ (((p5 → (False ∧ ((p4 → p1) ∨ ((((True ∧ p3) ∧ (True ∧ (p1 ∨ p1))) ∨ ((p4 ∨ p1) ∧ p5)) → p3)))) ∧ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308690909800881180552721809893 : (p2 ∨ ((p2 ∨ ((p2 ∨ (((p3 ∨ (p3 ∧ ((p1 ∨ (False ∧ False)) → (p2 ∧ p3)))) ∧ (((p1 ∨ p2) ∧ p3) ∧ True)) ∧ p1)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209309380414051897724469185892 : ((True → (True → ((False ∧ p2) ∧ False))) → (p1 ∨ (((True → ((p1 ∧ (False ∧ (p4 ∧ p4))) → (p5 ∨ p1))) → (p1 ∧ p5)) → (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217424809585127408598088131998 : (((p2 → (True ∨ False)) ∨ True) → ((((p1 ∨ False) ∧ p5) ∧ (p1 → (True ∧ ((((p5 ∧ False) ∨ True) → p1) → False)))) → ((p5 ∧ p4) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h17 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h18 := h12 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : (((p5 ∧ False) ∨ True) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h26 := h19 h20
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h28 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h29 := h12 h28
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h31 : (((p5 ∧ False) ∨ True) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h32
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- False on the left can always be used.
          apply False.elim h35
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h37 := h30 h31
      -- False on the left can always be used.
      apply False.elim h37
  case inr h38 =>
    -- False on the left can always be used.
    apply False.elim h38
  -- Conjunctions on the left can always be decomposed.
  let h39 := h2.left
  let h40 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h41 := h39.left
  let h42 := h39.right
  -- Disjunctions on the left can always be decomposed.
  cases h41
  case inl h43 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h44 =>
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h45 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h46 := h40 h45
      -- We need to get the right conjuct of h46 based on <expert-advice>.
      let h47 := h46.right
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h48 : (((p5 ∧ False) ∨ True) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h49
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- Conjunctions on the left can always be decomposed.
          let h51 := h50.left
          let h52 := h50.right
          -- False on the left can always be used.
          apply False.elim h52
        case inr h53 =>
          -- One of the premise coincides with the conclusion.
          exact h43
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h54 := h47 h48
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h56 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h57 := h40 h56
      -- We need to get the right conjuct of h57 based on <expert-advice>.
      let h58 := h57.right
      -- We want to use the implication h58 based on <expert-advice>. So we show its premise.
      have h59 : (((p5 ∧ False) ∨ True) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h60
        -- Disjunctions on the left can always be decomposed.
        cases h60
        case inl h61 =>
          -- Conjunctions on the left can always be decomposed.
          let h62 := h61.left
          let h63 := h61.right
          -- False on the left can always be used.
          apply False.elim h63
        case inr h64 =>
          -- One of the premise coincides with the conclusion.
          exact h43
      -- We have shown the premise of h58, we can now drive its conclusion.
      let h65 := h58 h59
      -- False on the left can always be used.
      apply False.elim h65
  case inr h66 =>
    -- False on the left can always be used.
    apply False.elim h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110711700769295817507519316931 : ((((((True → (((((p2 ∧ True) ∧ False) ∧ ((p5 ∧ (p5 ∨ (False ∨ True))) ∨ True)) → p2) ∨ p1)) ∨ p1) → p4) ∧ False) ∧ p3) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751273097534835348230462243882 : (((True ∧ ((False ∨ p3) ∧ (p1 → (p3 ∧ ((True ∧ ((p5 ∧ (p3 → ((p4 ∧ True) ∨ p4))) ∨ (p4 ∧ p2))) ∧ ((True ∧ False) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54511664022362011051542210891 : (((((p2 → p3) → True) → (p1 ∨ (p5 ∧ p3))) ∨ ((True → True) → (p4 ∨ (p1 ∨ (True ∨ (p3 → (True → (False ∧ (True ∧ p1))))))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114404408483249760285055482260 : ((((True ∧ (p3 ∨ (p1 ∨ (p4 ∧ False)))) ∨ ((p4 ∧ p4) → (p3 → ((p3 → p5) ∧ p5)))) ∨ (p5 → (False ∨ (p2 ∨ p5)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204014533340996248345473804610 : ((p4 → (((p2 ∧ p4) ∧ False) ∨ p4)) ∧ ((False → False) ∧ ((((((p1 ∨ (True ∨ (p5 → p2))) ∧ (p4 ∨ p2)) ∨ True) ∧ p2) ∧ p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669431288893463151187400043762 : (((((((False → p2) → p4) → ((p5 ∧ ((((False → False) → p3) → p2) ∧ (p4 ∨ p2))) ∧ False)) ∨ (False → p4)) ∨ (p1 → (False → p2))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_329492945691623624986483158631 : (True → ((p3 → p3) ∧ (p1 → (p2 ∨ ((((p1 → (p1 ∧ (True ∧ p3))) ∧ (p2 ∧ p3)) ∧ (p5 ∧ (False ∧ (True → True)))) ∨ (p1 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46893076684491634286446247491 : ((((((((((p2 → (p5 → (False → ((p4 ∧ False) → p5)))) ∧ True) ∧ p1) → p4) ∨ (False → p4)) → p3) → p4) ∨ p5) ∨ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346305435618762548679529673888 : (p3 → (((((p1 → ((True ∧ p3) ∧ ((p1 ∨ p3) → (p2 ∧ (True → (p5 ∨ p3)))))) ∧ (True ∧ p1)) ∨ (p1 → p5)) → p5) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215961105334332086412132327707 : ((p4 ∨ ((p3 ∨ False) ∨ p2)) ∨ ((p5 ∨ (((True ∧ p2) ∧ ((True ∧ (True ∨ p1)) ∧ (p2 ∧ (p2 ∧ False)))) → (False ∧ True))) ∧ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h7.left
    let h17 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41503177224555656365618191141 : ((((True ∧ (((p3 ∧ p2) → ((False ∨ p4) ∧ (p5 ∨ p2))) → p4)) → ((((p1 ∧ p5) → p3) ∨ False) ∨ (True ∧ (p1 → p1)))) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157786908444264584726707055609 : ((((p2 ∨ (True ∧ (p1 ∨ p3))) ∧ ((False ∨ (True ∧ False)) ∨ p3)) ∨ ((True ∨ (p3 ∧ p4)) ∨ p3)) ∨ ((p4 → ((p4 ∧ p4) ∧ False)) ∧ p4)) := by
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
theorem thm_5_vars_659968485949105170012254453941 : (((((((True ∧ ((True ∧ p4) ∧ True)) → ((((False → (p1 ∧ (p5 → p3))) ∨ p5) ∨ (p2 → p1)) ∨ False)) ∨ p2) ∨ p4) → (p2 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173994869601145283312660963785 : ((((p5 → True) ∨ (((False → ((False → p2) ∨ (p4 → p3))) ∧ p1) → p3)) → p2) → (((((p1 ∧ p3) ∨ p3) → (False ∨ False)) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251386444222516850901067523767 : ((p2 → p4) ∨ ((False ∨ (True ∧ p1)) → (p1 → ((p4 ∨ (p2 ∧ True)) → (p4 → ((p3 → ((p4 ∨ p3) → p5)) ∨ (p4 ∨ (p2 ∧ True)))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207654455729931815041461546221 : ((((p5 → True) ∧ (p4 ∧ p3)) → p1) → (((p5 ∧ p5) ∧ ((p2 ∧ p2) ∧ (p2 ∨ (((True ∨ False) ∨ p5) ∨ (p1 → (p1 ∨ False)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111961169131989339344614685209 : ((((((p2 → False) ∨ (p1 → p4)) ∧ (p2 ∨ True)) → (((p2 ∧ (False → False)) → ((p3 ∧ p5) ∨ p2)) → (p1 → p5))) ∨ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149360109910737501962631253002 : (((p5 ∨ p5) → (True ∧ (((p3 → p5) ∧ ((((False ∨ p1) ∧ False) ∧ p4) ∨ True)) ∨ ((p3 ∧ p5) ∨ p2)))) ∨ (True ∧ (True ∧ (True ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190191300541021729247928771729 : (((p1 ∨ (((p3 → p5) → p3) → (False ∧ True))) ∧ p4) ∨ (((((p5 ∧ p3) ∨ ((p5 ∨ p2) ∨ ((p2 → p5) → p5))) ∧ p5) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_1980322872373005111919618765 : ((p1 → (p3 ∨ ((p5 → (p5 → (p4 ∧ (p3 ∧ (False → p5))))) → (p4 ∧ (False → (p3 ∧ p4)))))) ∨ (((p1 ∨ True) → False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172184134247898555989712261847 : (((p4 ∨ (p1 ∨ (p4 ∧ (True ∨ (p3 ∨ (p2 ∧ p1)))))) ∨ (p2 ∧ (False ∧ p4))) ∨ ((p4 → p4) ∨ (p3 ∧ (p2 ∨ ((p1 ∧ False) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172590778593878175793901887625 : ((((p2 ∧ p4) → p3) → (p2 ∨ (((p3 ∨ p3) ∨ p2) → ((p5 ∧ p1) ∨ True)))) ∨ ((False → ((p3 → True) → ((p3 ∨ False) → p3))) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125763675548838622436453131967 : (((True → False) ∨ ((p5 ∧ ((p2 ∧ p3) ∧ ((True → False) ∧ (p5 ∨ (p5 ∨ ((p2 ∧ ((p2 → p3) ∨ p2)) ∧ p5)))))) ∧ p4)) → (False ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h18 := h14 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h22 := h14 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h29 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h30 := h14 h29
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h32 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h33 := h14 h32
          -- False on the left can always be used.
          apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664318251822089225898676382397 : ((((p2 ∨ (((((((True → (p5 → p5)) ∨ False) ∧ p3) ∧ (p3 → p3)) → True) ∧ p2) ∨ ((p5 ∧ p4) ∨ (True ∧ p5)))) → (p3 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59526750773515250680795060728 : (((p2 → p4) ∨ ((p1 ∨ ((False ∧ ((False ∧ p1) ∨ ((p4 ∨ p4) ∨ p1))) ∧ p5)) ∨ ((True ∧ ((False ∨ (False ∧ False)) ∨ p5)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86686987462411218914937797457 : (((p1 ∧ (p5 ∨ ((p1 → (False ∨ True)) → False))) ∧ (False ∨ ((False ∨ (p5 → (((False ∨ (False ∨ p4)) ∧ (p1 → p2)) ∨ True))) ∨ False))) → p5) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h19 : (p1 → (False ∨ True)) := by
            -- Implications on the right can always be decomposed.
            intro h20
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h21 := h13 h19
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259893145254268772268672534194 : ((p1 → p4) → ((True → p5) → ((True → p1) ∨ (True ∧ ((p4 → (((p5 ∧ p1) → ((True ∧ p3) ∧ p2)) ∨ ((p3 ∧ p3) → True))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178985508490021869181740620479 : (((p2 → p4) ∨ (p1 ∨ (p4 ∧ (((p4 → p3) → (p2 ∧ True)) → p1)))) ∨ (p3 → ((p3 → (p3 → (p2 → (p3 → p3)))) ∧ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158757289105909445213385440089 : ((p4 ∧ ((((True → p1) → p3) ∨ ((p1 → (False ∨ p2)) ∨ p3)) ∨ ((p5 ∨ (p1 ∧ p4)) → p3))) ∨ (((False ∨ (True → p2)) ∧ p3) → p2)) := by
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
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134711040893341103350477583447 : (((((p2 → p5) ∨ True) ∧ ((((((False ∨ p2) ∨ p1) → p5) ∧ p1) ∨ (p5 ∧ ((p4 ∨ p2) ∨ p1))) ∧ p4)) → p2) ∨ (p3 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49684232269322948995468864758 : ((((p3 → True) ∧ (p3 → (((True → (False ∨ False)) → ((True → False) ∧ p5)) ∧ ((p2 ∨ (False ∨ False)) → p1)))) → ((p3 ∨ p2) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40065824462817873405512185238 : ((((((p5 → p2) → ((((p5 ∧ p4) ∨ p2) ∨ ((p4 → (True ∧ (p4 ∨ False))) → p5)) ∨ ((p5 ∨ p1) ∧ p2))) ∨ False) ∧ p3) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303976606035708936174465967958 : (p1 ∨ (((p2 ∨ (p1 → p3)) → ((False ∧ (((p3 → (False ∨ p4)) ∨ p1) ∧ p3)) ∨ ((False → p4) ∨ (((p2 ∧ p4) → p4) ∨ p5)))) ∨ p2)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181378663677954870485760673854 : ((p1 ∨ (((False ∧ p1) → ((p1 → p1) → (p3 → p4))) ∧ (p1 ∨ p1))) → ((((True → True) → ((p5 ∧ True) ∨ p4)) ∨ (p4 ∨ p2)) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320446405391973842288023955966 : (p4 ∨ ((p4 ∨ False) → (((True → ((p1 ∨ p1) → ((False ∧ (False ∨ (p1 ∧ (p1 ∨ (False ∨ p4))))) ∨ p4))) ∨ p2) ∧ (p2 ∨ (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46093963972443179895584986133 : (((((True → ((p1 → True) ∨ p3)) ∧ ((p3 ∨ (False ∧ p3)) ∨ ((p3 ∨ p1) ∧ ((p1 ∨ False) ∧ (p3 → True))))) ∨ False) ∧ (True ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258564228248842856171297951687 : ((p5 ∨ p3) → (False ∨ (((p2 → ((p1 → (p3 → p1)) ∨ (p3 ∨ (True ∨ p5)))) → ((p5 ∨ ((p3 ∧ False) ∨ p4)) → p3)) ∨ (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697613978422176179609502631941 : ((((p2 ∨ ((False ∧ True) ∧ ((True ∧ True) ∨ ((p3 → p4) ∨ p2)))) ∧ (((p2 → (p5 ∨ ((p1 ∧ (False ∧ p3)) ∨ p4))) ∨ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218864215902377884801687254195 : ((p2 ∧ (p5 ∧ (p4 ∨ p2))) → (p1 → ((((p2 → (False ∨ (p1 ∧ (p1 → p3)))) ∨ (True → ((False ∨ False) ∨ (p1 ∧ p5)))) ∨ p1) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301062126410621665899206823916 : (False ∨ ((True ∧ ((p5 ∧ p3) ∧ (p3 ∨ ((True ∨ p1) ∨ p2)))) ∨ (p4 ∨ (((((p4 ∧ (p4 ∨ p3)) ∧ True) ∨ (p2 → p1)) ∧ p1) ∨ True)))) := by
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
theorem thm_5_vars_305557286662856058617779967552 : (p1 ∨ ((((p4 → p3) → ((p3 ∨ (False ∨ False)) ∨ True)) ∨ (p1 → False)) ∧ (p3 → ((False ∨ ((p1 → (p2 ∧ True)) ∧ (p5 ∧ p2))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178957777608277942257398389961 : (((False ∨ p3) ∨ ((((p2 → (True → (p2 ∧ True))) ∨ p4) → False) ∨ False)) ∨ (p2 → ((((True ∧ (p1 ∨ p1)) → (p3 → p5)) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27293657062913357900696654553 : (((True ∧ True) → ((((p5 → (p1 → False)) → ((False ∧ ((p1 → p3) ∨ True)) ∨ (p1 ∧ (p3 ∧ (p2 ∧ False))))) ∨ True) ∧ (False ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52986041321113545581827465967 : (((((p3 ∨ (p3 ∧ p2)) → ((p4 ∧ p1) ∨ p1)) ∧ (p4 → p5)) ∧ (((p2 → (p3 ∨ p3)) ∧ (False ∧ (p4 ∨ False))) ∨ (False → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316521160754418890736926654745 : (p3 ∨ (p2 ∨ ((p2 ∧ p4) ∨ ((False ∨ (p2 ∨ ((((p2 ∧ ((p4 → False) ∨ ((p3 ∧ True) → p4))) → (p4 ∨ p2)) ∨ p5) ∧ True))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347170281649133566764106130098 : (p3 → ((((False ∨ p3) ∧ p4) ∨ (True → (True ∨ (False ∨ (True → p4))))) ∧ (p5 ∨ ((p5 ∨ ((True → p5) → ((False ∨ p5) ∨ True))) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327855463393694968483853558154 : (True → (((((False ∧ p5) ∧ p3) ∧ p5) ∨ (p3 ∨ ((p4 ∧ (((((p4 → False) ∧ True) → (True → False)) ∧ True) → p5)) → True))) ∨ (True ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68209264934883389387266411272 : ((p3 → ((p3 → ((True ∧ ((True ∨ (p1 ∧ ((p4 ∧ p5) ∨ True))) ∨ ((p3 ∧ p1) ∨ (p3 → (p5 ∧ True))))) → (p4 ∧ p1))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225388875208200918078241235448 : (((p2 ∨ p3) ∧ p1) ∨ ((p2 → (p2 → p1)) ∨ (p5 → (p1 ∨ ((p3 → (((p3 → (((False → p2) → p5) → p3)) → p4) ∨ p5)) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53037116842454060203692664237 : (((((p4 ∨ True) ∧ p5) → ((True ∨ ((p4 ∧ p2) → p4)) ∨ p3)) ∧ (((False → p3) ∨ (p1 → (True ∨ ((p4 ∧ p5) → False)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227932933082933855355017541710 : ((p3 ∧ (False ∧ p4)) ∨ ((p3 ∨ (p4 ∨ p3)) ∨ ((p5 ∨ p5) ∨ (True ∨ ((True ∧ False) ∧ (((False ∧ p3) ∨ p5) ∧ (p4 → (p1 → p5)))))))) := by
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
theorem thm_5_vars_38534596993974915791994734068 : ((((((False ∧ ((p5 ∨ True) → p1)) ∧ (False → p4)) ∧ p2) ∧ ((True ∧ ((p5 ∧ (((False → True) ∧ p2) → p5)) → p1)) → p3)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300081932234686490907641950600 : (False ∨ (((p2 → ((True → (((((p3 → ((p5 ∧ p3) ∨ False)) → p4) ∨ p2) → (p2 ∧ p5)) → False)) ∧ (p1 ∨ p2))) → p5) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147472183847998298644559121269 : (((p1 ∧ (((p2 → (((p4 ∧ p2) ∨ p3) ∨ p4)) ∧ ((p5 ∧ p5) ∧ p5)) ∨ (True ∨ (p3 ∧ p5)))) ∨ False) ∨ (p1 → ((p5 ∨ False) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337377811934071331263286690751 : (p1 → (((p4 ∧ (p2 ∨ p1)) → (p2 ∨ ((p1 ∧ (p4 ∧ p1)) ∧ (p3 ∨ (p2 ∨ ((p5 → (True → False)) ∨ False)))))) ∨ (True ∨ (False ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303769825195221854095967798241 : (p1 ∨ ((((True ∧ p4) ∨ ((p1 ∧ ((False ∨ ((p1 ∨ ((True ∨ True) → p2)) ∧ (p1 ∧ (False ∧ p2)))) ∧ True)) ∨ (p2 ∨ False))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158060353304447247319810484921 : (((p5 ∨ (p5 ∨ ((p3 → p1) ∨ p4))) ∨ (p1 ∨ (((((p1 ∨ True) → True) ∧ p1) → True) ∧ False))) ∨ ((p4 → (p5 ∨ p4)) ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184345706064170834591313480471 : (((p3 ∧ ((p4 → p1) ∧ (p2 ∨ ((p5 ∨ p5) → False)))) → p5) ∨ (True ∨ ((False → True) ∨ (True ∨ (False → ((p1 → p3) → (p5 ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780794533622205259259498695299 : (((p2 ∨ ((p1 ∧ ((p5 ∨ False) → p2)) ∧ ((p2 ∨ ((p1 ∧ p2) ∧ ((p5 ∧ True) → p5))) → (p5 ∨ (p3 → ((p2 ∧ p3) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



