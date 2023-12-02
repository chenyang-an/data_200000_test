variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55100132724395265491564303542 : (((p4 → ((p2 ∨ p5) ∧ (True ∧ p5))) ∧ ((p5 ∨ ((((p4 → True) ∨ p4) → ((p3 ∨ False) ∨ p2)) → ((p5 ∨ False) → p3))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676697248136333430269434424162 : ((((p5 ∧ ((p4 ∨ False) ∧ (((p3 → (p5 → (True ∧ (p1 ∨ (p2 → False))))) → (False ∨ p1)) ∧ p4))) ∧ (False ∨ ((p2 ∧ False) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157244210045839695815954417415 : (((((p4 ∧ p1) ∧ ((p5 ∧ (p1 → p4)) ∧ p3)) → (((p4 ∧ p3) → (p5 ∧ p5)) ∧ p5)) → p5) ∨ ((p1 → ((False → False) ∨ p3)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753939833603688596092318113219 : (((False ∧ ((False → (p3 ∧ ((True ∧ True) → True))) ∧ (((p1 → p1) → ((p4 ∨ (p1 ∧ (p2 → p4))) ∨ (p3 ∨ (p3 → False)))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37289816649516929809059143115 : ((((p4 ∨ (((p2 ∧ (False ∨ False)) ∨ (((p2 → False) ∧ p1) → (p3 ∨ (p4 → (True → p5))))) ∨ ((p4 ∧ p1) ∨ p5))) ∧ True) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39265203707425836004436335092 : (((False ∧ (p3 ∧ ((p4 ∨ (p4 ∧ p4)) ∨ ((p4 ∨ (False → p2)) → ((((p4 → p4) → (p3 → (p2 ∨ p1))) ∧ True) ∨ p1))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655270318317546448195372970612 : (((((((p4 → p1) → (p5 ∨ p3)) → (p4 ∧ (p3 ∨ ((((p4 ∧ True) ∨ p2) → (p5 ∧ False)) ∧ True)))) ∧ (p4 ∧ p3)) ∨ (p4 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_147624397429766266186809924486 : ((((((True → ((p4 ∨ p1) ∨ ((True ∧ (p4 ∨ (p5 → p2))) ∨ p4))) → (False → p2)) → p4) → p1) → False) ∨ (p4 → ((p5 ∨ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67512545578205214717810483074 : ((p1 → ((False → (False ∧ (((p1 → True) → p3) ∨ p1))) → ((((False ∧ False) ∧ ((p3 → (p5 ∨ p4)) ∧ p4)) ∨ (p5 → p1)) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243417385081647075223434299964 : ((p5 → True) ∧ ((p3 ∧ (p1 ∧ (p4 ∧ ((p2 → ((((p2 ∧ p5) → p2) ∧ p5) → (p1 ∨ p1))) → p5)))) ∨ ((True ∨ p2) ∨ (p1 ∧ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259475380591436971610187178934 : ((False → p4) → (False ∨ ((((p1 → False) ∧ p4) → p5) ∨ (((((p1 ∧ (False ∧ (False → p2))) ∧ p2) → p3) → (p3 → False)) → (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783709664103224872043389101897 : (((p3 ∨ (((p5 ∨ (p1 ∨ False)) ∧ (False ∨ p5)) ∨ ((p5 ∨ True) → ((p1 → (True ∨ (((False ∨ p5) ∧ p2) ∧ (False ∨ False)))) ∨ p3)))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56399328947598267506164480205 : ((((p4 ∧ (p5 ∨ p1)) → p2) → (((((p1 ∨ (p1 → p5)) ∨ p2) ∧ (p3 ∨ (False ∧ p1))) → ((p2 → False) ∧ False)) ∨ (True ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352014435100272929228395842450 : (p4 → ((p2 ∨ (((p3 ∨ True) → True) → (p1 ∧ p3))) ∨ (False → ((p2 ∧ (((True ∧ p1) ∧ (p5 → p3)) ∨ ((p1 ∨ p5) ∨ False))) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h2
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h2
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h2
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156985066260789435018896156098 : ((((((p1 ∧ p3) → p5) ∧ (p1 ∧ p2)) ∧ (True ∨ (p2 ∧ (p1 ∨ ((p4 ∨ p1) → p2))))) ∨ p1) ∨ (p4 → ((False ∧ (True ∧ False)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751391634221514397308937203590 : (((True ∧ ((p4 → p5) ∨ (p5 ∧ (((False ∧ (False ∨ (((p2 ∧ (((p2 ∨ p3) ∧ True) ∧ p4)) ∨ False) ∧ False))) → p4) → (True ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626664025884575122844277834474 : ((((p4 → (p4 → ((((p4 → p1) → (p1 → (False → ((p2 ∨ p3) ∧ (p3 ∧ (p3 ∧ p1)))))) → False) ∨ ((True → p4) ∨ p3)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119397769485260319241361097553 : ((p4 → ((p4 → ((p3 → p2) → (p1 ∨ (p3 → ((p5 ∧ (True ∧ (((p3 → (p2 ∧ False)) ∨ p1) ∧ p3))) ∨ p3))))) ∧ p4)) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66229276684599387542365312424 : ((p5 ∨ (((((p2 ∨ p4) ∧ p1) ∨ p3) → (p3 ∨ p5)) ∧ (((p1 ∨ p1) ∧ ((p3 → (True → p4)) → False)) ∨ ((True ∧ p1) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134320244284554446295277657017 : (((p1 ∧ (((p3 → (False → ((p4 ∨ p3) ∨ p5))) ∧ (p5 ∧ p1)) ∧ (p3 ∨ (p1 ∨ ((p4 ∧ p3) ∨ p5))))) ∨ True) ∨ ((p5 ∨ False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246517838819840426000198464866 : ((p5 ∧ p1) ∨ (((((((p1 → p2) ∨ p3) ∧ p2) → ((p1 ∧ True) → p2)) ∨ p4) ∧ p2) → (((p4 → p3) ∨ p3) ∨ ((False ∧ p5) → p3)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356017688743887983012496784429 : (p5 → ((((p1 → (((p1 ∨ ((p3 ∧ p3) ∧ (p1 → (False ∨ p4)))) ∧ p5) ∨ p1)) ∨ (False ∨ True)) → p4) ∨ (True ∧ (False → (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148058081560310994336309377572 : (((p4 ∨ ((p3 → (p3 ∧ p2)) → (True ∧ ((((True → p4) ∧ p4) ∨ p5) ∨ (False → p2))))) ∨ (p4 ∨ p3)) ∨ ((p3 → (True ∧ False)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299311194366069747348010161743 : (False ∨ (((True ∧ (True ∨ ((p4 → p1) → (p4 ∨ False)))) → (((((p4 ∨ p3) ∧ p5) → (p1 → ((p4 ∨ p4) ∧ True))) → p4) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61821342337451547333260728559 : ((p2 ∧ (((False ∨ False) ∨ ((((True → (p1 ∨ p3)) ∨ p5) → ((p5 → (True ∧ (((p5 → False) → p4) → True))) → p2)) → False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774282917343036373088471654804 : (((False ∨ (((p4 → ((((p2 → ((p3 ∨ p3) ∨ p2)) → True) ∨ p1) → (p5 ∨ ((p1 ∧ True) ∧ True)))) ∨ p1) → (p3 ∨ (p5 ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792252130283283406815397305042 : (((True → (((p4 ∨ ((False ∧ p1) ∨ p5)) ∧ (((True ∧ True) ∨ ((p1 → (True ∧ p4)) ∨ p1)) ∨ p2)) → (p1 ∨ ((True ∨ False) → True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h29
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h30 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h30
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h32
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732262653281489351064994671063 : ((((False ∧ True) ∧ ((((p3 ∧ p2) ∨ p4) → p3) ∧ (True → ((p4 → (((False → True) → (p4 ∨ p5)) → ((p4 ∨ p3) ∨ p2))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184082655531596744042983435572 : ((((p3 → (False ∧ (False ∨ p4))) → (p2 ∧ (p2 ∧ p3))) ∨ p1) ∨ (((((p4 → p5) ∧ p4) ∧ ((p4 ∧ p1) → (False ∨ p2))) ∧ p5) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3004923358013172963891364460 : (((p1 ∨ p2) ∨ p5) → (((p4 ∨ (False ∧ p2)) ∨ p2) ∨ (p4 ∨ (((p4 ∨ p3) → p3) → ((False → p5) ∨ (p5 ∨ (p4 ∨ p3))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184100355775578412778234656441 : ((((p3 ∧ p1) ∧ ((p2 ∨ (p2 ∨ False)) → (p3 ∨ p1))) ∨ p2) ∨ (p1 → ((((True ∧ ((p1 ∨ p4) ∨ False)) ∨ p5) ∧ (True ∧ p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h4.left
        let h11 := h4.right
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h4.left
        let h14 := h4.right
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219368090232199919443183070363 : ((p3 ∨ ((p5 ∨ p5) ∨ True)) → (p1 → (((((False ∨ ((True → (p2 ∨ (p2 ∨ (p4 ∧ False)))) ∧ p2)) → True) ∧ False) ∨ p3) ∨ (p1 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135779914891942645473554403745 : ((((p2 → (p5 ∧ (((p5 → ((False → p3) → False)) ∧ p5) ∨ p4))) → False) → ((p2 ∨ (p3 → p4)) ∨ (p1 ∨ True))) ∨ ((p1 ∨ p3) ∨ p4)) := by
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
theorem thm_5_vars_257215669136599428821070424065 : ((p2 ∨ p2) → ((p3 ∨ (False ∧ p5)) ∨ ((False ∧ p5) → ((((False ∧ (p4 → p2)) → (True ∧ p1)) ∨ p3) ∨ (((p5 → True) ∧ p2) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350241565585048593216456026504 : (p4 → (((p5 → p4) → (p4 ∧ (((((p2 ∧ p5) ∨ (p5 ∧ p3)) ∨ (True → (p5 → p2))) → (True ∧ p5)) ∧ ((False ∨ True) ∨ p2)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801159628712698499647178111378 : (((p2 → ((True → (((True ∨ p5) ∨ False) ∧ (p4 → ((p1 ∨ ((p2 ∧ p2) ∨ (p4 ∨ p5))) ∧ p1)))) ∨ ((p3 ∨ (p4 → p1)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57579551129589552108870413015 : ((((p3 ∨ p2) ∧ p2) → (((False ∨ False) ∨ (p1 ∧ False)) ∧ ((p1 → (((True ∧ (p5 ∨ True)) ∨ p2) → p2)) ∨ (p5 ∧ (True ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149716934705366377339781356469 : ((p5 ∧ (p3 → (((p2 ∨ (p4 → p3)) ∨ True) → (((p3 ∨ p2) ∧ (p4 → p5)) ∨ ((p4 → p2) ∧ p2))))) ∨ ((False → (True ∨ p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149241603716305776480247944640 : (((False ∨ p1) ∨ ((p2 → (p5 ∧ (((True → p2) ∧ ((p5 ∨ (p5 ∨ p1)) ∨ True)) → (p2 ∨ False)))) → p3)) ∨ ((p5 ∨ p2) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113665887150238503486245662176 : ((((((p4 ∨ p5) ∨ (((p4 → p3) → p1) ∨ ((p4 ∨ (((p2 ∧ True) ∧ False) → p5)) ∨ p1))) → p4) ∨ p5) → (True ∧ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158268408979703202673811698390 : (((False ∨ (p3 ∧ p1)) ∨ (((p3 ∨ (False → p1)) → (((p3 ∧ True) ∧ p3) ∧ (p1 ∨ p5))) ∨ True)) ∨ (((p1 → p2) → p2) ∨ (p3 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241394433245055896764715946045 : ((False → p1) ∧ ((((p5 ∨ False) → (((((p4 → p1) ∧ (((False → p2) → p4) → p5)) → (True → (p3 ∧ p2))) ∧ p4) ∨ p5)) ∨ p1) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163158980248023560366769806568 : ((((p5 ∧ ((p5 → (p1 ∨ p5)) → (True ∨ p1))) → p5) → (((p4 ∨ p3) ∨ p5) ∨ True)) ∧ (((p4 ∧ (p4 ∨ p2)) ∨ (p2 ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801034736393225268780917322111 : (((p2 → ((((p5 ∨ p3) ∨ (p5 → (p4 ∧ (p5 ∨ p2)))) ∨ ((p5 ∨ p3) ∨ ((p5 → (p2 → False)) ∧ p2))) ∨ (False → (True → p1)))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112059755692723065924916734585 : ((((True ∨ p1) ∧ ((((p5 → p3) → (p2 → (True → (((p2 ∧ (p4 ∨ p2)) ∧ p1) → p5)))) ∧ (p5 ∧ False)) ∧ p2)) ∨ p1) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632749706754164265810693249737 : ((((((((((p1 ∧ (p2 ∨ p4)) ∨ p2) → p4) ∧ (((p5 ∧ True) → p5) ∧ (p4 ∧ p1))) → (p5 → p5)) ∧ p1) ∧ (p5 ∨ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137462262146715827576220564143 : ((p4 ∧ (p2 ∧ (True ∧ (((p1 ∧ p2) → p1) → (False ∨ ((p4 ∨ ((p3 → False) → False)) → ((p5 → False) ∧ False))))))) ∨ ((p3 → p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208593233850838762242223436155 : (((p2 → p2) → (p3 ∨ (False → p5))) → (((p3 ∧ (p2 → (p3 ∧ (p4 → p4)))) ∧ True) ∨ (((p2 ∨ p4) ∧ p4) ∨ ((True ∨ p1) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_179929096100070175872118180772 : (((((p5 → (False ∨ (p1 ∨ False))) ∨ ((p1 ∨ False) ∨ p2)) → p3) ∨ p1) → (p1 → (((p4 → p2) ∨ p2) ∨ (p3 → (True ∨ (p1 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49010803437760285991770317367 : (((((p2 ∨ ((p3 ∧ p5) → ((((p2 → (p4 ∧ ((True ∧ p5) ∨ False))) → p1) ∧ True) ∨ p2))) ∨ False) → p5) ∨ (True ∨ (p4 → p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748079284083327596322098363194 : ((((p1 → p2) → ((((((True → (True ∧ p3)) ∧ p2) ∨ (((False → p3) → True) ∨ False)) → (p3 → p3)) → True) → (p3 ∨ (True → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56699172984644789954267022740 : ((((p1 ∧ p5) ∨ True) ∧ ((p1 ∧ ((True → False) → ((p2 ∨ (True ∨ True)) ∨ (((p2 ∨ p5) → True) ∧ ((p2 ∨ True) ∧ p2))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69358234464579282167048757577 : ((p5 → (p4 ∨ ((((((p5 → ((((((True → False) ∨ p5) → p2) → p4) ∨ True) ∨ False)) ∨ p5) ∨ True) ∨ p1) ∨ p4) ∧ (p2 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132792275279415588914678570042 : ((p2 ∨ ((((p3 ∨ (p5 ∨ False)) ∧ p3) ∨ (p5 ∧ (False ∨ ((p1 → (p5 ∧ (False ∨ p4))) ∧ (p3 ∨ True))))) ∨ True)) ∧ (True ∨ (False ∧ p2))) := by
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
theorem thm_5_vars_766197624338505772633618423046 : (((p4 ∧ ((True ∧ False) ∨ ((((p3 ∨ p4) → ((p5 → p1) ∨ (p3 ∨ ((((p1 ∧ False) → p5) → False) ∨ True)))) ∧ (p4 → p1)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351234790837203906525598469312 : (p4 → (((((p2 → (p3 ∨ False)) ∧ (True ∧ (False → (False ∨ True)))) → p1) ∧ ((p3 ∨ p1) ∨ ((True → p2) ∨ p1))) ∨ ((False → p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57967115231714063854346238966 : (((p2 → (p5 → p5)) → (p5 ∧ (p3 → (p1 ∧ ((p3 ∨ False) ∨ ((p2 ∧ p5) ∧ ((False → (((p5 → p5) ∨ p2) → p5)) → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232940337664035953914059248484 : ((p3 ∧ (p2 ∨ p1)) → ((((p4 → (p4 → False)) ∨ (True ∧ p4)) ∨ (False ∧ ((False ∨ p1) → ((p3 ∨ (p5 ∧ p1)) → (p2 → p4))))) ∨ p3)) := by
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
theorem thm_5_vars_158599608597746963571074597139 : ((False ∧ (((((p4 → ((p4 ∧ p4) ∧ ((p1 → p2) → p3))) → False) ∧ p1) → (p2 → p1)) → p1)) ∨ ((p1 → (p4 ∧ False)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353747335442829787231331265726 : (p4 → (True → ((p1 ∨ p4) ∧ (((((False ∧ p5) ∨ p1) ∧ ((False ∨ (True → (True → p3))) ∧ p3)) ∧ p5) ∨ (((p5 → True) → p3) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344495727025154637690218852108 : (p2 → (True → (((p2 ∧ p3) → ((p2 ∧ p5) ∧ False)) → (((p2 ∧ ((p4 → p5) ∨ (((p5 → p1) ∧ (False → p2)) ∨ True))) ∨ p2) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51227416927887566351157727527 : ((((True → ((p1 → True) → False)) ∧ (p5 ∨ ((p2 ∧ (True → (p5 ∧ (p5 ∨ p4)))) → p5))) ∨ ((False ∨ (p4 → False)) ∨ (p5 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116256553224865699955937761077 : (((False ∧ (p3 ∧ p3)) ∨ (False ∧ ((True → (p4 → True)) → (((((((p5 → False) ∧ p5) → True) ∨ p2) ∧ p5) ∨ False) ∧ p1)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319690546040912530642667346482 : (p4 ∨ ((p5 → (((p1 ∧ (p5 → p4)) ∨ False) ∨ p2)) → ((p4 ∨ p1) → ((True ∧ ((p3 ∨ p5) ∧ False)) ∨ ((p3 ∨ p3) ∨ (False → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329742804087504828832724047534 : (True → (True ∧ (((((False ∧ p4) → ((p4 ∨ (p1 ∨ p3)) → p3)) ∧ ((p3 ∨ (p3 → p1)) ∨ (((p4 ∧ p4) ∧ p3) ∨ True))) ∨ False) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h2.left
      let h10 := h2.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h2.left
      let h13 := h2.right
      -- False on the left can always be used.
      apply False.elim h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61575799936054856416178255475 : ((p1 ∧ ((p3 ∨ (True → (p2 → True))) ∧ ((p5 ∧ ((p4 ∧ (p1 ∨ False)) ∨ p3)) ∨ (((False ∧ p5) → False) ∨ ((p3 ∧ p3) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42610734028697645159242857931 : (((p3 ∨ ((p4 ∨ ((True → (((p3 ∧ False) ∨ (((p1 → p3) ∨ p2) ∨ (p1 → p4))) ∧ p1)) ∧ ((p2 → True) ∨ p4))) ∨ True)) ∨ p5) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164849356336029455258224010434 : (((p5 ∧ ((p1 → False) ∨ (((p1 ∨ (p4 ∧ (True ∨ p1))) ∧ (p5 ∨ p4)) → False))) ∨ True) ∨ (True ∨ ((p4 ∧ p5) ∧ (True ∧ (p5 → p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317093174831341593955871264824 : (p3 ∨ (p5 → ((((False ∧ ((True → (p4 ∧ p4)) ∧ (((p2 ∨ ((p2 ∨ (p1 ∧ p5)) → (p1 ∧ True))) ∨ True) ∧ False))) ∨ True) ∧ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327087225918359362621644569377 : (True → ((((p1 ∧ True) ∧ True) → ((True → (((p4 ∨ (((True ∧ (p3 ∧ p4)) ∧ True) ∨ (p5 ∧ False))) → p4) ∨ (False → p4))) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636631808174516839510755197828 : (((((((False ∨ (p1 ∨ p4)) ∧ (p2 ∧ ((p3 ∨ (True → p3)) ∧ p5))) ∨ p4) ∨ ((p3 ∨ p4) ∨ (p5 ∧ ((False → p4) ∧ True)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225228655633935173138573751586 : (((p5 ∧ p2) ∧ p5) ∨ ((p2 ∨ ((p4 → (p1 ∧ False)) ∧ ((p4 ∨ (p3 ∧ True)) ∧ (((p1 → (p3 ∨ p5)) → (p5 ∧ p5)) → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115445326338045386833273427733 : ((((p1 → ((p3 ∧ p4) → False)) → (p2 ∨ p5)) ∨ (True ∧ (((p3 ∧ (True → p1)) → p1) ∨ ((p2 → False) → (p2 ∧ False))))) ∨ (True ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173671145840344049455443210263 : ((((((p1 ∧ p4) ∧ ((p1 ∨ ((p5 → False) ∨ p5)) ∨ p4)) → p4) ∨ p3) ∨ True) → (((p5 ∨ ((True ∧ True) ∧ p3)) ∨ p2) ∨ (False → False))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691507840550643187613221528751 : (((((False → True) → (((p1 ∨ p4) ∨ (((p1 → p1) ∧ p4) ∧ p2)) ∧ (p2 ∧ False))) → (p2 ∨ ((p1 → False) → (p3 ∨ (p2 ∨ p2))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606600538640796914567088539916 : (((((((p3 ∧ p1) → ((((False ∨ p5) ∧ (p5 ∧ ((p1 ∨ (p3 → p2)) ∨ (False ∨ (p5 ∨ p5))))) → p4) → p5)) → p3) ∧ True) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_171599778081700181735588174235 : ((((p1 ∨ ((p1 ∧ (p2 ∨ p5)) ∧ p4)) ∧ (False → (p2 ∧ (True ∧ p4)))) ∨ p2) ∨ (p1 → (((p5 ∧ (False ∧ p2)) ∧ (p1 → p5)) → False))) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136460471772007032936226063868 : (((p2 → ((p3 ∨ p2) → p2)) → (((p1 → ((p2 ∧ p3) ∨ (p5 → True))) ∧ p1) → (p5 ∨ ((p4 ∨ p5) → p2)))) ∨ ((False → False) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134854755286620533939804914564 : (((p5 ∨ (p2 → ((p3 → (p4 ∨ True)) ∧ (((True ∨ ((p3 ∧ ((True ∨ p3) ∧ p3)) → p4)) ∨ False) ∨ p2)))) → p4) ∨ (False → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39950128420812220885612586787 : (((p4 → ((p2 → ((((p4 → p3) ∨ (p1 ∨ False)) ∧ p5) ∨ (p1 → ((p3 ∧ p5) ∨ (p5 ∨ (False ∨ (p3 ∨ p2))))))) ∨ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244147880085868578355807520848 : ((True ∧ p4) ∨ ((p3 ∨ (((p1 ∧ ((p2 ∨ (p4 ∧ (p4 ∨ p3))) ∧ p4)) ∨ False) ∨ (p3 ∧ p3))) ∨ (p4 → ((False ∧ (p1 ∧ p5)) → p3)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328531559745722529895958949517 : (True → ((p2 ∧ ((p3 ∧ p5) ∧ (((True → p5) ∨ (p5 → ((True → False) → p3))) ∨ p2))) ∨ ((p4 ∨ p4) → (((p1 ∨ p4) → p4) ∨ p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114899745193187132945066914194 : (((p1 → (p1 → ((p4 ∧ (p1 ∧ ((p3 ∨ False) ∧ p2))) → (p5 ∨ p5)))) ∨ (((p2 → p5) ∧ True) ∧ (p3 ∧ (p5 ∧ p2)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233034441972989064717878859981 : ((p4 ∧ (p5 ∧ True)) → (((p2 → ((True → ((p3 ∨ ((p1 ∨ p4) → p1)) ∧ (p5 ∧ True))) → p3)) ∨ ((False ∨ p5) ∨ p3)) ∧ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811414145020485426747512637389 : (((p5 → (p2 ∨ (False ∨ ((p1 ∧ p4) ∧ (False ∨ ((p3 ∧ p3) ∨ (p3 ∨ ((p3 ∨ p1) ∧ ((True ∧ p2) ∨ ((p4 → p3) ∨ p1)))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76636286733902751098073433492 : ((((p1 ∨ (p3 ∨ ((((((False ∧ p3) → p2) ∨ p2) → p1) ∧ p4) ∧ ((p4 → True) ∨ True)))) → ((p1 ∨ (p3 ∨ True)) ∨ p4)) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (p3 ∨ ((((((False ∧ p3) → p2) ∨ p2) → p1) ∧ p4) ∧ ((p4 → True) ∨ True)))) → ((p1 ∨ (p3 ∨ True)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h2
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697839757786567712939561387960 : (((((((p5 ∧ ((p2 → False) ∨ p5)) → (p5 → p2)) ∧ False) ∧ p4) ∨ (False ∨ ((True ∧ (((False → p2) ∨ p3) ∧ False)) → (p5 ∧ p4)))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142740708065772455640852359150 : ((p2 ∨ ((p3 → ((False ∧ p3) ∨ True)) → (p1 ∧ (p1 → (((((p2 → p4) → p3) ∨ False) ∧ (p2 ∧ p5)) ∧ False))))) → (p4 → (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66361067651505250206872664012 : ((p5 ∨ (False ∨ ((((p4 → (p1 ∧ ((p4 ∨ p4) ∧ p5))) ∧ p1) ∨ (p1 ∧ True)) ∨ (p1 → (p1 → ((p4 ∨ p3) ∨ (p5 → p1))))))) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781552118434083198070332397724 : (((p2 ∨ (False ∨ ((p1 → (((p4 ∧ (p3 ∨ ((((p1 ∧ (p3 ∧ True)) → p4) → False) ∧ p4))) ∨ (p4 → p2)) → (p5 ∨ p5))) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309340957328528413230378282919 : (p2 ∨ ((((p3 → p4) → (p3 ∨ (((p3 ∧ ((p1 ∧ p1) ∨ (p4 ∨ False))) ∧ True) ∧ (p1 → True)))) ∨ (True ∨ (p3 → p1))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322328019404168480858850411703 : (p5 ∨ ((((((p1 ∧ (p1 ∧ ((True → p5) → p1))) ∧ (p4 ∨ p4)) ∨ (p3 → (((p3 → p3) ∧ True) ∧ p1))) → False) ∨ (True ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324030251683850798189102421774 : (p5 ∨ ((True ∧ (p3 ∨ ((True ∧ ((p5 → p2) ∨ ((p4 ∧ True) ∨ p1))) ∨ True))) → (p5 → ((p4 → ((False ∧ (False → True)) ∨ True)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h17
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739670395557652650720708466422 : ((((p5 ∧ p5) ∨ (p2 ∧ ((p2 ∧ ((((((p1 → (p3 ∧ (p2 → (False → True)))) ∨ p5) → p2) ∧ (p5 ∧ p1)) ∧ p3) ∧ p5)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55909182970167291269913460017 : (((p5 ∨ ((p3 ∨ p1) ∨ p4)) ∧ (((p4 ∧ (p2 ∨ (p1 ∨ ((p2 → p2) → ((True ∧ (True → p3)) → p4))))) → p3) ∨ (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19548384151614904884860998240 : (((((p4 ∨ ((False ∧ p2) ∧ (((False → p4) ∨ p3) → False))) ∨ p1) ∨ (False → p3)) ∨ (p5 → ((p2 ∧ ((p4 ∧ p4) ∨ p3)) → False))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_700136384020243220037968411543 : (((((False ∨ True) ∧ (True ∧ (p2 ∧ ((p4 ∧ p5) ∨ (True → p3))))) → ((p5 ∧ False) ∨ ((p4 ∧ ((p1 ∨ True) ∨ (True ∨ p3))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45309429443761861512291845667 : (((p3 ∧ ((((p5 ∧ (p4 ∧ (p4 ∨ p4))) ∨ (True ∨ ((p3 ∧ p4) ∨ p5))) → ((p2 ∨ (p2 → (p1 ∨ False))) → True)) ∨ p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638603218181348213072252473661 : (((((True → ((p5 ∨ p5) ∧ (p1 → p4))) ∨ ((True ∨ p2) ∧ (((((p4 → False) ∧ True) → (p5 ∧ (True → False))) ∧ p4) ∨ False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149827625040412545818834444202 : ((p1 ∨ ((False ∨ ((p4 ∧ (p2 ∧ p5)) ∧ ((p5 ∨ ((p3 ∨ (p5 ∧ False)) → p1)) ∨ p1))) ∨ (True → p1))) ∨ (((p2 ∨ False) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



