variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746524851383177498789143105812 : ((((p2 ∨ p4) → (p5 ∨ ((p1 ∧ True) ∧ ((((True ∧ False) → (p5 → (p3 → ((False → ((p3 ∧ p3) → True)) ∧ p3)))) → p4) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758014143906402160001660358265 : (((p1 ∧ (True → (p5 → (((p2 ∨ p4) ∧ (p1 ∧ (((p1 → False) → p5) ∧ (p1 → (((p2 ∧ p3) → p5) ∧ p3))))) ∨ (p5 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69039028600892074004305996670 : ((p5 → (((True → ((((((p1 ∨ (p2 → p1)) ∧ False) ∧ p4) → False) ∧ p4) ∧ p5)) ∧ ((p1 ∧ (False ∨ (p5 ∨ p4))) ∧ p3)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181407799328480035375424390502 : ((p2 ∨ (((True ∨ (p2 → p1)) ∨ (p5 ∨ (p3 ∧ p2))) ∧ (p3 ∨ p4))) → ((p2 ∨ ((False ∧ p5) → True)) ∨ ((False ∨ (False → p4)) ∧ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173168462871016035277633626185 : ((p4 ∨ (((((p3 → (p4 → p2)) ∧ (p4 ∨ False)) ∨ p3) ∧ (p5 → p3)) ∨ False)) ∨ (((p5 → (True ∨ False)) ∨ (p5 → p1)) ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190600370071527871792742625493 : ((((False → p5) ∨ (True ∨ (p1 → (p5 ∨ p1)))) → p2) ∨ (((p5 ∨ False) ∧ (p3 ∨ p4)) ∨ (((False ∧ False) ∧ p4) ∨ ((p5 ∧ p5) ∨ True)))) := by
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
theorem thm_5_vars_258095966405644711899614612751 : ((p4 ∨ p3) → (((((p3 → (((p3 → p3) ∧ ((p2 ∧ (p3 ∧ False)) ∨ p5)) → (p1 ∨ p4))) ∨ p5) ∧ (p3 → p3)) ∨ (False → p2)) ∨ p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48052263293236582588142038749 : ((((((True ∨ p3) ∨ (p5 → p3)) → (False ∧ False)) ∧ ((((p4 ∨ p5) → (p2 ∧ p1)) → (p2 ∧ False)) → (p1 ∧ p5))) → (False ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∨ p3) ∨ (p5 → p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245294170859905015536890559051 : ((p2 ∧ p2) ∨ (((p4 ∨ p5) → (((p2 ∧ ((((p3 ∨ p2) → ((p4 → (p2 → p4)) → p2)) ∧ p2) ∨ p3)) → p3) → p4)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138445640604957517955204545867 : ((p5 → ((False ∧ p1) ∧ ((((p2 → p2) → (p3 ∧ p4)) ∧ ((p3 ∧ p2) ∨ (True → (True ∨ p5)))) ∧ (p3 → p1)))) ∨ ((False ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134546093296094290509897631590 : (((((((False ∨ p1) ∨ False) → (p2 ∧ p1)) ∨ (p4 ∧ ((False ∨ (False ∨ p1)) ∨ ((p2 ∨ p3) → p3)))) → p4) → False) ∨ ((p1 ∧ p2) → p2)) := by
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
theorem thm_5_vars_119222058257460069249068399753 : ((p2 → ((False ∧ (p1 ∨ p4)) ∧ ((((p5 → (p4 ∧ True)) ∧ ((False → False) ∨ False)) ∨ p3) ∧ (p2 ∨ (p1 ∧ (p3 ∨ p5)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468076742118598697989946136186 : ((((p4 ∧ ((p2 ∨ p5) ∧ ((p5 ∧ (((p3 → p2) → p2) → p5)) ∨ True))) ∨ (((False → (p1 → p1)) ∨ (False ∨ True)) ∧ (False ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684573365278121872564722883816 : (((((False ∧ ((p5 ∨ p2) ∨ p3)) ∨ (p3 ∨ (p1 ∧ (False → ((p4 → (p2 ∨ True)) ∨ p4))))) ∨ (True → (p4 ∨ (p2 → (False ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243779303560142947963716945761 : ((p5 → p5) ∧ (((p3 → (p5 ∧ ((p3 → (p2 ∨ p4)) → p2))) ∨ ((p1 ∨ (p1 → p2)) ∨ (False → (False → p4)))) ∨ ((p5 ∧ p1) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156672168694419231696139415993 : (((((p5 → p1) ∨ ((p3 ∧ (p3 → (p2 → p2))) → ((False ∨ p3) ∧ p4))) ∧ (p2 ∨ p5)) ∧ p2) ∨ ((False → (True ∨ False)) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797476697527563366594059487331 : (((p1 → ((p3 → (((((((p1 ∨ p3) ∨ True) → ((p2 ∧ False) ∧ False)) ∨ True) ∧ p4) ∨ (p4 ∨ (p3 → p3))) ∨ (True → p1))) ∨ False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336390334266434704206465491664 : (p1 → ((p2 ∧ ((p5 ∧ (p1 → ((p5 → (((p3 → p5) ∧ ((p4 ∧ False) ∧ ((p2 ∧ (p4 ∧ p4)) → False))) ∨ p5)) ∧ True))) ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218475537661563368768330862141 : (((True ∨ p3) → (False → p2)) → ((False ∧ (((False ∨ (((True ∧ (False → (p1 ∧ (p1 ∧ (p4 → p3))))) → p2) ∧ p2)) ∧ p1) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115140404299329261757603748708 : (((True ∧ (((p1 → p2) ∨ (p1 ∨ (p3 ∧ p4))) ∧ (p5 ∨ False))) → ((((((True → p5) ∧ p2) ∨ p1) ∧ True) → True) → p4)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215384004244862332074935655316 : ((p2 ∧ (False ∧ (p3 ∧ False))) ∨ ((((True ∧ (True ∧ (p1 ∨ True))) → False) → p5) → ((p3 ∨ (((True → (False → p3)) ∨ p3) ∨ p4)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41443882843128630667256415983 : ((((p4 ∨ ((p2 ∧ p2) ∨ (((p3 ∨ p2) ∨ (p2 ∧ (p5 ∨ p3))) ∨ p3))) → (p4 → ((((p4 ∨ p5) ∧ p1) ∧ p3) → p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172812361007847830197686148217 : ((True ∧ (((True ∧ True) ∨ ((p3 ∨ p4) ∧ (p3 → (p2 → (p5 → p2))))) → p4)) ∨ ((p5 ∨ (True ∨ ((p2 → (p5 ∧ p5)) → True))) ∨ False)) := by
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
theorem thm_5_vars_729905874745100373835731106506 : (((((p2 ∧ p5) → p2) → (p2 ∨ (((((True ∨ ((p1 → p1) → (p2 ∧ False))) ∨ (p2 ∧ p4)) → (p2 ∨ p1)) → p3) ∨ (False ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64279626843508820607059623911 : ((False ∨ (p1 → ((((((False ∧ p3) ∧ False) ∧ p4) → (((True ∧ p1) ∧ p1) ∧ (False → p1))) → ((True → p3) → p2)) ∨ (p1 → True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204149646556189203196656081375 : (((((p4 ∨ p5) ∧ p3) ∨ p1) ∧ p3) ∨ (((((p3 ∧ (p2 ∧ (True ∧ p1))) → (p2 → p3)) ∧ p5) → (((True → True) ∨ p3) ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116051441036230158753162780471 : (((p3 → ((p3 → p3) ∧ p1)) → (((((p4 ∨ (p5 → (p4 ∨ (p5 ∧ p4)))) ∧ p3) ∧ p1) ∧ ((p1 ∧ p2) ∧ p4)) → p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590768331133317092334748434986 : (((((p1 ∨ ((((p4 → p3) ∨ ((((False ∧ ((False ∧ False) → p2)) → p4) ∨ p5) ∧ p3)) ∨ (p1 ∨ (p4 ∨ p3))) → p5)) → p4) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740136399343595044484644015128 : ((((False ∨ p3) ∨ (((p3 ∧ False) → p2) ∧ ((p1 ∧ (p5 → ((p1 ∧ True) ∧ (p3 ∧ p1)))) ∧ ((p3 ∧ (p1 → (True ∨ False))) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358199786576297865244180711849 : (p5 → (p3 ∨ (p1 ∨ ((p5 → ((True → (True ∨ (p1 → ((p5 ∧ (False ∨ p4)) → p2)))) ∧ False)) → (((p2 ∧ p1) ∨ (p5 → p3)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48654782460770947571699977206 : ((((((p4 ∧ (p3 → p3)) ∨ (((p5 ∨ False) ∧ False) ∧ (p1 ∨ False))) → True) → (p4 → (p3 → (p5 → False)))) ∧ (p3 ∧ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740575370281749252555368967792 : ((((p2 ∨ False) ∨ (p1 ∧ ((((False → (p2 → p5)) ∧ p5) ∨ (p2 → p1)) ∧ (((p5 ∨ p4) → p4) → (((True ∧ p2) ∨ p4) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172230855808366934924675166401 : ((((p1 → ((p1 → (p2 ∨ p4)) ∧ p3)) ∧ p4) ∧ ((p2 ∧ (True ∧ p5)) ∨ p4)) ∨ (p4 → (p2 → (((p2 ∨ (p2 ∧ False)) ∧ False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708057322791755550055890194859 : ((((p3 ∨ (p4 ∧ ((p2 ∨ (p2 → p4)) → p3))) ∨ (p4 → (p5 ∨ ((p1 ∧ (p4 ∨ (p3 ∨ ((p3 ∧ p4) ∨ (p3 ∨ False))))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124965113364351885309453869830 : (((p2 ∨ (True ∧ (p2 ∨ False))) → (((((p2 → True) ∨ ((p2 ∨ p4) ∧ p4)) ∧ ((p5 ∧ p5) ∧ (p2 → p4))) ∧ p1) ∧ p5)) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69162092566972241722884918626 : ((p5 → (((False ∨ ((p4 ∨ ((True → p1) → ((p4 ∧ (False → (p1 → p2))) → p3))) ∨ p5)) → p2) → (p3 ∨ (p5 ∧ (p3 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113476442745152519589623941148 : (((((p4 ∧ p3) ∧ (p5 → ((p1 ∧ False) ∧ (p5 ∧ ((((p1 → False) → p1) ∧ p4) → p5))))) ∧ (p5 ∨ False)) ∨ (p5 ∨ False)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314425868699483792784001533716 : (p3 ∨ (((False → ((p2 ∨ False) ∨ True)) ∧ ((p1 ∧ (p4 → ((True ∧ (p1 ∧ p1)) ∧ (p4 ∧ p2)))) ∨ True)) ∨ (True ∧ ((p5 → False) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200437167549786756082166987281 : (((p4 ∨ False) ∨ (True → ((p1 ∧ True) ∧ True))) → (p3 → (p1 → ((False ∧ True) ∨ ((p4 ∨ (p2 ∨ ((p4 ∧ p2) ∧ (True ∨ True)))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43401836768220842383107530797 : ((((((((p5 ∧ p3) ∨ p3) ∨ (p2 → p1)) → ((p4 → p4) ∨ p5)) ∧ (p1 → (True ∧ ((p1 → (p3 ∧ p4)) → p4)))) ∨ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198979753508368579872926291328 : ((p5 → (((p4 → p2) ∨ True) → (p4 ∨ False))) ∨ ((p3 → False) → (((p5 → p1) ∨ (p2 → p4)) → (False → (p3 ∨ (p1 → (p5 ∧ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741869556185316724226750806607 : ((((True → p5) ∨ (((True → p4) → p1) → ((((((True ∧ p3) → (p2 ∨ p3)) → True) → False) ∧ (((True ∧ p5) → p4) → p5)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47031179050413934783525070647 : ((((p5 → (p2 → ((((p1 → p5) ∧ ((p1 ∨ p2) ∧ ((p4 → p5) ∨ (p5 ∧ p2)))) ∧ p4) ∧ (True ∧ True)))) → p3) ∨ (True ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58817676328597508628629170218 : (((p5 → p4) ∧ (((p2 ∨ (((p4 → (p3 → p5)) ∨ (((p5 ∧ True) ∧ p1) → p3)) ∨ p2)) ∧ (p5 → False)) ∨ (False ∨ (p5 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345607624415388308656140548675 : (p3 → (((True ∧ True) → ((p2 ∧ ((p4 ∨ ((p3 ∨ (p3 ∨ False)) → p3)) ∧ p3)) ∨ (False ∧ ((p5 → (p4 ∧ (p4 → p4))) ∨ p2)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50692000967452820188808306103 : (((((True ∨ True) ∧ False) ∨ ((p3 ∧ p5) ∨ ((((p1 ∨ p5) ∧ ((p3 → p4) ∨ p4)) ∧ True) → p5))) → ((p4 ∨ (p1 → p2)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177688811621032923501107673107 : ((((((p3 → p2) → ((p2 → p3) → p1)) ∨ p1) ∧ (p3 → p5)) ∧ p3) ∨ ((True ∧ ((((False ∧ p1) → p5) ∨ (p1 → p1)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215729270404035805754190091329 : ((False ∨ (p2 ∨ (p2 ∨ p1))) ∨ (((p1 ∧ ((p4 ∨ (p5 ∧ True)) ∨ (p4 → p1))) ∨ (p1 ∨ (p1 ∧ (p1 ∧ ((p2 ∧ p5) → p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166165453656295926113149659089 : ((False ∧ ((p4 ∨ (p3 ∧ p4)) ∨ (((p3 ∨ p4) ∧ ((p3 → (p4 → False)) → True)) ∧ p4))) ∨ ((p5 ∨ ((p4 ∧ p4) → (p4 ∨ p1))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165332012007576144737746774243 : ((((((p2 ∧ p4) ∧ (((p5 ∧ p1) ∨ p4) ∨ p5)) → p5) → p1) ∧ ((p3 → p1) ∨ p1)) ∨ ((False → (p3 → p3)) → ((p5 ∧ True) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217244438954331857296550775017 : (((True ∧ (p5 → p2)) ∨ p1) → ((True → ((((p2 ∨ (p4 ∨ p4)) → (p3 ∨ (((p4 → p4) ∧ p5) → (p4 → p4)))) ∧ p1) ∨ True)) ∨ p4)) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55413097522738464116298335512 : (((((True ∨ p3) ∧ (p3 ∨ p2)) ∨ p5) → (((p1 ∧ (p5 ∨ (((p4 → False) ∨ p1) → p1))) ∨ (((p3 ∧ p3) ∧ p2) ∧ p4)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779452285151881448602271504140 : (((p2 ∨ ((((p1 ∧ (p3 → (p2 ∨ True))) ∨ (((((p2 ∧ p3) → False) ∧ True) ∧ (p5 ∨ p4)) → (p3 ∨ True))) → (p5 ∨ p5)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_190895554712617205097686504213 : (((p5 ∧ (((p4 ∧ p2) ∨ False) → True)) → (p4 ∨ p3)) ∨ ((p3 ∨ p5) ∨ (((p5 ∧ (True → ((True → p5) ∨ (p5 ∧ p3)))) → True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231733186120863060921393171590 : (((p2 ∧ p4) → p3) → ((((p3 → ((False → ((p2 ∨ p5) ∨ p1)) → (p1 ∧ p3))) ∧ True) → (p3 ∨ True)) ∧ ((True ∧ p3) ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41402940511918201983287506510 : ((((((p5 ∨ (p1 ∨ (p5 → (p5 ∧ p3)))) ∧ ((False ∨ True) ∨ p2)) ∧ p5) ∨ (p4 ∨ ((True ∨ (False → (p5 ∧ p5))) ∨ p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247314192348192264074859829577 : ((False ∨ False) ∨ (((p2 ∧ False) ∨ (p3 ∧ True)) ∨ ((p2 ∨ (p2 → (p5 → (p2 → ((p1 ∨ (p4 ∧ False)) ∨ (False → (p2 → True))))))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54047838927508738825308883757 : ((((p2 → ((p5 → p1) ∨ True)) ∧ ((p2 ∧ p3) ∨ p2)) → (((False ∧ p1) ∧ p1) ∨ ((p5 → (p2 ∧ p1)) → ((p2 ∨ p3) ∨ True)))) ∨ p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76622003335029519713578320171 : (((((p5 ∧ ((((p4 → p1) ∧ p3) → (p3 ∨ (False ∧ p4))) ∨ p5)) ∧ (p2 ∧ (p3 ∨ p5))) → ((p5 → False) ∨ (p5 → p2))) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ ((((p4 → p1) ∧ p3) → (p3 ∨ (False ∧ p4))) ∨ p5)) ∧ (p2 ∧ (p3 ∨ p5))) → ((p5 → False) ∨ (p5 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347193827928186996340754144543 : (p3 → (((((p1 → True) ∧ p2) → (p4 ∧ (p3 ∧ p1))) ∨ (p2 ∨ False)) ∨ (((((False ∨ p3) ∨ (p2 ∨ p4)) ∨ (False ∧ p3)) → True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136592401708640694872957661858 : (((p1 ∨ (False ∧ False)) ∨ (((((((p5 ∨ p2) ∧ p5) ∨ (p1 → p5)) ∧ p3) → (p5 → p1)) → (p4 ∨ p1)) ∧ False)) ∨ ((p4 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599379895316680050631868118351 : (((((p4 ∧ True) ∨ ((True ∨ p2) ∧ ((True ∧ (p5 ∨ ((p4 ∨ p5) ∨ p1))) → (p2 → ((p3 ∧ p1) ∨ ((p3 ∨ True) ∨ p5)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58327126707922061096474269630 : (((False ∨ p1) ∧ (((((((p3 → p3) ∨ p5) ∧ p2) ∨ False) ∨ p1) ∨ (p5 → (p4 → ((p4 ∧ (p5 → (p5 → p2))) ∨ False)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665469031997561666695596752095 : (((((((((((p5 ∧ True) ∧ (p1 ∨ p5)) ∨ ((p3 ∧ p4) ∧ p5)) ∨ (True ∧ p2)) ∨ p3) ∧ False) ∨ p2) ∨ p5) ∧ (True → (False ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159029118583689658344100099534 : ((p4 ∨ (True ∧ ((p5 → (False ∧ p3)) ∧ (((False → p2) ∧ ((False ∨ p4) ∧ (p4 → p3))) ∧ p5)))) ∨ (((p1 ∨ p2) ∧ (False ∧ True)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224310030232510030694721494990 : ((False → (False ∨ p2)) ∧ (((p3 → False) ∧ p3) ∨ (((p2 ∨ p1) ∧ ((p2 ∨ True) → p3)) → ((False → (p5 ∧ p2)) ∧ ((p3 ∧ p3) ∨ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p2 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
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
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316752704290241068529988489859 : (p3 ∨ (True → (((((p5 ∨ (p5 → True)) ∧ p5) → (p3 ∨ (p5 → p3))) → False) ∨ (True ∨ ((False → (p2 ∨ ((True ∧ p1) ∨ False))) → p5))))) := by
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
theorem thm_5_vars_181640354952387871935865280881 : ((p3 → (((p5 ∨ p4) → (False ∧ ((False ∧ (p2 ∧ p4)) → p1))) → p3)) → (p3 ∨ (((((p3 ∧ p4) ∨ False) ∨ (p1 → p4)) ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676310239980735827239815160881 : (((((p2 ∧ True) ∧ (((p2 ∨ p4) ∨ (((p3 ∧ p4) ∧ p5) ∧ False)) ∧ (((p5 → p3) → True) ∨ False))) ∧ (False ∨ (p5 ∨ (p2 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247798030010563104045039686786 : ((p1 ∨ p1) ∨ ((p2 → ((p1 ∨ p4) ∨ (False → False))) ∧ (p1 → (p2 → ((p4 → ((False ∨ (p1 ∨ False)) ∨ True)) ∨ (False → (p4 ∧ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186950255397032988758869663808 : ((((p3 → p2) ∧ p1) ∨ ((p2 ∧ p5) ∨ (p3 ∨ (p3 ∨ p2)))) → ((False ∧ (p5 ∨ p5)) ∨ ((p3 ∨ False) → ((p1 ∧ p3) ∨ (False → p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
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
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- False on the left can always be used.
            apply False.elim h26
          case inr h27 =>
            -- False on the left can always be used.
            apply False.elim h27
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h31
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- False on the left can always be used.
            apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218926136224952465654738796312 : ((p3 ∧ (p2 ∧ (p4 → p2))) → (((((((True ∧ p2) ∧ (p4 → (p2 ∧ (p5 ∨ p5)))) → p1) ∧ False) ∧ ((p1 → False) ∨ p3)) ∧ p1) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658551851178862881448413121805 : ((((p2 ∨ ((p3 ∨ p2) ∨ ((p3 ∨ p2) ∨ (((True → p4) ∧ ((((p5 ∧ (p5 ∧ False)) ∧ False) → p4) ∧ p1)) → False)))) ∨ (True ∨ p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_68348742738767423158175455719 : ((p3 → (((p5 ∨ ((False ∧ p1) → (False → p5))) → (p4 ∧ False)) ∨ (p4 → (p5 → ((p2 ∧ p2) ∨ ((False ∨ p5) ∨ (p2 ∨ False))))))) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669408321122416692593976292779 : ((((((((p5 → ((p4 ∨ ((False → (p4 ∨ p1)) → p5)) ∨ True)) → False) → p4) → (p3 ∨ p5)) ∨ (p2 → False)) ∨ ((p2 ∧ False) → False)) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300075860620633165104999525059 : (False ∨ (((((p4 ∧ (((((p1 ∨ True) ∨ False) → p2) → (p4 ∧ p2)) ∧ p4)) ∧ (p3 ∨ p4)) → (p1 ∨ (p4 ∧ p3))) → p1) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338530300477165450777927698360 : (p1 → (((p4 ∨ p3) → p4) ∨ (p3 → (((p4 ∨ p3) ∨ False) → ((((True → (p4 ∨ p5)) ∧ (p3 → p5)) ∧ (p4 ∨ (False ∧ True))) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307641982478428272678704448969 : (p1 ∨ (p1 → ((p1 → p3) → (((p4 ∨ ((p1 → (p1 ∧ (True → p2))) ∨ p2)) ∧ ((False ∨ (p5 ∧ (True → (True → p5)))) ∨ p4)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263121122088351065823379283194 : (True ∧ ((((((p1 ∧ p2) ∨ (False ∧ True)) ∧ (False ∧ True)) ∨ (p5 ∨ p2)) ∨ ((False ∨ ((False ∨ p1) → p1)) ∨ (p4 ∧ False))) ∨ (True ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8778198011642980422655780396 : ((((((True → ((p3 ∨ True) → ((True → p3) → ((p1 ∨ p1) ∧ p3)))) ∨ p3) ∧ ((p4 ∧ p1) ∨ p3)) ∨ ((p4 ∨ p2) → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_260790562359619742324228863677 : ((p3 → p5) → ((p3 ∨ (p4 ∨ (p3 ∧ (False → (((True ∧ False) ∨ False) ∧ p1))))) ∨ ((p1 → (p3 → p4)) → (((p5 ∧ p4) ∧ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118336898427284274676983069787 : ((p2 ∨ ((((p1 ∨ p4) ∧ ((p2 → ((True ∧ ((p5 ∧ p1) ∧ (((p4 → p1) ∨ p2) → p1))) → False)) ∨ p5)) ∨ True) ∨ p2)) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344825030273576536423905771697 : (p2 → (p4 → (p5 → (((((((False ∨ p1) ∧ ((p3 ∨ False) ∨ p4)) ∧ (p5 ∨ ((False ∧ p2) ∨ p5))) ∧ p3) ∨ (p1 → p1)) ∨ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40588812583594737572982597873 : (((((((p2 ∨ False) ∨ False) → ((((p1 ∧ p2) → ((True ∨ p4) → p5)) ∨ (((p1 ∨ False) ∨ False) ∨ p2)) ∨ p3)) ∧ p1) → p2) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323281646444455190746309355649 : (p5 ∨ ((p5 → ((True → (p1 ∨ ((((((p3 ∨ (p4 → p2)) ∧ p4) → p3) ∨ p5) ∧ (p5 ∧ p3)) ∧ p2))) ∧ (p1 → True))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139476722474657488267829534066 : ((((p3 ∨ (((p5 ∨ p2) → (((p1 ∧ p4) ∧ ((p2 ∨ p4) → True)) ∧ (p4 ∨ (p4 ∨ False)))) ∨ False)) ∨ p4) → p3) → ((p3 ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258738515146240811956005438973 : ((True → True) → ((p3 ∧ p4) → (((p4 ∨ p5) ∧ (False ∨ ((p4 → (p2 → False)) ∧ ((((False ∧ p1) ∨ (True ∨ p3)) ∨ p1) ∨ p1)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313120720023130748147808585588 : (p3 ∨ ((((((p2 ∨ (p5 ∨ True)) ∨ (True ∨ (False → True))) ∨ ((p1 ∨ (p3 → p3)) ∧ False)) ∨ False) ∧ ((p1 ∧ False) ∨ (False ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256309873802246275574951472252 : ((False ∨ p1) → ((p4 ∨ True) → (((((p4 ∨ p2) ∨ (p2 ∧ ((p5 ∧ p5) → (p5 ∧ p1)))) ∨ True) → (((p4 ∧ p2) ∨ p2) ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165027825729107395340776265961 : (((((False ∧ p2) ∨ True) ∨ (((p1 ∧ (p3 ∨ False)) ∨ ((p2 → p1) ∧ p5)) ∨ True)) → False) ∨ ((p5 ∨ (p4 ∨ True)) → ((True → True) ∨ p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692975305865385038851359440058 : (((((False ∧ False) → ((False → ((p4 ∧ (False → (p4 → p3))) ∨ p5)) ∨ True)) ∧ ((((p2 ∨ False) ∨ p4) ∨ p5) ∧ (p2 ∨ (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315253497127832513436000337542 : (p3 ∨ (((p4 ∨ True) → (False ∨ p5)) ∨ ((p2 ∧ False) → ((p1 ∧ p3) ∧ (((p2 ∨ (False ∧ ((False → p5) ∧ (False ∧ False)))) ∧ False) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191255644995394242489641284310 : (((p3 ∧ p3) ∧ (((p3 ∨ (False ∧ p1)) ∨ True) ∨ False)) ∨ ((False ∧ p2) → ((((p4 ∨ p3) ∨ p1) ∨ (p4 → ((p2 → False) → False))) ∨ True))) := by
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
theorem thm_5_vars_67986467901578853950913392537 : ((p2 → ((p2 ∨ p4) ∧ (p3 ∨ ((((p2 → False) ∧ ((False ∧ (True → (p5 ∧ p4))) ∧ (p3 → p4))) ∨ (p5 → p4)) ∧ (p2 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114644925544398785900835924434 : ((((p3 ∨ ((p4 ∧ p2) ∨ (((p3 ∧ (True ∨ p2)) ∨ p1) ∨ p3))) ∨ (True ∨ False)) ∨ (((p4 ∧ p3) → (p4 ∨ False)) ∧ p3)) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148715217960193809395354706283 : ((((p2 → (False → p5)) → (p2 ∧ (False → p1))) → (p4 ∨ ((p5 ∨ p5) → (p4 ∧ (p1 → (p4 → True)))))) ∨ (p2 → (p3 ∨ (False → p5)))) := by
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
theorem thm_5_vars_669142594347977312742024717445 : (((((((False ∨ (p4 → (p5 ∧ p5))) ∧ p5) ∧ (((p4 ∧ p1) → (False → p5)) ∨ ((p2 ∧ p2) → p5))) → p4) ∨ (p3 ∧ (p1 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309908758791445536337310957959 : (p2 ∨ ((((p5 ∨ (((p1 → p4) ∨ p3) ∨ (((p4 → True) ∧ p4) ∨ p5))) ∧ (p4 ∧ True)) ∧ False) ∨ (((False ∧ False) ∧ True) → (False ∧ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251891322846079561796653805838 : ((p3 → p5) ∨ (p2 → ((((((p2 ∨ ((p4 ∨ p3) → p4)) ∨ p1) ∨ True) → True) ∨ p3) → (p5 → ((p5 ∧ (p5 ∨ (True ∧ p1))) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64173286065744065605576406258 : ((False ∨ ((True → False) ∨ ((((p3 ∧ (p2 ∨ p3)) ∨ ((p5 ∧ (p1 ∧ False)) ∧ p3)) ∨ (False → False)) → (p3 → ((p5 → p1) ∨ p3))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



