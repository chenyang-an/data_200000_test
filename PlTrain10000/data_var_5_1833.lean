variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124507902276689506974474339821 : (((((p5 ∨ p5) ∨ p4) ∨ (p2 ∨ p1)) ∧ (((p3 ∨ (p5 ∧ ((p1 ∨ ((p3 ∧ p2) → (p5 → p5))) ∨ p4))) ∨ True) → p1)) → (p1 ∨ p3)) := by
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
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h7 : ((p3 ∨ (p5 ∧ ((p1 ∨ ((p3 ∧ p2) → (p5 → p5))) ∨ p4))) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h8 := h3 h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h10 : ((p3 ∨ (p5 ∧ ((p1 ∨ ((p3 ∧ p2) → (p5 → p5))) ∨ p4))) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h11 := h3 h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : ((p3 ∨ (p5 ∧ ((p1 ∨ ((p3 ∧ p2) → (p5 → p5))) ∨ p4))) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : ((p3 ∨ (p5 ∧ ((p1 ∨ ((p3 ∧ p2) → (p5 → p5))) ∨ p4))) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48588012884073252025228211524 : (((((False ∧ ((((p1 ∨ (p1 ∧ (True ∨ p1))) ∧ p4) ∧ (True ∧ p4)) → True)) ∨ (p3 ∧ p3)) ∧ (False → p2)) ∧ ((p1 ∨ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52756023776552184037819588653 : (((((((p5 → ((False ∧ False) ∨ p2)) ∧ (True → p3)) ∨ p3) → True) → False) → ((False ∨ False) ∨ (False ∧ (False ∨ ((p3 ∧ p2) → p2))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 → ((False ∧ False) ∨ p2)) ∧ (True → p3)) ∨ p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343135764410850427069006655779 : (p2 → (((True ∧ False) ∨ p1) ∨ (((((p5 ∧ ((p4 ∨ p4) → p5)) ∧ ((False ∨ p4) ∨ True)) ∨ (p2 ∨ (p5 → p1))) ∧ p4) ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115095645358936886919908269426 : (((p5 → ((((((False → p5) → p5) ∧ p4) ∧ p5) ∧ False) ∨ p3)) ∨ ((p5 ∧ p3) ∧ ((p2 → p2) ∨ ((p3 ∧ p2) → p4)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716949863638379522821330992331 : ((((p3 ∧ (p2 ∧ (p2 → False))) ∧ ((((((((p5 ∧ p5) ∨ False) → p4) ∧ (((False ∨ p4) ∧ p5) ∧ p5)) ∧ p5) → p3) ∧ p5) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811382149355085053241080810043 : (((p5 → (p2 ∨ (((((p1 ∧ p5) ∧ (False ∧ (p5 ∧ p2))) → ((p3 ∧ (False ∨ p4)) ∨ (((p2 → p4) ∧ p5) ∧ p5))) → False) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74541081232449741196502185322 : (((True ∧ (((((True ∧ (p4 ∧ p1)) → False) ∨ ((p5 → ((True ∨ p3) → p4)) → p1)) ∨ ((p4 ∧ False) → (p4 → p5))) → p1)) ∨ p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((((True ∧ (p4 ∧ p1)) → False) ∨ ((p5 → ((True ∨ p3) → p4)) → p1)) ∨ ((p4 ∧ False) → (p4 → p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133626225481989217163998561714 : (((((p4 ∧ p1) ∨ (((p4 ∧ p3) ∨ (((p1 ∧ ((True ∧ p2) ∨ True)) ∨ False) ∨ p2)) → (p5 → False))) → p1) ∧ p5) ∨ (p3 → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257123253127254695364583472921 : ((p2 ∨ p1) → ((((((False ∧ ((False → p4) → p4)) ∧ p3) ∧ (False ∧ ((True ∨ p3) ∨ (p1 ∧ p4)))) ∨ (p5 ∨ (p4 → True))) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702932556542147737060278353596 : (((((p2 ∨ (p2 ∧ False)) ∧ ((True ∨ p1) → (p5 ∧ p5))) ∨ (((p1 ∧ (False ∧ False)) → (True → (p4 ∧ True))) ∧ (p4 ∨ (p1 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115564788205540043673112090269 : ((((False ∨ ((p3 ∧ p1) ∧ p1)) ∨ False) ∧ ((p3 → (True ∨ True)) ∧ (((p1 ∨ False) ∨ ((p4 ∨ p1) ∨ (p3 ∨ p4))) ∨ p3))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264791947016795717861761914460 : (True ∧ ((False ∧ p2) ∨ (True → ((((p2 ∨ ((((p2 ∨ False) ∧ p5) ∨ p3) → ((p4 ∧ p2) ∨ True))) ∧ p1) ∨ p2) ∨ ((p2 ∨ p4) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_336350200751447499524975872317 : (p1 → (((p5 → p2) ∧ ((((((((p4 ∨ (True → p5)) ∧ p2) → (False ∧ p3)) → p5) → False) → False) → p5) ∨ (True ∨ (p4 → p1)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340848537521044123954158783066 : (p2 → (((((False ∧ (((p4 ∨ False) ∨ ((p4 ∧ p5) ∨ p5)) ∧ p3)) → True) ∧ (p2 ∧ ((p3 → p5) → p4))) ∨ ((p4 ∧ p5) ∨ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47296092503492308064829402043 : (((((p3 → p5) ∨ False) ∧ ((p3 ∨ (p1 → ((((True ∨ p2) → ((p4 ∨ (p4 ∧ p2)) ∨ p1)) ∧ True) ∨ False))) ∨ p3)) ∨ (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_520226710246728658306295602622 : ((((p3 ∨ p3) → (p3 ∧ ((((True → ((p1 ∨ True) → p3)) ∧ (((((False → p5) ∨ p5) ∧ p2) ∧ p1) ∧ (p5 ∨ False))) → p4) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207873621038475946697850517818 : ((((True ∧ True) → p5) ∧ (p1 ∨ False)) → ((p3 ∨ (((False ∨ (True ∧ p2)) ∨ ((True ∧ p3) ∨ p4)) ∨ ((False ∨ False) → p1))) ∨ (p1 ∧ True))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353865353228621086271919504088 : (p4 → (p1 → ((p2 → (p3 ∨ (p1 → p4))) → (p2 → (((p2 ∧ ((True ∨ (p5 ∧ (p5 ∧ p5))) → ((p3 ∧ p5) ∨ False))) → False) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345350250806355585427029521265 : (p3 → (((p4 → ((p4 ∧ p1) ∨ (((((p1 → ((p1 ∧ (False ∨ (p2 → p3))) → True)) → (p1 ∨ p4)) ∨ p4) → p3) → p1))) ∧ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349723457392381140668863676245 : (p4 → (((((p5 ∨ (p4 → True)) → p4) ∨ ((True ∧ p1) ∨ p5)) ∧ ((((((p2 ∧ p3) → p2) ∧ (p3 ∨ p1)) → p5) ∨ p4) ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184967426916881231481082147708 : (((p3 ∧ (True ∨ p4)) → (False ∨ ((p5 ∧ (p2 → p4)) ∧ True))) ∨ (p5 → (False → (p2 → (((False ∧ (p2 ∨ p2)) ∨ (p5 ∧ p4)) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191502971384335081979193743489 : ((False ∧ ((((p1 ∨ True) ∧ (False ∧ True)) ∨ False) ∨ p5)) ∨ (False ∨ (True ∨ (((p5 → p2) → (p3 ∨ (((p2 ∨ p3) ∧ p1) ∧ p3))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221591157947401712633972747731 : (((p4 → True) ∨ p5) ∧ (p5 → ((False ∧ p4) ∨ ((p2 ∨ (p1 ∨ (p3 ∨ ((True → (p5 ∨ p3)) → p5)))) ∧ (p3 ∨ (p2 ∨ (True ∨ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111978116211389544157263802734 : ((((p2 ∧ ((p4 ∧ p5) ∧ (p1 → False))) ∨ ((((True ∨ (True → ((p4 → (p1 → True)) ∨ p5))) ∨ p5) ∨ p1) → False)) ∨ True) ∨ (True → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586292935616688503134501569181 : ((((((((p2 ∨ (True ∨ p1)) → p5) ∧ (p4 ∨ False)) ∨ ((((p1 → (p1 → (p4 ∧ p1))) ∨ False) → p2) ∧ (p4 ∨ True))) ∧ p4) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51058794622237015524633473653 : (((p5 ∨ (p5 ∨ (((((p1 ∨ False) ∧ (p2 → ((p4 ∨ p1) ∨ p5))) → p1) ∧ p5) ∨ True))) ∧ ((p5 ∨ (p2 ∧ p4)) → (p3 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350030781477059447504644426779 : (p4 → (((((p1 ∨ p3) ∧ ((p5 → (False ∨ p2)) ∨ (False ∨ ((True ∨ p4) ∨ True)))) ∧ (p1 ∨ ((True ∧ p4) ∨ (p4 → p5)))) → p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601539543374342224904168402031 : ((((p3 ∧ (((True ∨ (((((p1 ∧ p5) ∧ p5) ∧ False) ∧ p2) ∧ ((True → p4) ∧ (p5 → p2)))) → p5) → (False ∧ (p1 ∨ p3)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47985418555933149573219997710 : ((((p2 ∧ ((((p3 ∨ (p1 ∨ ((p3 → False) ∨ p2))) ∨ (True ∨ False)) ∨ p2) → p4)) → (p1 ∨ ((p5 → p3) ∨ True))) → (p1 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68211346405198414591454732675 : ((p3 → (((((((((True ∧ p2) ∧ p4) ∨ (p2 ∧ p4)) ∧ ((p1 ∧ p4) ∨ (False → (p3 → p5)))) ∧ p3) ∧ True) → p5) ∧ True) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58380101853342582518734363037 : (((p1 ∨ p3) ∧ ((True → (((True ∧ True) → True) ∨ True)) → ((True ∨ (False ∨ (p5 ∧ p4))) → ((p4 → (p2 ∧ p4)) → (p5 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165006353205011951390439129535 : ((((True ∨ ((p2 ∨ (True ∧ p4)) → p1)) ∧ (((p3 ∧ (p3 → p1)) ∨ p2) ∨ p2)) → False) ∨ ((p5 → (False → p1)) ∨ ((False → p2) ∨ p2))) := by
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
theorem thm_5_vars_62505551562569015943699868155 : ((p3 ∧ (p2 ∧ (((p4 → ((((True ∧ (p2 ∧ p3)) ∧ ((False → (False ∨ p3)) ∧ p1)) ∧ (p4 ∧ p1)) ∧ p4)) → (p1 → p1)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616679874901516682637657873716 : ((((((((p3 ∨ (p1 → p3)) ∨ (p4 ∨ p3)) ∨ True) ∧ p4) ∨ (False ∨ (((True ∨ (True → p1)) ∧ (p5 → (False → p1))) ∨ p2))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777353557704438122206663827207 : (((p1 ∨ ((True → (((True ∨ True) ∧ (p4 → (p2 ∨ True))) ∧ ((p5 ∨ ((p1 → p3) → p4)) → p2))) ∨ (False ∨ (True ∨ (p4 ∧ p3))))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805610813506856833114547259827 : (((p3 → (True → (((p4 ∨ p5) ∨ True) ∧ (((False ∨ ((p4 → (((p1 → (p1 ∨ (p2 ∨ p5))) ∨ p5) ∧ p4)) → p4)) → p1) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54686440145060675471254631418 : ((((p2 ∧ ((p4 ∧ p5) ∧ (True → True))) → True) → ((((p4 ∧ p4) ∧ ((((p4 ∧ False) → p4) → p4) ∧ p1)) ∨ (p4 ∨ True)) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61445848075253675221915283851 : ((p1 ∧ ((p1 → (((p3 → ((p5 → (p5 → (((p5 ∧ p4) → False) ∧ p2))) → False)) ∨ ((p2 ∧ False) ∧ p3)) → (p2 → p5))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932157132602667231373136510585 : (((((p1 → (p2 ∨ ((p2 ∨ True) ∨ p2))) → p5) ∧ (p2 ∨ (((p5 ∨ p1) → True) → ((((p3 ∨ p3) → p1) ∨ (p2 → False)) ∧ p3)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → (p2 ∨ ((p2 ∨ True) ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p1 → (p2 ∨ ((p2 ∨ True) ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674749816598668294199038114183 : ((((p3 → (((p4 ∨ False) ∧ p1) ∧ ((p1 → p1) ∨ ((p4 ∨ (((p5 → p4) → False) ∧ p2)) ∨ (p2 ∨ p1))))) → ((p1 ∨ True) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134971975874213800311343355939 : ((((((False ∧ p3) ∨ True) ∨ p5) ∨ (((False ∨ p2) → (p4 → p1)) → (p3 → ((p3 → p4) ∧ True)))) ∧ (p2 ∧ p1)) ∨ ((p3 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229483189718541775444219680798 : ((p2 → (p3 ∧ p2)) ∨ (((p5 ∨ (p4 ∧ (p1 ∧ p3))) ∧ (p2 ∨ (p1 ∨ (p1 → p5)))) ∨ (((p5 → (p4 → p4)) → (p1 ∨ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147457412406506894735076452342 : ((((p3 ∨ p2) → ((((False ∨ ((p5 ∧ (p5 ∧ (p2 ∨ (p4 → p1)))) ∧ True)) ∨ p2) ∧ p1) → False)) ∨ True) ∨ ((p2 ∧ (p3 ∨ p4)) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185349356250396405118703210041 : ((p4 ∧ (((False ∧ p2) ∧ (True ∨ True)) ∨ (p5 ∨ (p5 ∧ p3)))) ∨ (p3 ∨ (p4 → ((True ∨ ((False ∨ (p2 ∧ (p1 → p2))) → p1)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300480056866206599776172801260 : (False ∨ ((p1 → (((p5 ∧ p2) ∨ False) ∨ (p4 ∧ (((((p4 → ((p5 ∨ p5) ∧ p3)) ∧ p5) ∨ False) ∧ p5) → p1)))) → ((p3 → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762162671998842115657105225867 : (((p3 ∧ (((p4 → ((p4 → ((True ∧ True) ∧ (p4 ∧ ((p5 ∨ p5) → p3)))) → p3)) ∧ (((p2 → True) ∨ p4) ∧ p1)) ∨ (p4 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246679715118299794490237470976 : ((p5 ∧ p4) ∨ (((p5 ∨ (False ∨ ((p1 ∨ p3) ∨ ((True → p1) ∨ (p4 ∧ False))))) ∨ (p2 ∨ (((p3 ∧ False) ∧ (p2 → p4)) → True))) ∨ p2)) := by
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
theorem thm_5_vars_156912456897506065040765037466 : (((((p1 → ((False ∨ (((p5 ∨ p2) ∧ p4) → p3)) ∧ (p2 ∨ False))) ∨ (True ∧ True)) → p5) ∨ p2) ∨ (False → (False → (p2 → (p2 ∧ p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49119794315466840177896271101 : (((((p3 ∨ p3) ∨ (True ∨ ((((p4 → False) ∧ False) ∧ (p3 ∨ False)) ∨ p3))) → (p1 → (p3 → (False ∨ p5)))) ∨ ((False → True) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181409928041393362087944683844 : ((p2 ∨ ((p3 ∧ ((p2 → (p1 → (p2 ∧ p5))) → p5)) → (False → p4))) → (p5 ∨ ((False → p1) → (True → (True → (p3 → (p5 → p5))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164167324723519644437245754237 : ((p4 ∨ (((p2 ∧ p5) ∧ False) ∨ (p2 → (p2 ∨ (p4 → (p1 ∧ (p1 ∧ (p3 ∨ True)))))))) ∧ (p3 ∨ ((p1 ∨ (p2 ∧ (p4 ∨ False))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774452547808226277013197268262 : (((False ∨ (((p2 → (p3 ∨ p3)) → (True ∧ ((((p5 → p1) ∨ p2) → p1) → (p3 ∧ False)))) ∨ ((p3 → (True ∨ p2)) ∨ (p2 ∨ True)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167323103455996511562218293861 : ((((p4 → (False ∨ (p1 → ((p3 ∨ ((p2 ∨ p4) ∨ p4)) ∧ p5)))) ∧ (p3 → p3)) → False) → ((p5 ∨ (p1 → ((p1 ∨ True) → False))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 → (False ∨ (p1 → ((p3 ∨ ((p2 ∨ p4) ∨ p4)) ∧ p5)))) ∧ (p3 → p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h4
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 → (False ∨ (p1 → ((p3 ∨ ((p2 ∨ p4) ∨ p4)) ∧ p5)))) ∧ (p3 → p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h14 := h9 h13
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (p1 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- False on the left can always be used.
      apply False.elim h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h10
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67843314884483530040610475880 : ((p2 → (((p4 ∧ False) ∨ (((((False ∧ False) ∨ True) ∧ (p1 → True)) ∧ (True → p1)) ∧ ((True → True) ∨ (True ∧ p1)))) ∨ (False → p4))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215770271728467734572830741235 : ((p1 ∨ ((p3 ∧ p3) → False)) ∨ ((((p3 ∨ (p5 ∧ True)) → (((p5 → (((p4 ∨ False) ∨ False) ∧ p4)) ∨ (False → p1)) ∨ p3)) → False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (p5 ∧ True)) → (((p5 → (((p4 ∨ False) ∨ False) ∧ p4)) ∨ (False → p1)) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351902358256108046413694254597 : (p4 → ((((p5 → (p3 ∨ ((p5 → p4) ∧ p4))) → True) → p5) ∨ ((((p5 ∧ (False ∨ (p2 ∨ (False ∧ p3)))) ∨ (p4 → p1)) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134898136066130936003688112473 : (((p5 → (True → (p1 → ((p3 ∨ (((p1 ∧ (p5 ∨ False)) → (p2 ∧ p3)) → (p2 → (p4 → p2)))) ∧ p1)))) → False) ∨ (True ∧ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225459313235215002837040373812 : (((p4 ∨ p1) ∧ p5) ∨ ((((False ∧ ((p5 ∨ p1) ∧ (p1 ∧ p4))) ∨ ((p2 → ((p1 ∧ True) ∧ (False → p1))) → p2)) ∨ True) ∨ (False ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166460782216035121764009617265 : ((p2 ∨ ((p4 ∨ p4) → ((True ∨ (p4 ∨ (p5 ∧ True))) ∧ ((p4 ∧ p2) ∧ (p1 ∧ False))))) ∨ ((True ∨ True) ∨ ((p1 ∨ (p4 → p4)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178527925820421966648506842884 : (((((p1 → p5) ∨ False) ∨ ((p3 → False) ∨ False)) → ((p2 ∧ False) ∧ p4)) ∨ ((p4 ∧ p1) ∨ (((p5 ∨ p4) ∧ (p5 ∧ p4)) → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625895990793668734120394389984 : ((((p2 → (((((p3 ∧ p1) → ((p2 → (p5 ∧ p4)) ∨ p3)) ∧ ((p5 ∨ (((p3 → p4) → p4) → False)) ∨ p3)) ∧ p1) → p3)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_657997820935989566966091113032 : ((((p2 ∧ (((p4 ∨ p3) → ((((p3 → True) → False) ∨ p4) ∨ p1)) → (False ∧ (((p1 → p1) ∧ p3) ∧ (p1 → p3))))) ∨ (False → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61465173271910219847054675880 : ((p1 ∧ ((((p4 → p1) ∧ (p2 ∧ (True → p1))) ∧ ((p3 ∧ (p5 ∨ (False → (p1 ∧ True)))) → (p1 ∨ (p3 → p1)))) ∨ (False ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243312267920051865830758887067 : ((p4 → p4) ∧ ((p5 ∨ p3) ∨ ((p1 ∧ ((p5 ∧ (p4 → (((False ∨ p1) ∧ p3) ∨ (False → p3)))) → p1)) → (((p4 ∨ True) → p5) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48395515208015794796922146216 : (((False → (p4 ∧ ((p5 → ((p4 ∨ True) ∨ (((True → p3) → ((p5 ∧ False) ∨ ((p5 → p2) ∨ False))) ∧ True))) ∧ p4))) → (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178305521236056172084701675287 : (((((False ∨ (False → p1)) → ((p2 ∨ p4) ∧ p3)) ∧ p4) ∨ (p4 → True)) ∨ (((((p3 ∧ p5) ∧ True) → (True → p1)) ∧ (False ∧ False)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116577204898698325616390011526 : (((p3 ∨ p3) ∧ ((((False ∧ (p3 ∧ ((True ∧ p4) ∨ True))) ∨ (True ∨ p2)) ∧ False) ∧ (False ∧ ((p2 ∨ p4) ∧ (p5 → True))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320289211682830781697158446987 : (p4 ∨ ((p4 ∧ False) ∨ ((False ∨ False) ∨ (p4 ∨ (True ∨ (p4 → (p5 ∨ (((True ∧ (p1 → ((False → True) → (p1 ∧ p1)))) → False) ∨ False)))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761460294334775255078174272201 : (((p3 ∧ ((p1 ∨ ((p3 → True) ∧ (((p1 → ((p5 ∨ (False → p1)) ∧ True)) ∧ p2) → (((p5 ∨ p4) ∧ False) ∨ (True ∧ True))))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45159483279739304049427501312 : (((True ∧ ((p5 ∧ (p1 ∧ ((False ∧ (True ∧ ((p3 → (False ∨ (p5 ∧ (False → (p1 ∧ p4))))) ∧ p3))) → p5))) ∨ (p2 → True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225795304737165333084902176910 : (((p5 → p5) ∧ p3) ∨ ((p1 → ((False → p1) ∧ True)) ∧ (((True ∧ p4) ∧ (((p4 → p5) ∧ p2) ∨ (p2 ∧ ((p4 ∧ p4) ∨ p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18950607775277979235677510436 : (((p3 ∨ ((((p2 ∧ p3) ∧ p4) ∧ p2) ∨ (((p3 ∧ (p1 ∨ True)) ∧ False) → (False → p2)))) ∨ ((True ∧ p5) → ((p2 ∨ p5) → p1))) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655697243615470077458709369839 : ((((((p1 ∧ False) ∨ (((True → p2) → ((p2 ∨ p4) ∧ p5)) ∧ (False ∧ ((p5 → False) → False)))) ∧ (True ∧ (p5 ∧ p2))) ∨ (p2 → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51259903788214904389006859957 : ((((p4 ∨ p2) ∨ ((((p1 ∨ False) ∨ (p5 → (p1 ∧ p1))) ∨ True) ∨ ((p5 ∨ p5) ∨ p4))) ∨ ((p5 → (p4 → p4)) → (False → p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_60094226005455417188111383230 : (((p3 ∨ False) → ((((((p3 ∧ p5) → p3) ∧ p1) ∨ p1) ∨ ((True ∧ p4) → ((p2 ∧ p2) ∨ (p4 ∨ p3)))) → ((True ∨ p4) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342138813703055447081303012862 : (p2 → (((((p4 ∧ False) ∧ ((p2 ∨ (p4 ∧ ((p5 ∨ (p1 ∧ (True ∧ p4))) → False))) → p3)) ∨ p4) ∧ p5) ∨ (p1 → ((True ∨ p4) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187591981663284111334873176899 : ((p3 ∨ (p2 → (p5 → ((p1 ∨ p5) ∨ (True ∨ (p2 → p5)))))) → (((p1 ∨ (False → (p3 ∧ (p1 ∧ p2)))) → False) → (True ∧ (p4 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ (False → (p3 ∧ (p1 ∧ p2)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ (False → (p3 ∧ (p1 ∧ p2)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204003687149793681648643443898 : ((p3 → (p1 → ((p1 ∧ p3) ∧ True))) ∧ (p4 → ((((p5 → p3) ∧ p2) ∨ p1) ∨ (p1 → (((p5 → p3) → p5) ∨ (p5 → (p4 → p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309628031244501866453042218439 : (p2 ∨ ((((p3 → (p3 → ((((p3 ∧ p1) → p1) ∧ False) → True))) → p3) ∨ (p5 → ((p3 ∨ p4) ∧ (p2 ∧ p3)))) ∨ (True → (p2 ∨ True)))) := by
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
theorem thm_5_vars_341007144479298496352286324803 : (p2 → ((p1 ∧ (((p2 ∧ p1) ∧ ((((p1 ∧ False) → p4) ∧ p5) → (False ∨ ((((False → (p1 ∧ p2)) → p4) ∨ False) → p1)))) ∧ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200933914013215326773491899070 : ((p1 ∨ (p5 ∧ ((True ∧ (p5 → p1)) → p4))) → ((p3 ∧ (True ∧ (((p5 ∨ p4) ∨ p4) ∨ p3))) → ((p2 ∨ p1) ∨ (p5 ∨ (p1 ∧ False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49522374348918667754232815651 : ((((((p3 ∧ (True ∧ (p2 ∨ ((p4 ∨ ((p4 → (True → p1)) ∨ False)) ∧ p5)))) → p1) ∧ p4) ∨ (p2 ∧ p1)) → (p5 ∧ (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149919102833355455724850073215 : ((p3 ∨ ((((((False ∨ True) ∧ ((p4 ∧ p5) → p4)) ∧ (True ∨ False)) → p2) ∧ (p2 ∨ p2)) ∧ (True → p5))) ∨ (p4 → (p3 ∨ (False → True)))) := by
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
theorem thm_5_vars_51425440085150167119410082147 : (((((((False → False) ∨ (True ∨ p2)) → p5) → (False → (True ∨ (p1 → True)))) ∧ (p4 ∧ p1)) → (((p1 ∧ (p2 → False)) ∨ p5) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119604471877396613256032990438 : ((p5 → (p1 ∨ ((True ∧ (((p2 ∧ p3) ∨ (p2 ∧ ((False ∧ p5) ∧ p4))) ∧ (((p1 ∨ False) → p2) ∨ (False ∧ p1)))) ∨ p5))) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780156391504926325490747491919 : (((p2 ∨ (((p4 ∨ ((p2 → False) ∨ ((p2 → p4) ∨ (((p5 ∨ p3) ∧ p3) → p5)))) ∨ (True ∧ (False ∨ True))) ∧ (False → (p2 → p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132991765689577241317498750732 : ((p5 ∨ ((False ∧ ((p4 → p2) → ((((p4 ∨ True) → True) → p1) ∨ ((((False → p4) ∧ False) → p5) ∧ p2)))) ∨ True)) ∧ (False → (p2 → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42107409065952428474606239739 : ((((p2 ∧ p4) → (((p2 ∨ (p3 → True)) → ((True ∧ (((((False ∧ (p5 ∨ False)) ∨ p3) ∨ p4) ∧ p4) ∨ p5)) ∨ p1)) ∨ p5)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_268591096990018151351931544 : (((((p2 → p4) ∧ ((p5 ∧ (p3 ∧ False)) ∧ (p1 ∧ p5))) ∨ p5) ∨ (((((p4 ∧ False) → p4) ∧ p4) ∧ (p2 ∨ p2)) → p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684608882338732748201030133495 : ((((((p2 ∨ False) ∧ True) ∧ (False ∨ ((p3 ∧ ((p1 ∧ p5) ∨ False)) ∨ (p5 → (p3 → p5))))) ∨ (((True ∨ p4) ∨ (p1 ∧ p2)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133639583876734452857197437038 : ((((p3 → (p4 → (((((p1 → p1) ∧ (False ∨ True)) ∨ p4) → p4) ∨ ((False ∨ p3) ∨ (p2 → p4))))) → p1) ∧ p5) ∨ (False → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156789631375370916807746254467 : (((p2 ∧ ((p4 → (((p5 ∨ (False ∨ True)) ∧ False) ∧ (p4 → p5))) ∧ (p5 ∧ (p4 → p5)))) ∧ p2) ∨ ((True → p5) ∨ ((True ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_326308169977454193714040168393 : (p5 ∨ (p4 → (((False ∨ (False ∧ p5)) ∨ p3) ∨ ((False → (p4 ∨ ((False ∨ (p2 ∨ (p3 ∨ (p1 ∧ ((p2 → p3) → False))))) ∧ p1))) ∨ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564748359279123161567749705528 : (((True → ((((p4 ∨ p3) → (((p1 ∧ (p5 ∨ p3)) → (p2 ∨ (((p1 ∨ p5) → False) → p4))) → ((False → p4) → p1))) ∧ p1) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606813436407824718040614058679 : (((((((p4 → ((True ∨ (False → p1)) ∧ ((False ∨ ((p3 → True) → False)) ∨ (p3 ∧ p2)))) ∨ False) ∧ (p3 ∨ (False ∧ p5))) ∧ p5) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698164958340908932307777392896 : (((((((p3 ∧ ((False ∨ p5) → p2)) → (p5 → False)) → p1) → p3) ∨ ((False ∨ (p2 → p3)) ∨ (((p3 ∧ (True ∨ p4)) ∧ False) → p5))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647171095989469307225094464521 : ((((p3 → (p5 ∧ (((p4 ∨ p2) ∨ ((p5 → (p4 ∨ (p5 ∨ (p2 ∨ p4)))) ∧ (p3 ∧ (p3 → p3)))) → (p4 ∧ (p1 → True))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191545592337250476993730858614 : ((p1 ∧ ((False ∨ (False ∨ (p3 → p1))) → (p4 ∨ p1))) ∨ (p3 → ((p3 ∨ (((p5 ∨ p3) ∨ p1) → (((True ∨ p4) ∧ p3) ∧ False))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133745815172390831593550718379 : ((((((p2 → p3) → (p4 ∨ (p4 ∧ p4))) ∧ p4) ∨ ((p1 ∨ (((p3 ∨ p2) ∨ p3) → p2)) ∧ (p4 ∧ p3))) ∧ p4) ∨ ((p1 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



