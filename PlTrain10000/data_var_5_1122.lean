variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48005540798049628261303587977 : (((((p5 ∧ (p2 → (p5 ∨ (False ∧ (False ∧ True))))) ∧ ((p2 → p1) → p4)) → ((((p1 → False) → p3) ∧ p3) → False)) → (p4 → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589743166322605639821647098208 : (((((((((p3 ∨ ((((p5 → (p2 ∨ p4)) ∧ (False ∧ p3)) ∧ p5) → True)) ∨ (True ∨ p1)) ∧ True) → p5) ∨ (p4 ∨ p5)) → p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151289241966267893166303076599 : (((p5 ∧ ((p4 → (False ∧ (False → (p2 ∧ p5)))) ∧ (((p3 → True) ∧ p3) ∧ (False ∨ (p1 ∧ p4))))) → p3) → (p2 ∨ ((p1 ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152151924976732589256003493657 : ((((p2 → (p5 ∧ (p4 → p3))) ∨ (p5 ∧ False)) ∨ ((((((p4 → False) ∨ False) → p4) → p4) ∨ p2) → p4)) → (((True → False) ∧ p4) → False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753048161285398879881941312268 : (((False ∧ (((p4 → p3) → (p2 → (False ∧ ((p2 ∧ (((p5 ∨ (p2 ∨ p4)) ∨ True) → (False → p1))) ∨ ((p3 ∨ p4) → p4))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58811229289042479681318160449 : (((p5 → p3) ∧ (((p5 ∨ ((((p2 ∧ True) ∧ (p4 → p5)) ∧ p3) ∧ p4)) ∨ (((p5 ∨ p5) ∨ p3) ∧ (p3 → (p2 ∨ p1)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48719624004750916850489273494 : ((((p1 ∨ (p4 → (True → p5))) ∨ (((False ∧ p1) → ((((p1 ∨ p1) → (p4 ∨ p5)) ∧ p3) ∨ p4)) → p3)) ∧ ((p1 ∧ p4) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173206716768938024295572583024 : ((p5 ∨ ((p1 ∧ (p4 ∨ (((p3 ∨ p5) → p2) ∧ False))) ∧ ((p2 → p3) ∨ p4))) ∨ ((False ∨ (False → (p5 ∨ False))) ∨ (True ∨ (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147492240830521221966461817638 : (((p5 ∧ (True → (((((((p2 ∨ (p2 → p5)) → p3) ∨ False) → (p4 ∨ p3)) ∧ False) → p5) → p2))) ∨ True) ∨ ((p2 → False) → (p1 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341032124393550297931921936175 : (p2 → ((p5 ∧ ((p5 ∧ (((p1 ∨ (p2 ∨ p2)) ∨ True) → (True → p1))) ∨ (p3 → (((p3 ∧ False) ∨ ((False → p3) → p3)) ∨ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178451748746017690743282695344 : ((((p2 ∧ p2) ∨ ((p5 ∧ (p5 ∧ p1)) ∧ p4)) ∧ (p3 ∧ (p3 → p2))) ∨ ((p2 → p1) ∨ ((True → (True ∨ (p1 ∧ (p3 → p2)))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230524603578595994296670240072 : (((False → True) ∧ p3) → (p4 ∨ (p1 ∨ (((((p2 ∨ p1) ∨ p3) ∨ p2) ∨ p5) ∧ (True → (((p3 ∧ p4) → (True → p1)) ∨ (True ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650009654703218828677129766638 : (((((p4 ∧ (((p3 → p2) → p2) ∧ (True → (p4 ∨ (p3 → (p4 ∧ ((p4 ∨ p5) ∨ p4))))))) ∨ ((True → True) ∨ True)) ∧ (False → p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256606136564895497204806394318 : ((p1 ∨ True) → ((p3 → (True ∧ (p1 ∨ False))) ∨ (p3 ∨ ((p4 ∨ ((p4 ∧ ((p5 ∧ p1) → p5)) ∨ (p4 → p3))) ∨ ((True ∨ p5) ∨ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_803989393472403757817510532878 : (((p3 → ((((p4 ∨ (False ∧ (((p1 ∨ (p4 ∧ ((False → (p4 ∧ p5)) → p1))) → p4) ∧ p4))) ∨ p1) ∧ p2) ∨ ((p1 ∨ p1) ∨ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699978225145865896454024905734 : (((((((False → p3) → p2) → True) ∨ (p4 ∨ (p2 → (False → True)))) → (p3 ∧ (p5 ∧ (((p2 ∨ p5) ∨ (p3 ∧ p5)) → (True → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137037250253177327449302607416 : (((p5 ∨ p5) → (p4 → (p1 ∨ ((True ∧ (p3 → False)) ∧ ((p3 → (((p2 ∧ (p5 ∧ p4)) ∨ p4) → True)) → p5))))) ∨ ((True ∨ p1) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148429778012342436833557363071 : ((((p2 ∧ p3) ∨ (((False ∧ ((p3 → p1) ∨ p3)) → p5) ∨ (p1 ∨ True))) → ((True → p3) ∧ (p3 → p4))) ∨ (False → ((False ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156742465159231763051300616631 : (((((p5 → p4) ∧ p5) ∧ ((p1 ∧ ((p1 ∧ p5) ∧ (p2 → ((p5 ∧ p1) ∨ p5)))) ∧ p2)) ∧ p5) ∨ ((p1 → (p1 ∨ p5)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320382612126025342233172103624 : (p4 ∨ ((True ∧ p4) → (p2 → (((((True → ((p2 → (True ∨ ((p4 ∧ p3) → p1))) → False)) ∨ ((p4 → p4) → p5)) ∨ p5) → False) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46300487489709906307489541487 : (((((((p1 → p2) ∧ ((p5 ∨ p4) → p4)) ∨ (p4 ∧ p3)) ∨ ((p2 ∧ p3) ∧ (False ∧ p2))) → (p1 ∨ (p2 ∧ p2))) ∧ (True ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247418739746471455748490803591 : ((False ∨ p2) ∨ (((p3 → ((((p1 ∨ (p1 ∧ (True → p4))) ∨ p4) ∨ (p2 ∧ (True ∨ p3))) ∨ (True ∧ (True ∨ p2)))) ∧ False) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164827744741362194495471457633 : ((((p4 → p3) → (p3 → ((((p3 ∧ (True → p4)) ∨ True) → (p3 ∨ p4)) ∧ False))) ∨ p3) ∨ ((p1 ∨ False) → ((p2 ∨ (False ∨ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312771846926455500551514596245 : (p3 ∨ ((((p1 ∧ (p3 ∧ False)) ∧ p3) ∨ (p1 → (p2 → ((p3 ∨ (((p4 ∧ ((p2 ∨ (p2 ∧ p4)) ∨ False)) ∧ p2) → p2)) ∨ p5)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200922478770911850108836031359 : ((p1 ∨ ((True → (p3 ∧ False)) ∨ (p5 ∨ False))) → (p3 → ((p1 ∧ (p5 ∨ (((p5 ∨ True) → False) ∨ p4))) ∨ ((p3 ∨ (False ∨ p4)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337804923217690473919417852622 : (p1 → (((True → (p3 ∧ p3)) ∨ ((((p5 ∧ (p4 ∧ (p5 ∨ False))) ∧ p1) ∧ p3) → p4)) → (((p1 → ((p2 ∨ True) → False)) ∧ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134960552438707185291810968896 : ((((p4 ∨ ((p3 ∨ p3) → ((p2 ∧ (p5 → p3)) ∨ p4))) ∨ (p4 ∨ ((p5 → (False ∧ p4)) → p4))) ∧ (p3 → True)) ∨ (False → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60219352203505646613696732029 : (((True → p1) → ((p5 ∧ p2) ∧ (True → (False ∧ (((p2 ∨ p4) ∨ ((True ∨ (p4 → (p2 → (True ∧ p3)))) ∧ True)) ∨ (p4 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113505491791637549778191500227 : (((((((True ∨ p1) ∨ (False ∧ p1)) ∨ ((False ∧ p1) → p1)) ∧ (False ∧ p4)) ∨ (False ∨ ((p4 ∧ True) ∧ p5))) ∨ (False → True)) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57432999599741299929694889065 : (((p3 ∨ (p3 ∨ False)) ∨ (p4 ∨ ((p2 ∨ (True ∨ p5)) ∨ (((p3 ∧ True) ∨ ((p4 ∧ True) ∧ (((True → False) ∨ p4) → p3))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42191855404741927360050352894 : (((True ∧ ((p5 ∧ ((p5 ∧ (p5 ∨ (p4 → p2))) → p4)) → ((((True ∧ (p2 → (p5 ∧ p2))) → (p4 ∨ False)) ∧ p1) ∨ p4))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234241491022213821774929588546 : ((False → (p2 ∨ p3)) → (p5 ∨ (((p4 ∧ p1) ∨ ((p2 ∧ ((p2 ∧ (True ∨ True)) → True)) ∨ (p3 → (p1 → p4)))) ∨ (p4 ∨ (p4 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245644671071719811210449782491 : ((p3 ∧ p1) ∨ (((((((True ∧ p4) ∧ (p5 ∨ (((False ∧ (p1 → False)) → p4) → p4))) ∧ (p2 ∨ (p5 ∨ p5))) ∨ p3) ∨ p5) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159434475293732314965162540872 : ((((True ∧ ((p3 ∧ (False ∨ (((p5 ∨ p1) ∨ p3) ∧ False))) ∨ (False ∧ True))) → (False → False)) ∧ p2) → ((p2 → False) → (p3 ∧ (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358159102858609821378087614807 : (p5 → (p3 ∨ ((True → (p2 ∧ (p2 ∧ (((((p2 ∨ (((p2 → p1) ∧ (p4 → p1)) → p2)) ∧ False) → (p5 ∧ p3)) → p2) ∧ True)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41402114715271599495858349005 : ((((((((p3 ∧ p2) ∧ False) ∨ (False ∨ (p1 → (p5 → p4)))) ∧ p2) ∧ p5) ∨ (True → (False ∨ ((p5 → (p5 ∧ p1)) ∨ False)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158545831944155991562916187065 : (((p3 → p4) → ((p5 → False) ∧ (((True ∨ ((p1 ∨ (True ∧ p1)) → p1)) ∨ p4) → (p3 ∧ False)))) ∨ ((p5 → ((False → True) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42403716767136718464933681142 : (((p4 ∧ (True → (False ∧ ((p1 ∨ ((False → (False ∨ True)) ∧ (p1 → False))) → (False ∨ ((p5 ∨ (p1 → p5)) → (p1 ∨ p2))))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158911665388031548482118412741 : ((p1 ∨ (((p5 ∨ p1) ∧ p3) ∧ (False ∨ (p4 ∧ (((p1 ∨ ((False → p5) ∧ p5)) ∧ p5) ∨ True))))) ∨ (((p4 → (p5 ∨ False)) ∧ p4) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612296712743456713642741094394 : (((((False ∧ ((p4 ∨ (p2 → ((False ∧ False) ∧ (True ∧ (p1 ∧ (p5 → (p2 ∨ ((p4 ∨ False) ∨ True)))))))) ∧ p3)) ∧ (p1 ∧ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46605995547221300610479914708 : (((p2 ∧ ((((p4 → True) → p2) → (p4 ∧ (True ∧ ((True ∧ (p5 ∨ p2)) → True)))) ∧ (p1 ∧ ((p3 → True) ∧ p1)))) ∧ (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68154102531088958138271274422 : ((p3 → (((((p5 ∨ False) ∨ p5) ∧ p4) ∧ ((((((True ∧ True) ∨ (p1 ∧ True)) ∧ (p4 → p1)) → (p2 → p5)) ∨ p4) ∨ True)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133665730740778537645081263792 : (((((((((p1 ∨ p5) → p2) ∧ ((((p3 → p3) → False) ∧ p2) ∧ True)) → p2) ∧ p4) ∧ p1) → (p4 ∧ p2)) ∧ p2) ∨ ((False ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52370594627470800072259966000 : ((((p1 ∨ ((p4 ∨ (((True ∧ False) ∨ False) ∨ p4)) → p4)) → (True ∧ p2)) ∧ (p5 ∧ (((p4 → ((p4 → p3) ∧ p5)) ∧ p3) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51328793974672771696619070247 : (((p1 → (((((p2 ∨ (((p4 ∨ p5) → p4) → p4)) ∧ (p2 ∨ False)) → p1) ∨ p1) → p2)) ∨ (True ∨ ((True ∨ p2) → (False ∧ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15177633795900032214895620777 : (((p5 ∨ ((True ∧ (p4 ∧ (((p2 ∨ (p1 ∧ (((p1 ∨ True) → p2) ∨ p5))) ∨ (p1 ∧ (p3 → p1))) ∧ p4))) ∧ p5)) ∨ (p2 → True)) ∧ True) := by
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
theorem thm_5_vars_120596452139706686558920489439 : ((((p5 ∨ (True ∧ ((True ∧ p3) ∨ ((((False ∨ p4) → ((p2 ∧ p2) → p3)) → p3) ∨ (p4 ∧ (p3 ∧ p1)))))) ∨ p1) ∨ p1) → (p2 ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110838356602495145332989059766 : ((((p1 ∨ ((p2 ∨ p4) ∧ (((True ∧ p4) ∨ ((p1 → ((p5 ∨ p5) ∨ True)) ∧ ((True → True) → p3))) → p4))) ∨ p3) ∧ p5) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41733501694742026119949251730 : (((((p2 → p4) → (p4 → p3)) ∧ (p5 → ((p4 ∨ ((False ∨ (p2 → (p5 ∧ ((p5 ∧ p3) → p2)))) ∨ False)) ∧ (p1 ∨ p1)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709212315881844224340036333096 : (((((p1 → p3) ∧ (p3 ∧ ((p2 → p4) ∨ p3))) → (((((p1 → p4) ∨ (p5 ∨ ((p2 ∨ p1) ∧ False))) ∨ (p5 → p4)) ∨ True) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166849282644038598418348649270 : ((((((p5 ∨ p5) ∨ ((p1 ∧ p1) ∧ (p4 → p1))) ∨ (p3 → (True ∧ p3))) → False) ∧ True) → (p2 ∧ (p4 ∨ ((p1 → p4) → (p2 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 ∨ p5) ∨ ((p1 ∧ p1) ∧ (p4 → p1))) ∨ (p3 → (True ∧ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (((p5 ∨ p5) ∨ ((p1 ∧ p1) ∧ (p4 → p1))) ∨ (p3 → (True ∧ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153557988792054489912246964946 : ((True → (p3 ∨ ((p3 ∧ (p3 ∨ p2)) ∨ ((p2 → (True → (True → (p2 ∧ (p3 ∨ (p1 ∨ p4)))))) → p3)))) → (p1 → ((True → False) → False))) := by
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
theorem thm_5_vars_351208611366274619557344475164 : (p4 → (((((p4 → p2) ∨ (p5 → (p3 ∨ p5))) → (p5 ∧ (p2 ∨ ((((p1 → p2) ∨ False) → True) ∨ p2)))) ∧ p1) ∨ ((p3 → p4) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305588201686373148391650559044 : (p1 ∨ ((((p3 ∧ p5) → ((p2 ∧ p2) → True)) ∧ (p2 ∧ (p1 ∧ False))) ∨ (p4 ∨ ((p1 ∨ ((p4 ∨ False) → (False ∨ p2))) ∨ (p5 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134408994221025082244174183806 : (((p1 → ((p5 ∨ False) → (p2 ∧ ((p1 ∨ p5) → ((p1 ∨ ((True ∧ (p5 ∧ True)) → p3)) → (p5 ∧ False)))))) ∨ True) ∨ ((p5 ∨ p4) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251184072460859635105330583583 : ((p2 → p1) ∨ (((((False ∨ p2) ∨ False) ∧ (p3 ∧ (p1 ∨ (((((p5 ∧ (p1 ∨ p1)) ∨ p5) ∧ p4) ∨ True) ∨ p1)))) ∨ p3) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328893702339053820863876966009 : (True → (((p4 → p1) → ((False ∧ p3) ∨ (p1 → p3))) ∨ (p1 → (False → (p4 ∧ ((p4 → ((False ∧ p3) ∨ (p3 ∧ (p3 ∨ p3)))) → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39874478967388670405040992164 : (((p2 → ((p4 ∧ ((p5 ∨ (((p5 ∨ False) ∧ p1) ∨ (True → (p5 → (p1 → (p4 ∨ p3)))))) ∨ (True ∧ (p3 → p4)))) → p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114096472667712243506849315714 : (((False ∧ (((p1 ∧ (False ∨ p1)) → (False → ((False ∧ (p1 ∨ (p2 → p5))) → (False ∧ p1)))) → p4)) ∨ (p5 → (True ∨ p2))) ∨ (p2 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329129539789230936479954862670 : (True → ((p5 ∧ ((p4 ∨ p1) ∨ p2)) ∨ ((p3 ∨ (True ∨ (p4 ∧ ((p4 ∧ (p4 ∧ True)) → (p2 ∨ p1))))) ∧ ((p5 → True) ∨ (p4 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617244462652589821665116873162 : (((((p4 ∧ ((p3 ∧ (p4 ∧ (p5 → p5))) → False)) ∨ (((((p3 ∨ p5) ∧ p2) ∨ (True ∨ p2)) ∨ (False ∧ p2)) ∨ (p3 ∨ p4))) ∨ p3) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42810609073676871377225990603 : (((p1 → ((True ∧ ((False → ((((p1 → ((p4 ∨ (p5 → (p2 ∨ p3))) → p3)) ∧ p4) → (True ∧ True)) ∨ p5)) ∧ p4)) → p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113741784089590777219112508763 : ((((((p1 → True) ∨ (((p1 → p4) ∧ True) ∨ (p2 ∨ p1))) ∨ p2) ∧ (((p4 → p1) ∨ p4) ∨ (p3 ∧ p1))) → (True ∧ p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673824389929304860623694222514 : (((((True → p1) ∨ ((((p4 → p1) ∧ (((False ∨ p3) → (((p3 ∧ p4) → p3) → p1)) ∨ True)) ∨ p3) ∨ False)) → ((True ∨ p1) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114349534799858641345392827295 : (((p1 → ((p2 ∧ ((p3 ∨ ((p2 ∧ (p1 ∧ False)) ∧ ((p2 ∧ p3) ∨ False))) ∧ True)) ∧ True)) ∧ ((p2 → p3) ∧ (False ∨ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701327154204837855287765519809 : ((((((p2 ∨ (False ∨ False)) ∧ True) ∧ ((p1 ∧ False) ∨ True)) ∧ (p5 ∧ ((True ∧ (p2 ∧ p1)) ∧ ((p3 ∧ p2) ∨ ((p3 ∧ p4) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780616695650435640828633031118 : (((p2 ∨ ((((p1 ∧ p3) → (True ∨ ((p2 ∧ p5) → p4))) → p5) → (p4 → (((True → (True → p4)) ∨ (p1 ∧ (p5 ∧ False))) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190813064055348905534807681678 : (((False ∧ (((p5 ∧ p1) → p3) ∧ False)) ∨ (p2 ∨ p4)) ∨ ((p1 ∧ (False ∨ p3)) → (p2 ∨ ((False → (False ∨ (p5 ∧ (p4 ∨ False)))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137426084455979400220600602601 : ((p4 ∧ (((p2 → (p5 ∨ (p5 ∧ (((False ∨ p5) ∧ (p3 ∨ p4)) → ((p1 → p3) ∨ p3))))) ∨ (True ∨ p3)) → p1)) ∨ (p4 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219831471471570372171426526271 : ((p3 → ((True → p4) ∨ p3)) → ((((p1 → p3) ∨ ((True → (((p2 ∧ True) → p2) ∧ False)) ∨ True)) ∨ (p2 ∨ (p3 ∨ p5))) ∨ (p3 → False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658865864612321466905040489554 : ((((True → (p1 ∧ (((((False → p4) → (p3 ∧ p4)) ∨ (p4 → (p2 ∨ (True ∨ (False ∧ p2))))) ∧ p2) ∨ (p5 → p4)))) ∨ (True ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136439498172032859852635323933 : ((((p2 ∧ p1) → (p5 → True)) → (True → (p1 ∧ (True ∧ (p3 ∨ ((p1 ∧ ((p5 ∨ False) ∧ p4)) → (p4 → p2))))))) ∨ (p4 ∨ (True ∧ True))) := by
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
theorem thm_5_vars_8920007699963896459925942738 : (((((False ∨ (False ∨ (((p4 ∨ (p4 ∨ (p4 → (p4 ∨ (p5 ∨ p1))))) → True) ∨ True))) → False) → (p1 ∨ ((p1 ∨ p3) ∧ False))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (False ∨ (((p4 ∨ (p4 ∨ (p4 → (p4 ∨ (p5 ∨ p1))))) → True) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300980313443807747050943772347 : (False ∨ ((p1 → (False ∧ ((((p3 ∨ (True ∨ p5)) ∨ True) ∧ p5) ∨ p4))) ∨ ((False ∨ True) → (False ∨ ((p5 → p5) → (True ∧ (p1 → True))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113848991213843656852510256517 : (((True → ((False ∧ ((((((p4 → (p1 → p5)) ∨ p3) ∧ (p4 ∨ p3)) ∨ p2) ∨ True) ∧ (p3 ∧ p1))) → p5)) → (p1 ∧ p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135886322885281225012097833350 : (((p4 ∨ ((p2 ∧ (((p4 → False) ∨ (p5 → True)) → p3)) ∨ p5)) ∨ (((p1 ∧ (True ∧ (False ∨ True))) → p2) ∧ p4)) ∨ ((False → p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774586094226987228484199206417 : (((False ∨ (((((False ∨ True) → True) ∨ p4) → (p2 ∨ (p2 → (p4 ∧ p5)))) ∨ (((False ∨ p1) ∧ p3) ∧ (p4 → (p5 ∨ (p2 ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257844884232316028726426061370 : ((p3 ∨ p5) → (p5 → (((((p1 ∨ ((p5 → p5) ∨ p4)) ∧ (p4 ∨ p1)) ∨ (((True → p1) → True) ∧ True)) ∨ ((True → p4) ∨ p1)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148011771259023774167744929026 : ((((p1 ∨ (p2 ∧ (((p4 → p4) → p5) ∧ (p4 ∨ (p4 → True))))) ∧ ((p3 ∧ p5) ∨ p1)) ∨ (p3 → False)) ∨ (p5 → (p3 → (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650209500248236179387518455822 : ((((((p1 ∨ (p5 ∨ (False ∨ (p1 ∨ p5)))) ∧ (((p2 ∧ p1) ∧ (p2 → True)) → False)) ∨ (p1 ∨ ((p3 ∧ p1) → p1))) ∧ (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42923924151122932350107084483 : (((p4 → (((p3 ∨ (p2 ∨ (p3 ∨ (((p2 ∧ False) ∧ ((p4 ∧ p4) → p1)) ∨ p3)))) ∧ ((p4 ∧ p4) ∧ (p5 → p2))) ∨ p4)) ∨ p5) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678943121331317936392857675922 : ((((p4 ∧ (((p5 ∧ (p4 → (p2 ∧ p3))) → (p4 → (((p2 ∧ p4) ∨ (True ∨ True)) → False))) → p2)) ∨ (True → ((p1 → p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160511863416922438925397635392 : (((False ∨ (True ∨ ((p4 → (False ∧ p1)) → ((p4 ∨ p5) ∨ False)))) ∧ (p2 → ((True ∧ p1) ∨ p2))) → ((((p5 → p2) → p4) → p4) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
theorem thm_5_vars_178068237760553404614147267139 : (((((True ∨ p1) ∨ ((p3 → False) ∧ ((p3 → p3) ∨ True))) ∨ False) → p3) ∨ ((False → False) → (p4 → (p5 → ((True ∨ False) ∨ (p2 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762007078813798844851065208618 : (((p3 ∧ ((False ∨ (((p1 ∧ ((p5 ∧ (False ∧ False)) ∧ p4)) ∨ (p1 ∨ True)) → (True ∨ ((((p5 ∨ p2) → p4) → False) ∨ p3)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56365140670093249701765899344 : ((((True → (True → p4)) ∨ p5) → (((((p5 ∧ p1) ∨ p2) ∧ p2) ∨ ((((p2 → p5) ∧ (p2 ∨ False)) ∨ p4) ∧ p4)) ∧ (p5 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619702512234833357590848921613 : (((((p5 ∧ p1) ∧ (((False ∨ p2) ∧ (p3 ∧ ((p2 ∨ p1) ∨ (p1 → (p4 ∨ p2))))) ∨ ((p1 → (True → p4)) → (True → p5)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_53717199389912655175821393753 : (((p4 ∨ ((p3 ∨ True) → (p1 ∧ ((True ∧ p2) ∧ False)))) ∧ (p4 ∧ (((p2 ∧ (p4 ∧ p3)) ∧ ((p3 ∨ (True → True)) ∧ p4)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749042245685605418234583601363 : ((((p4 → p5) → (p2 ∨ ((p3 → (p5 → (p2 → ((p5 ∨ p2) → (False ∨ (((False ∧ (p2 ∧ p5)) ∧ p3) → (p3 → p3))))))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790730483156901150167977997191 : (((p5 ∨ (True → ((p1 ∧ (p3 ∧ ((p1 ∨ p4) ∨ False))) → ((((False → (p2 ∨ p2)) ∧ (p5 → (True → p4))) ∨ (False ∧ False)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44061139364756080723965768022 : (((((((p5 → (p4 → p2)) → (((((p3 ∨ p5) ∧ True) ∧ p1) → p1) ∧ p1)) → (False → p1)) ∨ p2) ∧ ((p1 ∧ p4) → True)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745736675718607465924359142962 : ((((True ∨ p5) → (p3 ∨ (p1 ∨ (p2 ∨ ((p2 ∨ (p5 → (p1 → (False ∨ (p1 ∨ (p1 ∧ p2)))))) → (((p3 ∧ p4) ∨ True) ∨ p4)))))) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246360159194055588571324175202 : ((p4 ∧ p5) ∨ (p3 ∨ ((p5 ∨ ((False ∧ (p4 → p4)) ∧ p3)) ∨ ((False ∧ p4) ∨ ((False ∨ (p1 → (((p4 ∧ False) ∧ p5) → p1))) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53929098726552433820917515258 : (((p5 ∨ ((((p1 ∧ (p5 → True)) ∧ p1) ∨ p1) → p4)) ∨ ((((p1 ∧ p5) ∨ (False → ((p2 → False) ∨ True))) → p3) ∨ (p5 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51268477066439226281535064165 : ((((False → p4) → (((p1 → ((True → p4) ∨ (p1 → p5))) ∨ ((p3 ∨ p1) → False)) ∨ False)) ∨ ((False → p4) ∨ ((p2 ∧ True) ∨ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137959121820832784680450996159 : ((p5 ∨ ((p4 → (False ∨ ((p4 ∧ (False ∧ False)) ∨ (((True → ((p5 ∨ p5) ∧ p1)) → p4) ∧ (p3 → p2))))) → p3)) ∨ ((p3 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309669634063284505239616380221 : (p2 ∨ (((True → (True ∧ (False ∨ (((p5 → p3) → (((p5 ∧ p3) ∨ p1) ∧ (p4 ∧ (p4 ∧ p3)))) → p1)))) ∧ True) → ((p4 ∧ p3) → p3))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166281031995355162579324406186 : ((p4 ∧ ((((True → False) → False) → ((p5 ∨ (p2 ∨ ((False ∧ False) ∧ True))) ∨ p4)) ∨ p4)) ∨ (False → ((False ∨ (p3 ∧ p2)) → (False ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186524624803034711790660857221 : (((((True → p4) → (True → (p4 ∨ p3))) ∨ p5) ∨ (p4 ∧ p3)) → (True ∧ (((p2 ∨ (p2 ∨ True)) ∨ p4) ∨ (p1 → (p3 ∧ (p5 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
    case inr h4 =>
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
theorem thm_5_vars_136440078862026333691849959079 : ((((p5 ∧ p4) → (p5 ∨ False)) → (((p5 → (False ∧ ((True → True) ∨ (((False ∧ p5) ∨ True) ∧ p3)))) ∧ p1) → p2)) ∨ ((True ∨ p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



