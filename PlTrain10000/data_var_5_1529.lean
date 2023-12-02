variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673762417211251962150655879494 : (((((p5 → p1) ∧ ((True ∧ False) ∨ (p1 → ((False ∨ p4) ∨ (False → (p4 → ((p2 ∨ True) ∧ (False → True)))))))) → ((False ∨ p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708002327106638802704530878898 : ((((p1 ∨ ((p2 ∧ p3) ∨ ((False ∧ False) ∧ p3))) ∨ ((((False → (p5 → ((p1 → (p2 → p1)) ∧ p4))) ∨ False) → (False ∧ p1)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159664704220602048248175735633 : (((((((p3 ∧ True) → p5) ∨ p1) → (p5 ∧ ((((p5 ∧ p3) ∨ p2) ∧ p4) → p1))) → p3) ∨ False) → ((p3 ∧ (p5 ∧ p2)) → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700048010624067032916805579259 : (((((p2 ∨ (p4 ∧ p3)) ∧ (p4 → (p3 → (p2 → (p3 ∧ p4))))) → (((p5 ∧ (p2 → p1)) ∨ (((p1 → p4) ∨ p5) → True)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791619993613125064247581074612 : (((True → ((((p4 ∧ ((p4 → ((p4 ∨ ((p4 ∧ p2) ∧ (p1 → True))) → (p1 ∨ p4))) ∨ (False ∨ p4))) ∧ p1) ∨ (False ∧ False)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55018995961923663242104694960 : (((False ∧ (((p5 → p5) → True) ∨ p2)) ∧ (p4 ∧ ((p1 ∨ (False ∧ p5)) → ((p3 ∨ ((False ∨ (p3 ∧ p3)) ∨ (p3 → p4))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657138669146180708117535434229 : ((((((p5 → True) → False) ∨ ((p1 ∨ ((p5 ∧ p2) ∧ (True ∨ (((p4 ∨ (p4 ∧ p5)) ∧ (p4 → p4)) ∨ p4)))) ∨ True)) ∨ (p3 ∨ p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191610914424107532719665113646 : ((p3 ∧ (((p4 ∨ p3) ∧ p1) ∧ (p2 → (False ∧ False)))) ∨ ((p4 ∨ (False → (((True ∧ (p5 → ((False ∧ p4) ∨ False))) → p1) → True))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171363007187900434322922165067 : (((((p1 ∨ (p4 ∨ ((p3 ∨ p2) → (p5 → p2)))) ∨ p3) ∨ (p3 ∨ p1)) ∧ p5) ∨ (((((p4 → p5) → False) → p4) → p5) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675171989330153573022608139597 : (((((((p2 → (((p5 → False) ∧ True) ∧ (True → False))) ∧ p3) → (p3 → ((p5 ∨ p4) ∧ p1))) ∨ True) ∧ ((p5 → p5) ∧ (p2 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40837668767988578714998050685 : ((((p3 → ((((((((p5 ∧ False) ∧ p2) ∧ (p3 → (True → False))) ∧ (p5 → (p4 → p3))) ∧ p1) ∨ p3) → p2) ∨ False)) → False) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185211848168617741108579426847 : ((True ∧ (p4 ∨ (p4 ∨ (((p3 ∨ (p4 ∨ p5)) → False) → p2)))) ∨ (((((p1 ∨ True) ∨ p4) ∨ p5) ∧ p2) → (p5 ∨ (True ∨ (p1 ∧ p4))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655376514675613312070439640011 : ((((((p3 ∨ (p1 → ((((p3 → True) ∧ False) ∨ False) ∨ ((p1 ∧ (p2 ∧ (False ∨ p3))) ∨ False)))) → False) ∨ (p5 → p3)) ∨ (p1 → p1)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_639986316348862622798574740965 : (((((p2 ∨ (p4 ∧ p5)) ∨ ((False ∧ ((((True → (p3 → (p4 → p5))) ∨ p2) ∧ p3) → (False → (p5 ∧ p4)))) → (p5 ∧ p3))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48529047298920685330259724662 : ((((p1 ∧ (((((p3 ∧ False) → ((p1 ∧ p1) → (False ∨ ((False ∧ True) → p5)))) ∨ False) → p1) → p5)) ∨ p2) ∧ (p4 ∨ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40139372135073546722600910855 : ((((((p1 → (((p5 → p4) ∨ ((p3 ∧ (False → (p2 → p4))) ∨ p5)) ∧ p3)) ∧ p1) → (((p2 → p1) ∧ p5) ∨ p5)) ∧ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233785284043478080543404349711 : ((p3 ∨ (p5 ∨ p2)) → (p4 → (False ∨ ((False ∨ ((p1 ∨ (((True ∧ ((p1 ∧ p5) ∧ (p1 ∨ p4))) ∨ p5) → p3)) → (p4 ∨ p5))) ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136111205078187979565494775556 : ((((p1 → False) ∧ (p2 ∧ ((p4 → False) ∧ p2))) ∨ ((p1 → ((p2 ∧ p4) ∨ ((p4 ∨ (p2 ∧ False)) ∨ p4))) ∨ False)) ∨ ((p5 → True) ∧ True)) := by
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
theorem thm_5_vars_257864611353674274472343943658 : ((p4 ∨ True) → ((((p2 ∨ ((p3 ∨ p2) → (p3 ∨ p5))) ∧ ((((True ∧ False) ∨ (p4 ∨ True)) ∨ p2) ∧ p4)) ∨ (False → p1)) ∨ (False ∨ p3))) := by
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
theorem thm_5_vars_248804938906870926052211858439 : ((p3 ∨ p4) ∨ (((p1 ∧ ((p4 ∧ (p2 → (p1 → (p5 ∧ ((p3 ∨ (p1 → p2)) → True))))) ∨ p4)) ∨ (((False ∧ p3) → p2) ∨ False)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137010116256564810074447720515 : (((p1 ∨ p3) → ((p5 ∨ (p4 ∨ (((False → p2) ∨ p1) ∨ True))) ∧ (((True → p3) ∨ p2) → (p2 ∧ (p5 ∧ p2))))) ∨ ((p3 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89072934508002471352116861171 : ((((p5 ∧ False) ∨ p4) ∧ (((p2 → (p5 ∨ True)) → ((p3 ∧ p5) ∧ (p2 ∧ (((p3 → True) ∨ ((True → p2) ∨ p1)) → p5)))) ∧ p3)) → p2) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p2 → (p5 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147350186630854332238597445556 : (((((((p5 ∧ (p4 ∧ ((p5 ∧ p4) ∨ False))) ∧ p1) → p2) ∨ (p3 ∧ p3)) ∧ ((p3 → p3) → p5)) ∨ p1) ∨ ((True ∨ p4) ∧ (p5 → True))) := by
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
theorem thm_5_vars_142504937154057912896257196954 : ((True ∨ ((((True ∨ p5) ∨ ((p1 ∨ (p5 ∧ (True ∨ ((p4 ∧ (p3 ∧ p4)) → True)))) ∧ (p4 ∧ p1))) → p2) ∧ p5)) → ((p2 → p1) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337409154699286177987667630071 : (p1 → (((((p2 → ((p4 ∧ p5) → ((p1 ∨ ((p3 → False) ∨ (p1 → p4))) ∧ (False → p4)))) ∨ p4) ∨ True) ∨ p4) → ((p2 → False) ∨ True))) := by
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116579757315247439252674410131 : (((p3 ∨ p5) ∧ (((p2 ∨ p1) → (((p1 ∧ ((p1 ∧ p1) → p3)) → (False ∨ False)) ∨ ((p2 ∨ (p3 ∨ p5)) ∧ False))) ∧ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719014225209478853421870125274 : (((((p2 → p3) → (p2 ∧ True)) ∨ ((False ∧ (((p3 ∨ (False ∨ (p2 ∧ (p2 ∨ p1)))) ∨ ((p3 → False) ∧ p3)) ∧ False)) ∧ (True ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315126877265791506961533949498 : (p3 ∨ (((p4 ∨ p5) ∨ ((p1 ∨ p4) ∨ True)) ∨ (((p5 ∨ p2) → False) → ((p2 → ((True ∨ ((p4 ∧ False) ∨ p2)) ∨ p2)) ∨ (p1 → p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50987629357583314656497615238 : ((((p2 ∧ p1) ∧ (True ∨ ((p2 ∨ p3) ∧ ((p2 ∧ p4) → ((p3 ∨ p5) ∧ (p4 ∧ p2)))))) ∧ ((False → (p2 ∧ (p2 ∨ False))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61810890072004388668319952048 : ((p2 ∧ ((((p1 → False) → (p1 ∧ (p4 ∨ ((False ∧ (True ∧ p4)) ∧ (True ∧ (p1 ∧ p4)))))) ∧ (((p5 ∨ False) ∧ p4) ∧ p5)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251862115768628955787961166088 : ((p3 → p5) ∨ (((((p4 ∨ True) ∧ True) → (p4 ∧ ((True ∨ False) ∧ (False ∧ p5)))) ∨ p4) → ((p2 → True) → (p5 ∨ (p4 ∨ (True ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618778487810107051237395990790 : (((((True ∧ (p5 ∧ p5)) ∧ (p5 ∨ ((((False ∧ (p4 → ((p5 ∨ (True → p4)) → True))) → p5) ∨ (True ∧ p1)) ∧ (p1 ∨ p5)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_172589537798139473925307880383 : ((((p5 → p4) ∨ p2) → (((p4 ∨ (False → p1)) → ((p2 ∨ p5) ∨ p5)) → p2)) ∨ (p5 → ((p3 ∧ False) → ((p1 → (p2 ∨ True)) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50514412734939210827831524785 : ((((((True → p1) → p1) ∨ (p2 ∨ ((p4 ∧ (True ∨ ((p3 → False) ∧ (p3 → True)))) → True))) ∧ p3) → (((True ∨ p5) → p1) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676330187354424452195432519083 : (((((p1 ∨ p3) ∧ (True → (((p2 ∨ (((p3 ∧ True) ∧ p3) → (p3 ∧ (False ∧ p4)))) → False) → p4))) ∧ (p1 → (p3 ∨ (p5 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66006064374518377699668268799 : ((p4 ∨ (p5 → (p1 → ((True → p5) ∧ (p4 ∨ (((((p1 → True) → ((p5 ∨ (True ∨ p5)) → p2)) ∧ p3) ∨ (p1 ∧ True)) ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119088482365378447247634079002 : ((p1 → ((((p3 ∨ (p1 → True)) ∧ (p5 ∧ (p2 ∨ (p3 ∨ False)))) ∧ p4) ∨ (p3 ∧ ((p3 ∨ ((p4 ∧ p5) ∨ p2)) → p5)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247303742038785606527236354698 : ((False ∨ False) ∨ ((((((p2 → ((p3 ∨ p3) ∨ p2)) → p1) ∧ p2) ∨ ((False ∧ (p3 ∧ p4)) ∧ p5)) → p5) ∨ (p5 ∨ (True ∨ (p2 → p2))))) := by
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
theorem thm_5_vars_263101861248166777711580119960 : (True ∧ (((((True ∨ (((p3 ∧ (((p3 ∨ p5) ∧ p5) → ((p5 ∨ p3) ∧ p4))) ∧ p5) → p1)) ∨ p4) → p2) ∨ (p5 ∧ p5)) ∨ (False → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687199880026173844924595846670 : ((((p5 → (((((((True ∧ p1) ∧ p2) ∨ p2) ∧ p1) → False) ∧ (p2 → p1)) ∧ (p4 ∧ p2))) → (((p1 → p2) → (p1 → p1)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788469901332669124868065555670 : (((p5 ∨ (((p5 ∧ p3) ∨ ((p1 → p3) ∧ ((((((False ∧ True) → True) → False) → p1) ∧ (False ∧ False)) ∧ ((p3 ∨ p4) ∧ p2)))) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_204332505695255939499668438147 : (((p4 ∧ (p2 ∧ (False ∧ p3))) ∧ p1) ∨ (p1 → (((False ∧ ((p1 → True) ∧ True)) → ((p2 ∨ ((p1 → p2) → True)) ∧ (True ∨ p3))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165341177178478976551799845981 : (((((p1 ∨ p3) ∨ (False → (p5 → p2))) → ((p2 ∧ p4) ∧ True)) ∧ (True → (p1 ∧ True))) ∨ (((True ∧ p1) → True) ∨ ((p1 → p5) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219988637929888004304802079972 : ((p5 → (p5 ∧ (False → p5))) → (((((p2 ∧ (p4 → (((p3 ∧ True) ∨ ((p5 → p2) → True)) → p5))) → p4) ∧ (p1 ∨ p2)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690292524758338270157855577643 : ((((p1 → (((False ∧ (True → (False → (p3 ∨ p5)))) → (p5 ∧ (p4 ∨ p3))) → False)) ∨ ((False ∨ p1) → ((False ∧ p2) → (p4 → False)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617365127154882350964667440955 : (((((((False → True) ∨ p1) → ((p3 ∧ False) → True)) → ((p4 ∨ (p2 ∨ (p5 ∨ p5))) ∧ (((False ∨ False) → (p3 → True)) ∨ p1))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_173092799586967842986177430846 : ((p1 ∨ ((False ∧ False) ∧ ((p4 → (p4 → True)) → (((p4 ∨ p3) ∨ False) → False)))) ∨ (p1 ∨ (p1 ∨ (((False ∨ False) ∧ (False → p1)) → True)))) := by
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
theorem thm_5_vars_224613554550571012840910865255 : ((p2 → (p5 → p2)) ∧ ((((False ∧ ((True ∨ False) → True)) ∨ (p4 ∨ (p4 → p3))) → (p1 → True)) → ((True → ((True → p2) ∨ True)) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23065873373798335105635741747 : ((((True → (p1 ∧ (p3 ∧ True))) ∨ False) → ((((p1 → (p5 → ((p2 ∧ (p1 → False)) ∨ p5))) → (p5 ∨ (True ∧ p4))) ∨ p3) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103152971970050968731600058851 : ((((p5 ∧ True) ∨ (((((((p2 ∧ p2) ∨ (False ∨ p3)) ∨ p2) ∨ p4) → ((p2 ∧ p1) ∨ (True ∨ p3))) ∨ p2) ∨ False)) ∨ True) ∧ (True ∨ p3)) := by
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
theorem thm_5_vars_646926809706597546428065321229 : ((((p2 → (True → (True → (((p4 ∨ (p5 → (p2 ∨ (p5 → (p5 ∨ p3))))) ∧ ((p5 → (True → True)) ∧ p2)) ∨ (p5 ∧ p5))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259876861773546273306936395093 : ((p1 → p4) → ((p2 ∨ (((((p4 → p4) → p1) → p5) ∨ (True ∨ p2)) ∨ ((p5 ∨ True) → False))) ∨ (p2 → (p4 → (False → (True ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_261486959403543352151652567518 : ((p5 → p2) → (p2 → (True → ((p3 ∨ (((p3 ∨ p4) ∨ ((p3 ∧ p5) ∧ p5)) ∨ ((True ∨ False) → p1))) ∨ ((p5 ∨ (p1 → True)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90954708372039120717449908290 : (((False → True) ∧ (((((p4 → (True ∧ p5)) ∧ p1) → (p2 ∨ True)) → False) ∧ (((False → (False → (p5 ∧ p2))) ∨ False) ∨ (p3 ∨ p5)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (((p4 → (True ∧ p5)) ∧ p1) → (p2 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h8
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : (((p4 → (True ∧ p5)) ∧ p1) → (p2 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h16
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h22 : (((p4 → (True ∧ p5)) ∧ p1) → (p2 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h26 := h4 h22
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213908226391096601481277583045 : (((p5 ∨ (p4 ∧ p3)) ∨ p3) ∨ ((p3 ∨ (p4 → (p3 ∨ ((True ∨ p5) ∧ (((True → (p4 → (p3 ∧ p5))) ∨ (p3 ∨ p4)) → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213297687222570722272474555484 : ((((p5 → p3) → p1) ∧ p1) ∨ (((((False ∧ False) ∨ p1) ∧ p5) ∨ (((p3 → p4) ∧ False) → p3)) ∨ (((True → p4) ∨ p4) ∧ (p1 → True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256198225339355232992621752803 : ((False ∨ True) → (p3 ∨ (((((p5 ∨ p1) ∧ p4) ∧ (True ∨ ((((p4 ∧ p2) → True) ∨ (p4 ∨ p2)) ∨ p5))) ∧ p5) ∨ (True ∧ (False → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184681050684801949789879068760 : (((p4 ∨ ((p1 → p3) ∧ (p5 ∨ False))) ∨ ((p2 ∨ False) ∨ p5)) ∨ ((p1 ∨ p4) → (True ∨ ((True → (((p1 ∧ p4) ∨ False) → p3)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54192743131572058429517993934 : ((((((p5 ∧ (p5 ∧ p5)) ∨ p3) ∨ p2) ∨ p1) ∧ ((((((p1 ∧ ((p2 ∨ False) → False)) ∨ True) ∨ False) ∧ False) → p3) ∧ (p5 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199925541641229149392563426340 : ((((p5 ∨ False) ∨ (p2 → p3)) ∨ (p4 → p5)) → ((p3 ∨ (p1 ∧ (p2 ∧ p1))) ∨ ((p3 ∧ (p1 ∧ ((p5 ∧ p4) ∧ (False ∧ p5)))) → p4))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h11.left
        let h15 := h11.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h24.left
      let h28 := h24.right
      -- False on the left can always be used.
      apply False.elim h27
  case inr h29 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h30
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h36.left
    let h40 := h36.right
    -- False on the left can always be used.
    apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642163009582622216694753345647 : ((((True ∧ (((p1 ∨ True) ∨ p1) → (((p2 ∨ p5) ∧ p4) ∧ (p1 → (((p1 ∧ (p5 ∨ ((p4 ∧ p4) ∧ p5))) → p3) ∨ p3))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65627384552428077888158825413 : ((p4 ∨ (((False ∨ (True ∧ ((((p5 ∧ ((False → p2) → p5)) ∨ p1) ∨ (p1 ∧ p5)) ∨ ((True ∨ (p5 → True)) ∨ True)))) ∨ p3) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793276804293142027164174781087 : (((True → (p2 ∧ ((True ∨ p2) ∧ (((((p4 → ((p4 ∧ p4) → p4)) ∨ p5) → (p2 ∨ ((p4 ∨ p2) ∧ (p3 ∨ p2)))) ∨ p5) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349944988583140864846294673304 : (p4 → ((((True ∨ ((p4 ∨ (False → ((p2 ∧ p4) ∨ (p2 → p2)))) → ((((p4 ∧ False) ∨ False) ∨ (p1 → p1)) ∧ p1))) → p1) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147476408916666651128038462240 : (((p2 ∧ (((p4 ∧ ((False ∧ False) → (((p3 ∨ True) → p4) ∨ (False ∧ p2)))) ∧ True) → (p5 → False))) ∨ p2) ∨ (((p3 ∨ False) ∧ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351519953884272745284825622684 : (p4 → (((((((p2 ∧ p5) → (True ∨ p5)) ∨ p4) ∨ ((p5 ∨ True) ∨ p2)) → (p3 ∨ p2)) ∨ p4) ∨ (p2 ∨ (False ∧ (False ∧ (p1 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191835089264102548994619831206 : ((p3 ∨ ((p5 ∧ ((p2 → p5) → p5)) ∧ (p1 ∨ p5))) ∨ (p1 ∨ (p2 ∨ (True ∨ ((False ∨ ((((p2 → p5) → p1) → p2) → p5)) ∨ p5))))) := by
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
theorem thm_5_vars_327068780186700800523499336725 : (True → (((p3 ∧ ((p3 ∧ True) ∧ p1)) ∨ (((((p2 → (p4 ∨ p5)) ∨ (False ∨ p3)) ∧ True) ∨ p1) → ((False ∨ p3) ∨ (p5 ∨ True)))) ∨ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183776159973690242733507410157 : (((((p5 → ((True ∧ False) ∨ p4)) ∧ (p3 ∨ True)) ∧ p3) ∧ p5) ∨ ((((p3 ∨ True) ∨ (False → ((p4 ∨ p1) ∧ p2))) ∨ (p5 ∧ False)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638927817570421511582249907450 : ((((((p2 → False) → (p5 ∧ False)) ∧ (((p1 ∧ p4) → ((((False ∧ (p1 ∨ p5)) ∨ ((p5 → p2) → p3)) ∨ p1) ∧ p4)) → p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42631557473418161822803270204 : (((p3 ∨ ((False ∨ p5) → ((True → False) ∨ (((True → p3) ∨ (((False ∧ False) ∧ p3) ∨ True)) ∧ ((p5 → p5) ∨ (p5 ∨ True)))))) ∨ p2) ∨ p1) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348849730502407651376366073616 : (p3 → (p2 ∨ (((p3 → (p1 ∨ (p4 ∧ ((p4 → (True → ((p5 ∨ p3) ∨ p3))) → p3)))) → ((True → False) ∨ ((False ∧ p4) ∧ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179789417553211321632879215962 : ((((p4 → (p2 ∧ p2)) ∨ (p2 ∨ (p2 ∨ ((p1 → False) → p1)))) ∧ True) → ((p4 → p5) → (True ∧ (((False → p5) → (p5 ∨ True)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168563777487782587473732834133 : ((p1 ∧ (p1 → ((p5 → p1) ∧ (((True ∨ (p2 → p3)) → ((p3 → p4) ∧ False)) → False)))) → (p1 → (p3 ∨ (p5 ∨ ((p4 ∨ True) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137750036883261297723533708897 : ((p2 ∨ (((p5 ∧ (((((p3 ∨ p1) → p4) → ((p2 ∨ p2) ∨ p1)) → (p2 ∨ (p3 ∨ False))) ∨ p4)) → p2) ∨ p4)) ∨ (p3 → (True ∧ p3))) := by
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
theorem thm_5_vars_147381139667529210414214611872 : ((((((p1 ∧ (p2 → p4)) ∨ p5) ∧ ((True ∧ p1) ∧ p2)) ∨ ((((p5 ∧ p4) ∧ p4) ∧ p2) ∨ p1)) ∨ False) ∨ (((p3 ∧ p5) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49125844095810052743593592023 : ((((p2 → ((p4 ∨ (p4 ∨ (p2 ∧ p4))) ∧ ((p4 ∨ p2) ∨ True))) ∧ ((p2 ∧ ((p4 → p4) ∧ p4)) ∧ True)) ∨ (False → (p3 ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147585090125781055956769661477 : ((((p3 → ((p2 ∧ True) ∨ ((p5 ∨ p5) → (p2 ∨ (((p5 → False) → (p1 → p2)) ∧ False))))) ∧ p1) → p3) ∨ ((p1 ∨ (True ∨ p2)) ∨ p5)) := by
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
theorem thm_5_vars_58643361916784454118557113985 : (((p1 → p1) ∧ (((p5 ∧ ((((False ∨ (p5 ∨ (True → p5))) → True) ∨ p2) → (p2 ∧ False))) ∨ (False → p2)) ∨ (False → (p5 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780185011328949252991858655944 : (((p2 ∨ (((((True ∧ p5) → p2) ∧ (False → (((p1 ∧ (((p1 → p1) ∨ p3) ∨ p5)) ∨ p4) ∧ False))) ∧ p5) ∨ ((p4 ∨ False) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42911080463677119172086325242 : (((p3 → (p5 ∧ (((((p4 → (p4 ∨ False)) → p5) ∨ p2) → (p3 ∨ (p4 ∧ False))) → (p1 ∨ (p5 → (p3 ∧ (p3 → p1))))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754981647645409218117596619169 : (((False ∧ (p5 ∨ (((False ∧ p1) ∧ ((p3 ∨ p3) ∨ p3)) ∨ ((p1 → p4) → ((True → p2) ∨ ((p4 ∧ p5) → ((p1 → p1) ∧ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758588110203463016748199612523 : (((p2 ∧ ((((False ∨ ((p3 ∨ ((p3 ∧ p2) → p5)) ∨ ((True ∨ (p3 → p1)) ∧ (p4 → p3)))) → ((p5 ∧ p1) ∧ p2)) → p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42919302518703906968289245006 : (((p4 → (((True ∧ ((((p5 ∨ (p5 → (p2 ∧ False))) ∨ (True → p4)) ∧ p2) ∨ ((p5 ∧ (p2 → False)) ∨ p2))) ∨ p3) ∧ p2)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19879121528546221503218751521 : (((p4 ∧ ((p4 → p1) ∧ ((p1 → p2) ∨ ((True → p4) ∨ (p3 ∧ (p5 ∧ p5)))))) → ((p3 → (((True ∧ p1) ∨ p4) → False)) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h18
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263382236194840581617105249887 : (True ∧ ((((((p5 ∧ False) ∨ ((False → (p1 ∨ True)) ∨ True)) → ((p3 → p4) ∧ p1)) ∨ ((False ∨ p5) ∨ False)) → p1) ∨ (False ∨ (p3 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138318870542241911769434952903 : ((p3 → (True ∧ (((p5 ∨ (False ∨ ((((p2 → (p5 ∨ True)) → (True ∨ False)) → p2) ∨ p5))) ∨ True) ∧ (True ∨ False)))) ∨ ((p5 ∨ p1) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_183609700980873722871081501085 : ((False → (p2 ∧ ((p5 ∧ ((p4 → (p4 ∧ p5)) → True)) ∧ False))) ∧ (p2 → (p3 ∨ ((p5 → ((p1 ∧ ((p2 → p2) ∧ True)) ∨ p3)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46978034434465712275541657606 : ((((((((p4 ∧ (p2 ∨ ((p1 → False) → (False → p2)))) ∧ (p5 ∧ p2)) → (p2 ∧ False)) ∧ p3) ∨ (True ∧ p3)) → p5) ∨ (p3 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191320225883910270633870788698 : (((False ∧ p2) ∨ ((False → (p1 → p2)) → (p5 ∧ p1))) ∨ (p4 → (False → ((p3 → ((False ∨ (p1 → True)) ∧ (p1 ∧ p1))) → (p5 ∧ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258946895140619740336853796463 : ((True → p3) → (((((p2 ∨ p5) ∨ ((True → False) ∧ (p4 ∧ p5))) ∨ ((p2 → False) ∨ p3)) ∧ (((p2 ∨ p5) ∧ p5) ∧ (p3 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174625274929316892900585403241 : ((((p2 ∧ False) ∨ (p5 → p3)) → (((p2 → p2) → ((p3 ∧ True) → False)) → p4)) → (((True → p4) ∧ p5) → (p4 ∨ ((True ∨ p1) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260456130557436964051112656434 : ((p3 → True) → (p4 → (p3 ∨ ((True → (p2 → (p3 ∧ (p4 → p5)))) → (p4 → ((p2 → ((False ∧ (False ∨ p5)) ∨ (p4 → p3))) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336267125276513358568151869855 : (p1 → (((((((True ∧ (p3 ∧ p2)) ∨ p1) ∧ False) → p1) ∧ (p4 ∨ (False ∧ p4))) → (p3 ∧ (((p1 ∨ False) → (p1 ∨ p3)) ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77466763930925734612939148101 : ((((p1 ∨ p4) → ((p1 ∧ (p1 ∨ (p1 → p4))) → (((True → (p2 → False)) ∨ p4) ∨ ((p4 → ((True ∨ True) → True)) ∨ True)))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ p4) → ((p1 ∧ (p1 ∨ (p1 → p4))) → (((True → (p2 → False)) ∨ p4) ∨ ((p4 → ((True ∨ True) → True)) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_831829572911018676724016298109 : ((((p3 → (((p2 ∨ (((p5 ∧ (p4 ∨ p3)) → p3) ∨ (p4 ∨ (p4 → False)))) ∧ (((p2 ∨ p1) → (False ∧ p2)) ∧ p3)) ∧ p5)) ∧ p3) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164856972592516311184974128965 : (((p1 ∨ ((((p4 ∧ p1) ∨ p2) ∨ ((p5 ∧ p3) → (p3 → (False → p3)))) ∧ p3)) ∨ True) ∨ ((((p5 → p4) → p2) → False) ∧ (p4 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664621515431462461938656957429 : ((((True → (((p2 ∨ (p5 → p3)) ∨ (p4 ∨ (((False → (True → p1)) → p1) ∨ ((True ∨ False) ∧ False)))) → (p4 ∨ False))) → (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119431713087208056687555038757 : ((p4 → (((((((False ∨ p4) → p3) ∧ (p4 ∧ p3)) → False) ∧ ((p1 → False) → p2)) ∨ (p4 ∨ True)) ∨ ((p3 ∧ p1) → True))) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234603319739112073480851098449 : ((p3 → (p4 ∨ True)) → (((p3 ∨ p1) → (p1 → (((False ∧ p4) ∨ ((p5 → p3) → p3)) ∨ (False ∧ ((True ∨ False) → p3))))) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



