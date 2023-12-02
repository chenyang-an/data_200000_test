variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161319355835606492644600972134 : ((True ∧ (((p2 → (p1 → (p5 ∧ True))) ∨ (True ∨ True)) → ((p3 ∧ (p3 ∧ (p3 ∧ True))) ∧ False))) → (((p3 → (p3 ∨ p5)) ∧ True) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 → (p1 → (p5 ∧ True))) ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149102820593363106028680004380 : (((True → (p3 ∨ p4)) → ((True → p1) ∧ ((p3 ∨ (p3 ∧ p4)) ∧ (p5 → ((p3 ∨ (p4 → p2)) → False))))) ∨ (p1 ∨ ((True ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151386080283585649800824285889 : (((((((True → p2) ∨ (((False ∨ p2) ∧ (p3 ∨ p5)) ∨ p5)) ∧ p1) ∧ False) → (p3 ∨ p3)) ∧ (False → p1)) → (p2 → ((p5 ∨ p3) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87199009570524007400739394082 : (((p3 → (p3 ∨ (p4 ∧ ((False ∧ p4) → p5)))) → (((p5 ∧ p3) ∨ p1) ∧ (((p1 ∧ (True ∨ p5)) ∧ (p1 ∧ False)) ∧ (False ∧ p4)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p3 ∨ (p4 ∧ ((False ∧ p4) → p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250142840237991063748647288803 : ((True → p5) ∨ ((p1 ∧ ((((p5 ∨ (p1 ∧ True)) ∧ (p5 ∨ ((False ∨ p3) ∨ (p5 ∧ (p2 ∨ False))))) → p3) → (p2 ∧ (p4 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217957880509302861223443673724 : (((p1 ∧ p3) ∧ (p5 → True)) → ((p4 ∨ (((p3 ∧ (p4 → (p4 → p2))) ∧ (p2 ∨ (p3 ∧ ((p1 ∨ p3) ∧ p2)))) ∨ p2)) ∨ (p5 → p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114450757743539987701583732992 : ((((((p2 ∨ p4) ∧ (p2 ∧ ((p2 → p5) ∧ ((p4 ∨ (p4 → p3)) → p2)))) ∨ False) ∧ True) → ((False ∧ p4) ∧ (p2 ∨ True))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112612799287697021038275131326 : (((((True ∧ (p3 → ((False ∨ (p1 → (False → p1))) ∧ False))) → (p3 → ((p3 ∨ (p1 → p4)) → p1))) ∨ (p2 ∧ True)) → p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148504653322042415281875229171 : (((False ∨ ((p5 ∨ (p2 → (p3 ∧ p5))) → (p5 ∧ (p3 ∧ p3)))) ∨ (False → ((False ∨ (True ∧ p3)) ∧ False))) ∨ ((p4 ∧ (False ∧ p4)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182008643639039953583879604899 : (((((p3 ∨ p2) ∨ ((p4 → p2) ∨ p3)) ∨ (p3 → p3)) ∨ False) ∧ (p3 → ((p5 → (p1 → ((p1 → p3) ∧ False))) ∨ (p4 ∨ (False → p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56381659218145835929680703585 : (((((True ∨ p4) ∨ p5) → p3) → (p1 ∨ ((((True → p1) ∨ False) → p5) → (p3 ∧ ((p4 → False) → (((True → False) → True) ∨ p1)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ p4) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342653170551726076002542124151 : (p2 → ((((p4 ∧ ((p2 ∧ p4) ∧ p1)) ∧ (p2 ∨ p2)) ∨ False) ∨ ((((p4 → p2) ∨ True) ∧ (((p1 ∧ False) ∨ (p1 → p2)) ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747006706663558273503889603999 : ((((p4 ∨ p3) → (((((p4 ∧ p3) ∨ (p3 ∨ p2)) ∨ p2) ∨ ((p4 ∧ ((((p5 ∨ p5) ∨ False) → False) → p3)) ∨ (False → p4))) ∨ p4)) ∨ p4) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218174529467145183824795928814 : (((False ∧ p1) ∨ (p3 ∨ p3)) → ((p1 ∧ p2) ∨ (((p2 → True) → p1) ∨ (((p3 ∨ p5) ∨ ((p1 → p1) ∧ p3)) ∨ (p3 ∧ (p3 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135511735058170470298547946929 : (((p2 → ((p3 ∨ ((False ∧ (p4 ∧ (p3 ∨ False))) ∧ True)) → (p4 ∧ ((p5 ∧ False) ∧ p3)))) → (False ∨ (p4 ∧ p1))) ∨ ((False ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25295638440683065064271476738 : ((((p3 ∨ p3) ∨ True) → ((((True ∨ True) ∧ (p4 ∨ p5)) ∧ (True ∧ (p5 ∨ ((p3 ∧ (True → ((True ∧ p5) ∧ False))) ∧ p5)))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126445347262686185022964684817 : ((p2 ∧ ((p2 ∨ ((p2 → p1) ∨ (((p3 → p1) → (p3 ∨ ((True ∨ (True ∨ False)) ∨ False))) ∨ ((False → p3) ∨ p1)))) ∨ p1)) → (p5 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714739160337721007652369003364 : ((((True ∧ ((p4 ∧ p3) → (False ∨ False))) → (p2 ∧ (p1 ∨ ((p1 → False) ∧ ((False ∨ (p3 → True)) → (p1 ∨ (p2 ∧ (p3 ∨ False)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654547619430768023236688553981 : (((((False ∨ (((((p4 ∨ p3) ∨ p1) → (((p3 → ((False ∧ p2) ∨ p5)) → p5) → (p3 ∨ False))) ∧ p1) ∧ p5)) ∨ False) ∨ (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669422951586212760345167296286 : ((((((p5 ∧ (True → (p1 ∧ (p5 ∨ p4)))) ∨ ((p1 ∨ (p3 ∨ p3)) → (p4 ∨ (p2 ∨ p4)))) ∨ (p5 ∨ p2)) ∨ ((True ∨ p3) ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785080635167149299140609318382 : (((p4 ∨ (((p3 ∨ (((p1 ∨ p2) → p4) ∧ (p2 ∨ (((p1 → ((p3 ∧ p2) → ((p5 ∨ p3) ∧ True))) → p5) ∧ p2)))) ∨ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52264456156131766743060237759 : (((p5 ∨ ((p5 ∧ (p1 ∨ ((p2 ∧ (p2 ∨ p2)) ∨ ((False ∨ p3) ∨ p3)))) ∨ p5)) → (False ∨ (((True → False) → (p5 → p4)) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h20 =>
              -- False on the left can always be used.
              apply False.elim h20
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h22
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158900913188746056635618946250 : ((p1 ∨ ((p5 → ((((((p4 ∧ p4) → False) → p1) → (p4 ∨ False)) ∨ (True ∧ p1)) → p1)) → p1)) ∨ ((p3 ∧ (False → (p5 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116368610325201721537973131393 : ((((p5 ∧ p3) → False) → ((((False ∨ p3) → p3) ∧ (True ∨ (((True → p3) ∨ ((p4 ∨ p3) ∨ p5)) ∧ p5))) ∧ (p3 ∧ p5))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118810685376027114701254216826 : ((True → ((((((p3 → (False ∨ (True ∧ True))) → (((p2 ∨ False) ∨ p3) ∧ p2)) ∧ (False → False)) ∨ True) ∧ (True ∨ p5)) ∨ p2)) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_650867253888076028214342567377 : (((((True ∨ (False ∨ ((p2 ∨ (p3 ∨ p5)) → False))) → ((((True ∧ p5) ∨ True) → ((False ∨ p2) → (p2 ∧ False))) ∧ True)) ∧ (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37541183374403865745834852376 : ((((p4 ∧ (p5 ∧ (p5 ∨ (((p2 → (((p4 ∧ p1) ∧ ((True ∧ (p5 ∧ (p2 → True))) → p4)) → False)) ∨ True) ∨ False)))) ∨ True) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654319107882073960690278814130 : (((((((p4 → (False ∨ ((p1 ∧ p5) ∧ (p1 → p4)))) → (((p5 ∨ p3) ∧ p2) ∨ p4)) → ((p5 → p5) → p4)) ∨ True) ∨ (False ∨ p4)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_51087392719278804270755738841 : ((((((p1 → (((p1 → (True ∧ p1)) ∧ p4) ∨ ((True ∨ p2) ∧ p2))) ∨ p1) ∨ p1) ∧ False) ∨ ((False → p1) ∨ ((False → p2) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44149964737377632261356257533 : (((((p2 ∧ ((((((True ∧ True) ∧ (p3 ∨ True)) ∧ p1) ∧ (p5 → (p4 → p5))) ∧ p4) ∧ p1)) ∨ p1) → ((True ∨ p2) ∨ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198156875352514860945197351476 : (((True ∨ p5) → (p4 → ((p3 ∨ p1) ∨ p1))) ∨ (((False ∨ (p5 ∨ p1)) ∨ (((p2 ∨ (p3 → p1)) ∧ (p1 ∨ (p5 ∨ True))) → True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215053762756431197126573132168 : (((p4 ∨ False) → (p1 ∨ p2)) ∨ ((p4 ∧ False) ∨ (False ∨ ((False ∧ (False ∨ p2)) → ((((True → True) → True) ∧ True) → ((False ∧ p1) → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197785051748346116471310665704 : ((((True ∧ False) ∧ p3) ∨ (False ∨ (p4 ∨ p3))) ∨ (((p3 ∨ p4) ∨ ((p5 → (False → True)) → (p1 → p2))) ∨ ((False ∧ p2) → (p1 → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41510004763347997970980129580 : ((((((p2 ∨ ((p3 → p1) → (False ∨ False))) ∨ p4) ∧ p4) ∧ ((False ∨ ((True → (True ∨ (p2 → (True → True)))) ∨ p5)) ∧ False)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55880111807675865057175693040 : (((False ∨ (p2 ∧ (p1 → p3))) ∧ (p3 ∨ (((True → p1) → p1) → (p5 ∨ ((((p4 ∧ True) ∧ (p5 ∧ (False ∧ p2))) ∧ p1) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37479147490951434729662039300 : (((((p5 ∨ (False ∨ (True ∨ p3))) ∧ (((((True ∨ p2) ∧ ((p5 ∨ p4) → p2)) ∧ ((p4 ∨ p3) ∧ p4)) ∨ p4) ∧ p3)) ∨ True) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762241124135466114304941052606 : (((p3 ∧ ((((p1 → (p3 → (p5 ∨ (p4 ∧ (False ∧ False))))) → (False ∧ (p1 ∧ p3))) → (True → ((p3 → p3) ∨ p5))) → (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759652334907898347387122646604 : (((p2 ∧ ((p3 → ((p2 ∨ (p4 ∧ (p5 ∧ (p2 → (True → (False → p3)))))) ∧ p4)) ∨ (p5 → (p4 ∨ ((p2 ∨ p2) ∧ (p1 → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249569339090897756117967477987 : ((p5 ∨ p2) ∨ ((p3 → False) → ((((p3 ∨ p3) → ((p4 ∧ ((p4 ∧ p3) ∧ False)) ∨ ((((p3 ∧ p3) ∨ False) → p2) → True))) ∨ p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309783719690632658753871758427 : (p2 ∨ ((((p1 ∨ (p4 ∨ (p5 ∨ False))) ∨ (p2 → ((p2 ∨ p5) ∨ (False ∧ ((p1 ∧ False) ∧ p2))))) ∨ p2) ∨ ((False ∨ True) → (p4 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305774168637335505978710179854 : (p1 ∨ ((((p3 → p3) → p3) → ((p1 ∨ p2) ∧ True)) ∨ (p4 ∨ (True ∨ (True ∧ (p3 ∨ ((p4 ∨ p1) ∨ (((p3 ∨ p1) → False) ∧ p2)))))))) := by
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
theorem thm_5_vars_137054206452629059082674589109 : (((p1 → p4) → (((((False ∧ p4) ∧ (True ∧ (p5 ∨ (p3 ∨ p2)))) ∨ (p2 ∨ p2)) ∨ ((p3 → p3) → p5)) ∧ p3)) ∨ (False → (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336337745826894181701737608789 : (p1 → (((p1 ∨ (p2 ∨ p3)) → (((((p1 ∨ False) ∨ (p4 ∧ True)) ∧ (p5 ∨ p1)) → (((p3 ∨ p3) ∨ p1) ∧ p2)) ∨ (p1 ∨ p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184848970008872665770808973019 : (((p2 → (p3 ∨ (True → p2))) → (p2 ∧ (p1 ∧ (p1 → p1)))) ∨ (((p4 ∧ p5) ∧ (p3 ∨ (True → False))) ∨ ((p2 → p3) → (p3 ∨ True)))) := by
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
theorem thm_5_vars_263392404382161603980865125748 : (True ∧ (((((p2 → (p2 → (((p5 ∨ True) → ((p1 ∨ p1) → p2)) → False))) ∧ False) ∧ p2) ∨ (p4 → (p2 ∨ p3))) ∨ (False → (True → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41386479747422097086185813699 : (((((((False ∧ (p4 ∧ ((p2 ∧ p3) → False))) ∧ p5) ∨ False) ∧ (p4 → p3)) ∧ ((p3 ∧ ((False → p2) → (p1 ∨ p3))) ∨ True)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209059604665426554274232503403 : ((p1 ∨ ((p2 → True) ∨ (p4 ∧ p1))) → ((((((p2 → False) ∨ p5) ∨ p5) → p1) ∧ (p5 → p4)) ∨ ((p2 → ((p3 ∧ p4) → p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759090533835031101221043318373 : (((p2 ∧ (((False ∨ ((p5 ∧ (p4 ∨ ((p5 ∧ (p4 → (p2 ∧ (p1 ∧ p5)))) → (False → (p3 ∨ True))))) ∨ False)) ∨ p2) ∧ (p2 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41184648796267786481189835191 : ((((((((p3 ∧ ((p1 ∧ (p1 ∧ p1)) ∧ p2)) → p4) ∧ p3) ∨ (p4 → p3)) → (p1 ∨ (p4 → p2))) → ((p5 ∧ p5) → p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173309200502618246673855537371 : ((p1 → (False ∨ (((p2 → False) ∨ True) ∧ ((((p1 ∨ p5) → p2) → p4) → False)))) ∨ ((False ∧ ((p5 → (False → True)) ∨ p2)) → (p3 ∨ p4))) := by
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
theorem thm_5_vars_193942331640125963688084981019 : ((p2 ∨ (((p5 → False) ∧ ((p4 → p1) ∨ p3)) → True)) → ((p2 ∧ (p1 ∨ p4)) ∨ (True ∨ ((p5 ∨ ((p5 ∧ (p4 → p2)) ∨ p3)) ∧ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336114748869547995813162328571 : (p1 → (((((p1 ∧ False) → ((p1 → p3) ∧ (p1 → ((p3 ∨ (p2 → ((True ∨ p4) ∨ (p5 ∨ (p1 → p3))))) → p4)))) → p5) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165625780089415977111914446180 : (((((True ∧ p1) ∧ (True → p2)) → True) ∧ (p5 ∨ (((p3 → p5) ∧ (False ∧ p3)) ∨ p1))) ∨ ((True ∧ (p5 → ((True ∨ p3) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65695254541089392793744522380 : ((p4 ∨ ((p5 ∨ ((True ∧ (p5 ∨ (((((p2 ∨ p3) ∧ (True → p5)) ∨ ((p2 ∧ p4) ∧ (p3 ∧ p1))) → p3) ∨ p3))) ∨ p1)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700593103519214091234456482844 : ((((False → (False → (True → (p4 ∧ (((p2 ∧ False) ∧ p2) ∧ p4))))) → (p2 ∨ (((p4 ∨ p4) ∨ ((p5 ∨ p3) → p3)) ∨ (False ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64012177791364551351971669888 : ((False ∨ (((((p3 ∨ (p5 ∨ ((p5 → p4) ∧ ((p2 ∨ p5) ∨ p3)))) ∨ ((p4 → (False → True)) ∨ p5)) ∨ p1) → p1) ∨ (p2 ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_52824218559587892659997940652 : ((((p5 ∨ (p3 ∨ (True ∧ p4))) → ((p5 → ((p2 → False) → True)) ∨ False)) → (p1 ∨ (((p5 → ((p2 ∨ p1) → False)) → False) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_196757796468942924599080785474 : ((((p1 ∧ (p2 ∨ p3)) ∨ (p3 ∨ False)) ∧ p1) ∨ (p2 → (p4 → (p4 ∨ (p4 → ((p1 → ((p5 ∧ (p1 ∧ (False ∨ p4))) ∧ True)) → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113616758042129922489889149929 : (((True → (((False ∨ (p3 ∨ (False ∨ ((p4 ∧ ((p3 → True) ∨ False)) → (p4 → (p4 ∧ p4)))))) ∧ False) ∧ p2)) ∨ (p4 → False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68998259661397192694812493900 : ((p5 → ((((True → (((p4 → False) ∨ (p2 ∨ p2)) ∨ p3)) ∨ ((p2 → p4) ∨ (True ∨ True))) ∧ (False ∨ (p5 ∧ (p4 → p1)))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974259027969560315593244051222 : ((((False → False) → ((((((p2 ∧ p4) → p3) → False) ∧ p2) ∧ p5) ∧ (((p1 ∨ ((p2 ∧ p4) → ((p4 ∨ p1) ∨ p2))) ∧ False) ∧ p2))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39194427887115165894586335041 : ((((p5 → p4) → (p2 ∧ (((p2 → ((True ∨ (((p2 ∧ p2) ∨ (p1 → p2)) ∧ (True ∨ False))) ∧ p1)) ∧ False) ∧ (p2 ∧ False)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624052410499917267436326454731 : ((((p2 ∨ ((((True → p1) ∧ p3) ∧ ((p1 ∧ p5) ∨ (p5 → p4))) ∨ (((False → (True ∧ p3)) ∨ (p1 ∧ (True ∧ p4))) → p1))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_52799529286329701316063657216 : ((((p5 ∨ ((False → p4) ∧ ((p5 ∧ False) ∧ p3))) ∨ (p2 → (p1 → p3))) → (True → (((p3 → ((p5 ∨ p3) ∧ p2)) ∧ True) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159221630040266624219825674674 : ((p2 → (p3 ∨ ((True → ((False ∨ p4) ∨ (p5 → p3))) ∨ ((False → ((False → p3) → p2)) ∧ p5)))) ∨ (((p2 → (False → p5)) ∧ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338400522689585552681325242021 : (p1 → (((p1 → (False ∨ False)) ∨ p1) → (p3 → ((p2 ∨ (((True ∧ False) ∨ p5) ∨ p5)) ∨ (((p3 → (p2 ∨ (False → p4))) → p3) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40353146412736728546626977216 : ((((((p2 ∨ ((False ∨ p4) ∨ ((p4 → (p3 → p5)) → ((((p3 ∨ p1) ∨ p2) → (p5 → p2)) ∨ p2)))) ∨ p5) → p1) ∨ True) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140328146808310605894353956677 : (((((False ∧ ((p5 ∨ p4) ∨ (False ∨ ((False → p2) → (p3 ∨ p5))))) → (False → p1)) ∧ p4) ∨ ((False ∨ p2) ∨ p4)) → (p2 → (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34145156816034913056018416946 : ((True → ((p5 ∨ (p4 ∨ (((p3 ∨ ((p5 ∨ (p2 ∨ p5)) ∧ (p3 ∨ False))) ∧ True) ∨ (True → (((p2 → True) ∧ p2) ∨ True))))) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259601874462087236377032056111 : ((p1 → True) → (True → (p1 ∨ (((True ∧ (p3 ∨ (p3 → ((p4 → ((((p3 ∧ p2) → p5) ∨ p4) ∧ p5)) → False)))) ∨ p3) ∨ (True ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40939141186358491742387401736 : (((((p4 ∨ (False ∧ ((((((True ∨ (False → (p5 ∨ p3))) ∨ True) ∧ (p5 ∧ p3)) → p1) → False) ∨ p2))) ∨ p3) ∨ (p2 ∧ True)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614674316266493798499635465077 : ((((((True → (((((p5 ∨ False) ∨ False) → p3) ∧ (p5 ∨ (p5 ∨ (p2 ∨ p2)))) ∨ p3)) ∧ p4) ∨ (p2 → ((p5 ∧ p2) → p4))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_323810076233999826838224281710 : (p5 ∨ ((p5 ∨ ((((True ∧ (True → p5)) → p1) ∧ (p4 ∧ (p2 ∧ (p4 ∨ (p5 ∨ p1))))) ∨ True)) ∨ ((p5 → ((p2 → p4) ∨ p4)) ∧ p5))) := by
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
theorem thm_5_vars_151014264066007694239295693963 : (((p3 → (((((p1 → ((False ∧ p1) ∨ (((p1 ∨ False) ∨ p3) ∧ p3))) ∨ False) ∨ p3) → p1) → p5)) ∨ p1) → ((p3 ∨ (p5 ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158427347931759336264821749761 : (((p5 ∧ p5) ∨ ((True ∧ True) → (p2 ∨ (p4 ∧ ((p4 ∨ p3) ∧ ((True → (p5 → True)) ∨ p1)))))) ∨ (((False ∨ (p3 → p3)) → p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p3 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147295290519618615439710715597 : ((((((p4 ∨ p1) → ((((False ∧ p2) ∧ p1) → (((False ∨ p2) ∧ p1) ∧ p2)) ∨ p3)) ∨ p4) → False) ∨ True) ∨ ((p4 ∨ (False ∧ p5)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324304674007082920503126370113 : (p5 ∨ ((p1 ∧ (p3 ∨ (((p4 ∧ p1) ∧ False) ∨ p3))) → (((p2 ∧ (((p5 ∧ p1) ∨ (True ∨ p2)) ∨ False)) ∨ ((p3 ∨ False) ∧ p1)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
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
      apply False.elim h8
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58517450271910419846535181871 : (((p5 ∨ True) ∧ (p5 → (((p5 ∨ p3) → ((((p3 ∨ p5) → False) ∨ ((p3 ∧ p3) → ((p2 → p5) → p5))) ∨ (p4 ∨ p1))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340750857068332431052148437362 : (p2 → ((((p5 ∨ (p1 ∧ (False ∧ p1))) ∨ (((False → ((p2 ∧ True) ∨ (p4 ∨ p4))) → ((p2 → (p4 → p1)) ∧ True)) ∧ p3)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52895158950621095094904891946 : (((p4 ∨ (False → (((p2 ∨ (p2 ∨ p2)) → (p3 → (p2 → p3))) ∧ True))) → ((p3 → (p5 ∨ (((True ∨ p2) ∧ p5) ∧ p5))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134210505413021556306588161801 : (((((p1 ∨ (False ∨ False)) ∨ (p3 ∧ (p3 ∧ False))) ∨ ((True ∧ (((False ∨ (False → True)) ∨ False) ∨ False)) → p2)) ∨ True) ∨ (p2 ∨ (p1 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38977427866166440238166506431 : ((((p2 ∧ p4) ∧ (((p2 ∨ (((False → ((((True ∧ (False → p4)) → p2) ∨ p2) → True)) → p4) ∧ p2)) → False) ∧ (p2 ∨ p3))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671735189830681096357353053112 : (((((((p1 → (p2 ∨ p4)) ∨ (False ∨ ((True → (p3 → (p5 ∨ p2))) → True))) ∨ (p4 → (p4 ∨ p2))) ∧ p1) → (p3 ∨ (p5 ∨ True))) ∨ False) ∧ True) := by
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
  cases h2
  case inl h4 =>
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
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48214899139597256177860118202 : ((((True → p3) → ((p2 ∨ (((((True ∨ (p1 ∨ p4)) ∨ ((p4 ∧ p5) ∧ False)) ∧ p1) → (p5 ∧ p2)) → False)) → True)) → (p1 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61670773960327167699690652704 : ((p1 ∧ (p4 ∧ (p3 → (((((p3 → p2) → p3) ∨ (((True → False) ∧ p4) ∨ True)) → p4) ∧ (p2 ∧ (((p1 → p3) → p5) ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201075876772829386694931344883 : ((p5 ∨ ((True ∧ p2) ∨ (p3 ∧ (p5 ∨ p3)))) → (((p2 ∨ (p4 ∨ (p1 ∨ (p3 ∧ (p5 ∨ (True ∨ (p2 ∧ p5))))))) ∨ p5) ∨ (p1 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
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
        -- One of the premise coincides with the conclusion.
        exact h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157198658955551662664077049907 : ((((((((p4 ∨ (p3 ∨ p2)) ∧ (False ∨ (p4 ∨ True))) ∨ p1) ∧ True) ∨ p3) ∨ (p4 ∧ p2)) → p3) ∨ ((p4 ∨ ((p4 ∧ True) → True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43833859686514744316748746825 : ((((((((p2 → ((p5 → p2) → True)) ∧ ((p2 ∧ p2) → p2)) → (False ∨ (p1 → p1))) → (False → p5)) ∨ p2) ∧ (True → p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342751935007085384850372553635 : (p2 → (((p2 → (False → ((p4 ∨ p5) → p3))) → p5) ∨ ((((p5 ∨ p3) ∨ p4) ∨ (p3 ∧ p4)) → (True ∨ ((p1 ∧ p2) → (p2 → True)))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3286502718558733283179214554 : ((p5 → False) ∨ ((p3 ∨ ((p2 ∨ ((True → ((True ∨ True) ∧ (p1 → p2))) ∨ p3)) ∧ (((p1 ∨ (p3 ∨ p4)) ∧ p4) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192588852074497901359390775568 : (((p2 → ((((False → p2) ∨ p4) ∨ p1) → True)) ∨ p4) → ((((p4 → ((p4 ∨ p4) → p5)) ∧ p2) ∧ (p1 → (False ∧ False))) ∨ (p5 → True))) := by
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
theorem thm_5_vars_40560542844793613309630402236 : ((((p2 → ((p4 ∨ p1) ∨ (((False ∧ (p2 ∨ p4)) ∨ p5) ∧ (((p2 ∨ (p3 ∨ ((p4 → p1) ∧ True))) ∨ False) ∨ p2)))) ∨ p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313210386538525746473877208423 : (p3 ∨ (((p3 ∨ (p1 → False)) ∧ ((((((p1 ∧ (True ∨ p1)) ∧ True) ∨ ((p3 → (p1 ∧ (True ∨ False))) ∨ p4)) ∨ p5) → False) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46708066018203237039327013225 : (((p4 ∨ ((p3 ∨ p1) ∨ (((False ∧ p2) → p2) → ((p4 ∨ ((p4 → p2) → (((p3 ∨ True) → p1) ∧ p3))) ∨ p2)))) ∧ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305578814004191103320551260202 : (p1 ∨ (((p2 → (p5 → ((((False ∧ p2) ∧ p2) ∨ p4) ∨ p1))) ∧ p4) ∨ (True ∨ (((p2 ∧ False) → (p2 ∨ (p4 → (p2 ∨ p1)))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148007416902384740248840767986 : ((((p3 ∨ ((((((False → p1) → (True → p4)) ∧ p3) → p4) → False) ∨ False)) ∨ (p3 → p3)) ∨ (p1 ∧ p5)) ∨ (p4 ∧ ((p5 ∨ True) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129297090956928297552090076933 : (((((p4 → p5) → p4) ∨ ((p1 ∧ (False ∨ (p1 ∧ p1))) ∨ (False → ((p1 ∨ (p3 ∧ (True ∧ p1))) ∧ True)))) ∨ p1) ∧ ((p5 ∨ p4) ∨ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4591569323533747116014928405 : (p4 → ((((p5 ∧ p5) ∧ p5) → (((p1 ∧ p5) ∨ False) ∧ ((False ∨ p3) ∧ p4))) ∨ ((p2 ∧ p5) ∨ ((p1 ∧ True) → (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709124983752302085807797073192 : ((((((p4 ∨ True) ∨ p2) → (p4 → (True ∧ False))) → (p3 → (False ∧ ((p2 ∨ ((p3 ∨ p4) → ((False ∨ p5) ∨ p3))) ∨ (p5 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251983301393467661737099811380 : ((p4 → False) ∨ ((((p4 → p5) ∨ p2) ∧ (((p3 ∧ (p5 ∨ p4)) ∨ False) → (p1 ∧ p4))) ∨ (((p4 → p5) ∧ p3) ∨ ((True ∨ p5) ∨ p4)))) := by
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



