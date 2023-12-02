variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56481652366196650070752709792 : (((True ∧ ((p4 → p2) ∧ p1)) → ((((p2 ∨ True) → (((p1 → ((p5 → p4) ∨ p5)) ∨ p5) ∧ ((False ∧ p3) → p2))) → p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179087997210183823965099692391 : ((False ∧ (((((p4 ∧ (p4 → p1)) → (p4 ∨ True)) → p4) → False) ∧ p2)) ∨ ((((p2 → (p3 ∨ True)) ∨ (True → p2)) ∧ (p1 → True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164707418563180768189926293821 : ((((p4 ∧ ((False ∨ (p2 ∨ p2)) → ((p1 ∧ p3) ∨ (True → (False ∧ False))))) ∨ p5) ∨ p2) ∨ ((((p1 → (False ∧ True)) ∨ False) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51159954350936097055810869189 : ((((p5 → (((p1 ∧ ((p2 ∨ p3) → (p3 ∨ p2))) ∨ (p1 ∧ p4)) → (False ∨ p3))) → p4) ∨ (True ∧ (((False → True) → p4) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300773797694607922402777070844 : (False ∨ (((((p3 ∧ p2) → True) → (((True ∨ (p5 ∧ False)) ∧ (p5 ∨ False)) ∨ False)) ∨ True) ∨ (p4 ∧ ((p3 ∨ ((p4 → True) ∧ p3)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773279704440332122328095895402 : (((False ∨ (((((p2 ∨ (p5 ∨ p1)) → p1) ∧ p4) ∨ ((((((True → (p5 → p5)) ∧ p4) ∨ (p1 ∨ p1)) ∧ p4) ∨ p2) ∧ p2)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40220875818186370760643319724 : ((((True ∧ (((((True → p1) ∨ False) → ((p4 ∨ (((True ∧ p4) ∨ p3) → p5)) → (p1 → p3))) → (False ∧ True)) → p2)) ∧ p1) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1777511994107903809816555320 : (((p4 ∨ ((p4 ∨ ((True → False) ∨ p3)) ∧ (False ∨ ((((p1 → p2) ∨ p3) ∧ True) ∧ False)))) ∧ (p4 → p1)) ∨ ((True → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215123170422122630028561992585 : (((p3 → p2) → (p3 ∨ False)) ∨ (p4 ∨ ((((p4 ∨ p1) ∨ p3) ∨ (p4 → p1)) → ((p2 ∨ False) → (((p4 → p5) ∧ (p1 ∨ False)) → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h11 =>
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204315420851363063097021660032 : (((p1 ∧ (p5 ∨ (p3 → p3))) ∧ p3) ∨ ((True ∧ ((p2 → p1) ∨ ((p1 → (p3 ∨ True)) → (p5 → (True ∧ (p5 ∧ False)))))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56751457095641512332748906947 : ((((p2 → True) ∨ p3) ∧ ((False ∧ (p3 ∨ True)) ∨ (((p5 → (p3 ∨ p2)) ∨ (False → ((p4 → False) ∧ (p3 → True)))) ∧ (False ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309931150389893560294782350895 : (p2 ∨ (((p2 ∧ p1) ∧ (p1 ∨ (((p5 → (True ∧ p2)) ∧ (((p1 → p4) ∨ p3) → p4)) ∧ p3))) ∨ (p4 → (((p5 ∧ False) → p3) ∨ True)))) := by
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
theorem thm_5_vars_37405782153336574511603438061 : (((((p5 → (((((p1 ∨ (p3 → (p5 ∨ p2))) ∨ (p4 ∨ ((True → p1) ∨ p2))) ∧ p5) ∧ False) ∨ p2)) ∧ (p2 ∧ p4)) ∨ p1) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318896739397106515081359256486 : (p4 ∨ ((p5 ∧ (((p5 ∨ p4) ∨ ((p3 ∨ p3) → (p3 ∨ (p5 → (((p5 ∨ (p2 ∧ p2)) ∧ p3) ∧ p2))))) ∧ p2)) ∨ ((True ∨ p2) ∨ p4))) := by
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
theorem thm_5_vars_42396240265898826812742876429 : (((p4 ∧ (True ∧ (((p4 → ((p3 ∨ p2) ∧ (p3 → (p2 ∨ p5)))) ∧ p5) → ((True ∨ False) ∧ (((p2 → p2) ∧ p2) → p1))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40111555181273857653514535970 : (((((p1 ∧ (p1 ∧ ((((p2 ∧ p4) → False) → ((p1 → (((p2 ∧ p2) ∧ p1) → p3)) → False)) ∧ p4))) ∨ (True → p1)) ∧ False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344289851469259205275727062668 : (p2 → (p3 ∨ ((p5 ∨ ((p1 ∨ ((p3 ∧ ((((p3 ∧ p2) → p2) ∧ (p4 → (False → (p4 → p3)))) → p5)) ∧ False)) ∧ (p1 ∧ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206026147849890818523648415566 : ((p2 ∧ ((p3 → (p4 → p1)) → False)) ∨ (p5 → ((p3 ∧ p1) ∨ ((True ∨ (False ∨ True)) ∨ ((False ∨ (((p3 ∧ p1) ∧ p4) ∨ p3)) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157146197421729786252220119111 : (((((((False ∧ True) → (p3 → p4)) ∧ ((True ∨ ((p1 ∧ p1) ∨ p4)) ∨ p5)) → p5) ∨ p4) → p1) ∨ (p4 ∨ (((False → p1) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_144474958758421459418114322828 : ((((True ∨ p1) → (False ∨ ((((False ∧ True) → p4) → (((True ∨ p4) → p5) ∧ p4)) ∨ True))) ∧ (p2 → True)) ∧ ((True ∧ p5) → (p2 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351244812886544681196002628520 : (p4 → (((p1 ∧ (p4 ∧ True)) ∧ (((False ∧ (p3 ∧ p2)) ∧ ((p2 ∨ p5) → (False ∧ (False → (p5 → True))))) ∨ p1)) ∨ ((p1 → p2) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263579532804838690524998302921 : (True ∧ (((p3 → p2) → ((p1 ∨ p1) ∧ (True ∧ ((((p2 ∨ (p1 ∧ p2)) → False) ∨ p1) ∧ (p2 ∧ p3))))) ∨ (True ∨ (p3 ∨ (p3 → True))))) := by
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
theorem thm_5_vars_134237364357747732093998016792 : (((((p1 → (p1 → p2)) → False) ∨ (p3 → (((True → True) ∧ (p3 ∨ p1)) ∧ ((p4 ∨ (p1 → p3)) ∧ p3)))) ∨ p2) ∨ ((p2 ∧ p5) ∧ p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136620400104607202273488244100 : ((((p3 ∨ p1) ∧ p2) → (((p2 ∧ (p2 ∨ True)) ∨ (p4 ∧ (False → False))) ∧ ((p5 ∧ (p4 ∧ p3)) ∨ (False ∨ True)))) ∨ ((p5 ∨ True) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662633472557141377318822152042 : ((((((True → False) ∧ (True → p1)) ∧ ((p4 ∧ (False ∨ ((((((p5 ∨ p5) ∨ True) ∨ p5) ∧ p2) → p4) ∨ p3))) ∨ p1)) → (p3 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233106822876472112466909067119 : ((p4 ∧ (p3 → p5)) → ((((((p4 → (p5 ∨ p4)) ∧ p3) → p4) ∨ (p5 ∨ ((p4 ∧ p3) ∧ True))) → (p2 → p1)) → (p1 → (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759548084353384226260126133486 : (((p2 ∧ (((p3 → (p5 ∨ p2)) ∨ (((p1 ∧ True) → (p5 ∨ (p2 ∨ p1))) ∧ (p3 ∧ p2))) ∧ ((False → (p3 → (p5 ∨ p1))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149393688330635134489720063395 : ((True ∧ ((((True ∧ p3) ∧ ((False ∨ p4) ∧ p5)) ∧ (((p1 ∨ (p5 → (p3 → p1))) ∧ p5) ∨ False)) ∧ p2)) ∨ ((False ∧ (True ∨ True)) → p3)) := by
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
theorem thm_5_vars_308371082267149089887984869526 : (p2 ∨ (((((((p2 → ((True ∨ p5) → ((p5 ∧ p4) ∨ (p1 ∨ p2)))) → p2) ∧ (True ∧ (p2 → (p3 → p4)))) → p4) ∨ True) ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158007960258602899912892386661 : (((((True ∨ p3) ∨ (p3 ∧ p2)) ∧ p2) ∧ (True → ((p2 → ((p5 → (p1 ∧ p1)) ∨ p4)) → p3))) ∨ ((p2 ∨ True) ∧ ((p2 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173227729870112064814769279177 : ((True → ((((p3 → p5) ∨ (((p2 ∨ p3) → p5) → (p4 → p5))) ∧ p3) ∨ p3)) ∨ ((((p4 → p5) ∨ (p1 → p3)) ∧ p5) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66683752039286421114160773095 : ((True → ((((p2 ∨ p2) → p2) → False) → ((p5 ∧ ((p2 ∧ (True ∧ p3)) ∧ (((p3 ∧ (p2 ∨ (p4 ∨ p2))) ∨ False) ∨ p2))) ∨ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ p2) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304086783149624226137792839083 : (p1 ∨ ((p5 ∨ ((True ∨ (p3 ∧ ((((p5 ∧ p1) ∨ p1) → (p3 ∧ p1)) ∨ (p2 ∨ p4)))) ∧ ((p3 ∧ (p5 ∨ p4)) ∧ (p2 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114687115475263105060384135968 : (((True → ((p3 ∨ (((p4 ∧ p4) ∨ (p5 ∨ ((True ∨ False) → False))) ∧ p2)) → p4)) ∨ ((p3 → (p1 ∨ False)) → (False ∧ p3))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146909646631941601792625412111 : (((((False → (((p4 ∧ (p1 ∨ p4)) ∨ p5) → ((False → (p1 ∧ p2)) ∧ (p5 ∧ True)))) → p1) ∧ p2) ∧ p5) ∨ ((True ∨ (False ∨ p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254450894670673060829076307844 : ((p3 ∧ True) → (((p5 ∨ (p5 → ((p4 ∨ (((((True → ((p1 ∨ p3) → (p2 ∧ p5))) ∧ p1) ∨ True) ∧ p2) ∧ p4)) ∧ p4))) ∧ p5) ∨ p3)) := by
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
theorem thm_5_vars_135476118228222471320432527000 : ((((p3 ∨ (p3 → (p2 ∧ ((True ∨ p1) → p4)))) ∧ ((p2 ∨ p4) ∧ (p4 ∧ (p1 ∧ p2)))) → ((False ∨ False) ∨ p1)) ∨ ((p2 → p1) → p4)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h6.left
      let h14 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h19.left
      let h27 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41914350102408368860246548228 : (((((p3 ∨ p3) → p3) → ((((((False ∨ False) ∨ (p1 ∨ p5)) ∧ True) ∨ p3) ∨ (p3 ∧ p5)) → (p5 ∧ ((p4 → p2) ∧ p2)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779155759971066328551021950601 : (((p2 ∨ (((True → ((((p1 ∧ (p4 ∧ (p3 → p4))) → p3) → ((((p2 → (False ∨ p2)) ∨ False) ∨ False) → False)) → False)) → p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186866788951669177306336516105 : (((((True ∨ p4) → True) ∨ p3) → ((p2 → (p3 → p1)) ∧ p1)) → ((p1 → ((p5 ∧ ((True ∨ True) ∨ (p2 → False))) ∨ p2)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662532469619430257287272425789 : ((((((True ∧ p5) → (False ∧ (p1 → p3))) ∨ (((p5 → (((p2 ∨ (False ∧ (p4 ∧ p4))) → p5) → p1)) ∨ False) → p3)) → (p3 → p3)) ∨ p2) ∧ True) := by
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
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115436127819951426258126851810 : ((((p1 ∨ (((False → p2) ∨ p5) → True)) → p3) ∨ ((((p1 ∧ p5) ∨ ((True → True) → p1)) ∧ (p3 → (p3 ∧ p5))) ∨ p4)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257974700370032387347319105663 : ((p4 ∨ p1) → ((((False ∨ (p5 → p5)) ∧ (((False → (((True ∨ p1) → False) ∧ p3)) ∧ ((True → True) ∨ p4)) ∧ p4)) → (p3 ∨ True)) ∨ p4)) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42563648848433425772489927733 : (((p1 ∨ (p4 → ((p4 ∨ (p2 ∨ ((False → (p3 → (True ∨ False))) ∨ (p3 → False)))) → ((False ∨ (p2 ∨ True)) ∨ (True ∨ p5))))) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165004068901290112142385623166 : (((((((p3 ∨ False) ∨ p4) ∨ p2) ∧ p5) ∧ (p5 → (p5 ∨ (p4 ∧ (p2 ∧ p5))))) → False) ∨ ((p3 → ((p4 ∨ p2) ∧ (p3 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158557498159733956567683564576 : ((True ∧ ((((((p1 ∧ p3) ∨ p2) ∨ ((p2 ∨ False) ∧ p5)) ∨ ((p1 → p3) ∨ p3)) ∧ p5) ∨ p3)) ∨ (((p3 → (p2 ∧ p1)) ∧ False) → p4)) := by
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
theorem thm_5_vars_115083424588426670539083042166 : (((p5 ∧ (p4 ∨ ((p4 → (p2 ∨ (p3 → (p5 ∨ p5)))) → False))) ∨ (((p5 → (p5 ∧ p2)) → True) ∨ (p2 ∨ (True ∨ p4)))) ∨ (p5 ∨ p1)) := by
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
theorem thm_5_vars_197786619718305814215486043971 : ((((p1 ∧ p5) ∧ False) ∨ ((p3 ∧ p5) ∨ p4)) ∨ (True ∧ ((((((p2 ∧ p2) → ((p5 ∨ True) → False)) → False) ∨ True) ∨ p1) ∨ (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178349841696749551954722899462 : (((p4 ∧ ((p4 ∧ (p2 ∨ ((p1 → True) ∨ p5))) ∨ True)) ∨ (p4 ∧ p3)) ∨ (True ∨ ((p3 ∨ (p1 → False)) → ((p2 → False) ∧ (p1 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315915501849186966008517630203 : (p3 ∨ (True ∧ ((p3 ∧ p3) → ((((((p3 ∨ p1) ∧ (p3 ∧ p1)) ∨ (p4 ∧ p5)) ∧ (((True ∨ p1) ∨ (p5 → p5)) → True)) ∧ False) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_167770082286586512998862438324 : (((((((p5 ∧ p2) ∧ (False ∧ False)) ∧ p2) ∨ p1) ∧ (p1 ∧ p2)) → ((p5 ∧ False) ∨ p3)) → (p1 ∨ ((p2 → ((p3 ∧ False) ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245301331312579560983355030266 : ((p2 ∧ p2) ∨ ((((p5 ∧ True) ∨ (p5 → ((p5 ∨ False) ∨ (False ∧ (True → (p1 → p3)))))) ∧ p2) ∨ (((p5 ∧ p3) ∨ (p4 ∨ True)) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41148643123722772670636795217 : (((((p2 ∨ (p5 ∧ (p4 ∨ p4))) → (((p5 ∨ True) ∧ (((p3 → (True ∨ p5)) → p3) ∨ True)) ∨ p2)) ∨ ((True ∨ p5) → p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351721023689848352764688271264 : (p4 → ((((True ∨ (True ∨ ((p3 ∧ p4) → ((p2 ∨ p3) ∨ p5)))) → False) ∨ p3) ∨ (((p1 ∨ (p2 → (p5 ∧ p3))) → p3) ∨ (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_473460901533733595495914543251 : (((((False ∨ ((p3 → False) ∨ True)) ∨ (True ∨ (p2 ∧ (p3 ∧ p3)))) → ((p5 ∧ (p4 → True)) → ((p1 ∨ p4) → ((p2 ∧ p4) ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h2.left
    let h21 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57398441975767128638315200329 : (((False ∨ (False ∨ p1)) ∨ (p3 → (((((p2 → (p1 → (False ∨ p4))) ∨ (True ∧ True)) ∧ p4) ∧ (p5 ∨ p3)) ∧ (False → (p1 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593512050600547564559353002842 : ((((((False ∧ p4) → (((((((p4 ∧ (False ∨ p2)) ∧ False) → p3) ∧ p3) → (p2 → p4)) ∧ True) ∨ True)) → ((p1 ∧ p5) ∨ p4)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358001423631671962835320230988 : (p5 → (False ∨ ((((p4 ∨ False) ∧ p3) ∨ False) ∨ (p4 ∨ (True → (p5 ∧ ((p2 ∨ p4) ∨ (True → ((p3 → p3) → (p2 ∨ (False → True))))))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53191587681905414860700196785 : (((((False → True) → (p3 ∧ (p2 ∧ (p5 ∧ p4)))) ∧ (p1 ∧ p5)) ∨ ((p4 ∨ ((p3 → p4) → (True → True))) ∨ (p1 → (p4 ∧ True)))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49672925291607492024121273764 : ((((p2 → (p2 → False)) → ((p4 ∧ ((p2 → (p5 ∨ p4)) ∨ p3)) ∨ (((p5 ∧ p5) → p4) ∨ (p4 → False)))) → ((p4 ∧ p2) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111917933309954201215581471865 : ((((p5 ∧ ((p5 ∧ (p1 → (p1 ∧ (p2 ∧ p5)))) ∧ (p1 ∨ p2))) ∨ (((p5 ∨ (True ∧ p2)) ∨ (p1 → False)) ∨ p4)) ∨ p5) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111856115590053444359444486084 : ((((p2 → (False ∧ ((p2 ∧ (((((p4 ∧ (p2 ∧ p5)) → p3) ∨ p3) → False) ∨ p2)) ∨ p5))) → (p3 ∨ (False ∧ p3))) ∨ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616614963953639398930868468174 : ((((((p5 → (p3 ∨ False)) → ((p5 ∧ p2) ∨ (p5 → False))) ∧ (((p1 → p2) → (True ∧ p1)) → (False ∨ ((p2 → p2) ∧ True)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19107633358869369752142598222 : (((((True ∨ (p1 → (True ∧ False))) ∨ (p3 ∧ True)) ∧ (p3 ∨ ((p4 → p1) ∨ (p3 → True)))) → ((p3 → (p4 ∨ (False → p4))) ∨ p3)) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
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
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h12
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h18
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h21
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49860007674323704025849506770 : (((((True → (p4 → True)) ∧ ((True → (p3 ∧ p3)) → ((p2 → p1) ∧ ((False ∨ False) ∧ p5)))) ∧ p1) ∧ (p5 → (False ∨ (p4 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171503103817230029115972726618 : ((((((((p5 → p5) ∨ p5) ∧ (p3 ∨ p5)) ∨ (p5 ∨ p2)) ∧ p5) ∧ False) ∨ p2) ∨ (True ∨ (p2 ∨ ((p5 ∧ False) ∨ ((p2 ∧ p2) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63217298255118795715724216686 : ((p5 ∧ ((p3 → ((((p3 ∨ False) ∨ (False ∨ True)) ∨ (p2 ∧ True)) ∨ ((False ∨ p4) ∧ p1))) ∧ (p1 ∨ ((p3 ∧ p4) ∨ (p4 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190980511834745499756756632252 : ((((p5 ∧ (False ∨ p1)) ∨ p2) ∨ ((p2 ∧ p4) ∨ p2)) ∨ (True ∨ (((((True ∧ (False → p4)) → p4) ∨ True) ∨ (p5 ∧ (False → p5))) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1848740243058514908453246614 : ((((p5 → ((p2 ∨ p3) ∧ ((p2 ∨ ((False → False) → (True → p5))) → p5))) → p4) ∨ (True ∨ (p5 ∨ p5))) → (p4 → (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164833068657477841172770309756 : (((False ∧ ((p3 ∧ (True ∧ (p2 → p5))) → (p2 ∨ (((p1 ∧ p1) → False) ∨ p4)))) ∨ p2) ∨ ((((p1 ∧ p3) ∧ (p5 ∨ p1)) → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350253616020725210009181979921 : (p4 → ((p1 ∧ (((p2 ∨ ((p2 ∨ (p5 → ((p4 ∧ p1) → ((p5 ∨ False) ∨ True)))) ∧ (True → (p1 → True)))) → (p5 → p3)) ∨ False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52892122238624037188998189575 : (((p3 ∨ (True → ((((False → p3) ∨ (True ∧ (p1 → p2))) ∨ p5) → False))) → (p2 → (((True → (p1 ∨ p5)) → (p1 → p5)) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_137709706325069538719888515478 : ((p1 ∨ ((((p5 ∧ p5) ∧ ((False ∧ p2) ∨ p5)) ∧ p2) ∨ (True → (p1 → ((False ∨ ((p3 ∨ p2) ∨ p4)) ∨ p1))))) ∨ (p5 ∨ (p2 ∧ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58315635984722489094105793633 : (((False ∨ True) ∧ (((((False ∨ ((p1 → p1) → p3)) ∧ ((p3 ∨ p2) ∧ p1)) ∨ ((False ∧ (p3 → (p4 ∧ p4))) ∨ p3)) ∧ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308475756493805026793655645202 : (p2 ∨ (((p2 ∧ (((True → (True ∧ (p2 ∧ (True → p1)))) → (True ∧ p4)) ∧ ((p2 ∧ (p5 ∨ False)) → (p1 ∨ True)))) → (p2 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144206375301041790447343355975 : (((((p2 → (p4 ∨ ((p4 ∨ True) ∨ p2))) → ((p2 ∧ True) ∧ (p2 ∨ p2))) ∧ ((p5 ∨ p1) ∨ False)) → p2) ∧ (p5 → ((p4 → True) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p2 → (p4 ∨ ((p4 ∨ True) ∨ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (p2 → (p4 ∨ ((p4 ∨ True) ∨ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707336486074949295946747956597 : (((((p2 ∧ (p4 ∨ (p2 → False))) ∨ (p5 ∧ p5)) ∨ ((p3 → ((((p2 ∨ (False ∨ False)) → p2) → p4) ∨ (True ∨ (True ∨ p3)))) ∨ p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156593687613344712767804239099 : (((((p5 ∨ (p1 ∧ (((p3 → p3) ∧ (False ∧ (p3 ∨ p4))) → (False ∨ p5)))) ∧ p5) ∧ False) ∧ p4) ∨ ((False → p4) → (True ∨ (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625116859916745794276439172608 : ((((True → (((p1 ∨ ((p3 ∨ p1) ∨ (p2 → (p4 → (False → ((False ∧ (True ∧ p3)) → p5)))))) → p2) ∧ (True ∧ (p1 ∨ p5)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107850766300383605797035246999 : (((False ∨ p4) ∨ (p5 → ((p1 ∧ p3) ∨ (((p5 ∨ p4) → (p1 ∧ (p3 → (p4 ∨ (True → (False ∨ (True ∨ False))))))) ∨ True)))) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690332171508120701500037425881 : ((((p3 → (((((p3 ∧ p4) ∨ p1) → ((False ∨ p5) → (False ∨ p4))) → p4) ∧ False)) ∨ (True ∨ (p5 ∧ ((p4 ∨ p5) → (p1 → p4))))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_180229370501383384976319289545 : (((False ∧ (True → ((True ∧ (p1 ∧ p4)) ∧ (True ∧ (p5 ∧ True))))) → p2) → (p3 → (p3 → ((p1 → p1) ∧ ((True ∧ p3) ∧ (p5 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151971172674363416459403897336 : ((((False ∧ True) → (((p3 → p2) ∨ p3) → (p3 ∧ (p3 ∧ p1)))) ∨ (p1 ∧ (((False → p2) → p3) → p2))) → (p4 → ((p4 → p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104967052427370343064387966719 : ((((p2 → (((p5 → p5) ∧ p1) ∨ (((p3 ∧ p4) → p3) ∧ (p5 ∨ ((p1 ∧ p3) ∧ p3))))) ∨ True) ∧ ((p5 → p4) ∨ True)) ∧ (False → p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317925904295122296514175590174 : (p4 ∨ ((False ∨ ((((((p5 ∨ (False → p4)) ∧ p5) ∧ (((p3 ∧ p1) ∨ p5) ∧ (True → p5))) ∨ ((p5 ∧ p3) → p3)) ∨ p1) ∨ p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586936343222357005852287606083 : (((((p2 ∨ ((((p3 ∧ (True → ((True → (((p1 → p2) ∧ True) → p2)) ∨ p4))) ∧ (True ∧ p2)) ∧ (p5 ∧ True)) → False)) ∧ p2) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204637562913146958096812194437 : (((p1 ∧ ((p4 ∧ p2) ∧ p1)) ∨ p4) ∨ (True ∨ ((p3 → (p4 ∧ (p5 ∨ ((True ∨ (p1 ∨ (p1 ∨ p1))) ∧ p4)))) ∧ ((True ∧ p1) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241321044594391919356298710865 : ((False → True) ∧ (p5 ∨ ((True → ((((False → p4) → False) → p3) ∧ (((p3 → ((p4 ∧ p3) → True)) ∧ (p3 → True)) ∧ False))) → (True → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111996697708391773531252559032 : ((((p5 → (False ∧ (False ∨ p3))) ∧ (p4 ∨ ((p4 → (((True ∧ p4) ∧ p5) ∨ (((p5 ∨ True) → p1) ∨ False))) ∧ p3))) ∨ p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230325855206386256946225798830 : (((p2 ∨ True) ∧ p1) → (((p3 ∧ p1) ∨ (((((p5 ∨ p4) → p1) ∨ p4) → p5) ∨ False)) ∨ ((True → False) → (p1 → (p5 ∧ (p3 ∧ p5)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- False on the left can always be used.
    apply False.elim h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h19 := h14 h18
    -- False on the left can always be used.
    apply False.elim h19
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h21 := h14 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50356523716036693220166598970 : ((((((p5 → False) ∧ p1) → p5) → ((p3 ∨ (p3 ∧ (((True ∨ p5) ∨ p4) → (True ∧ p3)))) → p1)) ∨ (((p2 → p1) → p4) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682699452232383067142257607787 : (((((p3 ∨ ((p2 → (p3 ∧ p1)) → p1)) → ((p5 ∨ p5) ∧ ((False ∨ p2) → (p3 → p5)))) ∧ ((p4 ∨ (p5 → (False → p3))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90660615646859808865907369401 : (((True ∨ p3) ∧ ((((p5 ∨ ((((((False ∨ ((p5 ∨ p4) → p5)) ∨ True) → p2) ∨ True) ∧ True) ∨ p4)) ∨ (p5 ∨ p2)) ∧ True) → False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((p5 ∨ ((((((False ∨ ((p5 ∨ p4) → p5)) ∨ True) → p2) ∨ True) ∧ True) ∨ p4)) ∨ (p5 ∨ p2)) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (((p5 ∨ ((((((False ∨ ((p5 ∨ p4) → p5)) ∨ True) → p2) ∨ True) ∧ True) ∨ p4)) ∨ (p5 ∨ p2)) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666762908117605387780758091858 : (((((((p2 → False) → (p3 ∨ (p3 → p2))) → p1) ∧ (((p5 → (False ∨ p2)) ∧ p2) → (False ∨ (p5 ∨ p3)))) ∧ ((p1 ∨ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42544569756418914945070083604 : (((p1 ∨ ((p3 ∨ ((p2 → ((p3 → p1) ∨ (p5 ∧ False))) ∧ True)) ∧ ((((p4 → p1) ∧ p5) → (p1 ∧ p5)) ∧ (p5 ∧ False)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698053525627011374479088470117 : (((((((p3 ∧ True) ∧ p3) ∧ (p2 ∧ (p5 ∧ (p3 ∨ p2)))) ∨ False) ∨ (((p2 ∧ ((False → True) ∧ (p3 ∧ (p3 ∧ p1)))) → p4) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_158096779428883081959793544357 : ((((p3 → (True ∧ p4)) ∧ True) ∧ (p5 ∧ (((p3 ∧ p1) → ((True ∨ True) ∧ (p5 ∧ p3))) → p5))) ∨ (False → ((p4 → p3) → (p1 → True)))) := by
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
theorem thm_5_vars_39074678213777758957249691392 : ((((p1 ∨ False) ∨ (((p5 ∧ p3) ∧ p4) ∧ (((((p3 → ((p4 → True) ∨ (False ∨ p1))) → False) → p4) → p1) ∧ (False → True)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340840137748666634970033205724 : (p2 → ((((p2 ∧ ((((True ∨ ((p3 ∧ (p1 ∨ p1)) → p5)) → (p4 ∨ p3)) ∨ False) ∨ (p1 → p4))) ∧ p3) ∧ (False → (False ∨ p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950144412948337882904803228131 : (((((p3 ∨ p1) → False) ∧ (((p5 ∧ (False ∨ True)) ∧ ((False ∨ True) → (p4 ∧ (True → (p5 ∧ False))))) ∧ ((p2 ∧ (p1 → True)) ∧ p2))) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h16 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



