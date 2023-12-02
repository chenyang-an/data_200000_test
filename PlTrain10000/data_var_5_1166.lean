variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299245761837707960571247324422 : (False ∨ ((((p1 ∧ (p3 → (p3 ∨ ((p1 ∨ True) ∧ ((True ∨ (p5 ∧ ((p3 → True) ∧ True))) ∧ True))))) ∨ p1) → (p3 ∨ (p3 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_991311846523956043591077641782 : (((p4 ∧ (((((((((p3 ∧ (True ∧ p3)) ∨ p1) → p4) ∨ p4) ∧ p4) → ((p3 ∨ (p2 ∨ p1)) ∧ (False → p5))) ∨ p4) ∨ p3) → p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((((((p3 ∧ (True ∧ p3)) ∨ p1) → p4) ∨ p4) ∧ p4) → ((p3 ∨ (p2 ∨ p1)) ∧ (False → p5))) ∨ p4) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62467729956264733811635618155 : ((p3 ∧ ((p3 ∧ p2) ∨ ((p3 ∨ ((((False ∨ True) → p5) → (p3 ∧ (p5 → ((((p5 → p4) ∧ True) ∨ p5) ∧ p5)))) ∨ False)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157808434411612752933561804197 : ((((((p2 → p3) ∧ ((False ∧ p5) ∨ (p5 → p4))) → True) ∨ False) → ((True ∨ p3) ∧ (False ∧ p1))) ∨ (p1 → (False → (p2 ∨ (p2 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117440957506015021374151406470 : ((p1 ∧ (((p3 ∨ (False ∨ (p1 ∨ (p4 ∧ p1)))) ∧ p5) ∨ (p3 ∨ ((True ∧ p4) ∨ ((((False → p1) ∧ True) ∨ p5) → p2))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66549551863323324990515856934 : ((True → ((p5 → (p1 → (((False → ((True → p3) → False)) → False) → (((((p3 ∨ (p4 → p5)) ∨ p5) ∨ False) ∨ p4) ∧ False)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607253780459948510871338079612 : (((((((p5 ∨ p5) ∨ (p5 ∨ False)) → ((((p4 ∧ p3) → p2) ∧ ((p3 ∧ ((p1 → True) → False)) ∧ (p1 ∧ p5))) ∧ False)) ∧ p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_149874971503393497732291684003 : ((p2 ∨ ((((p2 → (p2 ∨ True)) → (((p5 ∧ (p4 ∨ False)) ∧ True) → False)) ∧ (False → p1)) → (p5 ∧ p2))) ∨ ((p2 → (p2 ∧ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117781759188717368784599250705 : ((p4 ∧ ((((((p5 ∧ (p3 ∨ ((False → False) → p3))) → True) ∧ (p4 ∧ p2)) ∨ p2) → p1) ∧ ((p2 ∧ (p4 ∨ False)) ∧ False))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54698619976657329451301284283 : (((((True → p4) ∨ (p5 ∨ p3)) ∧ (True → p2)) → ((((p5 ∨ (((p5 ∨ (p2 → p1)) ∧ p3) ∨ p1)) → p3) → p5) ∨ (True ∨ p1))) ∨ p3) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48552079799961624739224063440 : (((((p3 ∨ (((p3 ∧ (((p2 ∧ (True ∨ (True ∨ p4))) ∨ p1) → (p5 → p5))) ∧ True) ∧ False)) → p3) → p3) ∧ (p4 ∨ (False ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184122243705766083698190546644 : (((True ∧ ((p5 ∧ (p3 ∧ (p3 ∧ p1))) ∧ (p1 → p5))) ∨ p4) ∨ ((p4 → (False ∨ (False ∨ (((p3 ∧ p2) ∨ (p2 ∨ True)) → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325947013987054734333144980612 : (p5 ∨ (p5 ∨ (((p1 ∧ p2) → p3) → (((p5 → (p2 ∨ (False ∨ ((p4 ∨ p5) → p3)))) ∧ (p1 ∧ (p4 → False))) ∨ (False → (p4 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_234324859181507002879632501801 : ((p1 → (p3 ∧ p2)) → ((p2 ∨ p1) ∨ ((p4 → (True → (p5 → p4))) → (p1 → (p5 ∨ ((p5 ∨ False) ∨ ((True ∨ (p3 ∨ True)) ∨ p2))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204317362969740897317801254935 : (((p2 ∧ ((p2 → p5) ∧ p3)) ∧ p2) ∨ ((p2 ∨ (((p5 → True) → ((p2 ∨ False) ∨ p5)) → (p3 ∨ ((True ∨ p1) ∨ (p4 ∧ p3))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_779445503045878833741515888901 : (((p2 ∨ ((((False ∧ p1) ∧ ((p5 → p3) ∨ (p1 ∧ (True → (True ∧ ((p5 → p1) → (p3 ∧ (p1 ∨ False)))))))) ∨ (p2 → True)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240894753979617273950545412474 : ((True → True) ∧ (p3 ∨ (p4 ∨ (((False ∧ p1) ∨ ((((p5 ∨ False) → p2) → ((True → p1) → False)) ∨ (False → (p1 → False)))) ∨ (p5 ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207790353473264061380900883799 : (((True → (p5 ∧ (p2 ∨ p4))) → p3) → ((((False → False) ∨ p2) → p4) ∨ (((False → False) ∨ p4) ∨ ((p5 ∧ False) → ((p4 ∨ False) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608288120159769261879819707898 : (((((((p1 ∧ ((p5 ∧ (((((False → (p2 → False)) ∧ p3) → True) ∨ (p4 → p4)) → p5)) → p2)) → (p5 → p4)) ∨ True) ∨ False) ∨ p5) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350103188184980028387185636791 : (p4 → (((p4 ∧ (p2 ∨ ((((p5 ∨ p4) ∧ p5) → (p3 ∧ p1)) ∧ (((p4 ∨ (p3 ∨ p1)) ∨ p5) ∨ p4)))) → ((False ∨ True) ∨ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216598529193372652294488944454 : ((((p1 → True) ∧ p4) ∧ p1) → (((p2 ∨ ((True ∨ p2) → ((p5 ∨ (p2 ∨ ((p3 ∧ ((p4 ∧ True) ∧ p2)) ∧ p4))) ∨ True))) ∧ p4) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_548454082480723975162834163853 : (((False ∨ ((False ∧ (p4 ∨ p2)) ∨ ((True ∧ (p3 → (p2 → p3))) → ((((p4 ∨ False) ∧ p4) ∧ p5) → ((p4 → False) ∨ (p2 → p2)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55273189953041245368587450983 : ((((p2 → p2) → ((False ∧ p4) ∨ p4)) ∨ ((((p4 → p4) → False) ∧ False) → ((((True ∧ p4) ∧ p2) ∧ (p5 → (False → p4))) ∨ p3))) ∨ p5) := by
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
theorem thm_5_vars_691705856060895778927425282199 : ((((False ∨ ((p1 → (p1 → (False ∨ (p1 ∧ ((p4 → (p4 ∧ p1)) → p4))))) → p1)) → (True → (p2 ∧ ((p3 ∧ (p2 → p3)) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_536253899188708439488963318 : ((((p4 ∧ ((((True ∨ p5) ∧ ((((True → p5) ∨ p5) ∧ (False → ((p1 ∧ p1) ∧ False))) ∧ p2)) ∨ p2) → p5)) → False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52004728412704308904751388583 : (((p1 ∧ (p3 → (((p3 ∨ (p4 ∨ p1)) ∧ (p5 → ((p3 ∨ True) → p1))) → p4))) ∨ ((True → ((False → (p4 ∨ p4)) ∨ p3)) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679871496083203683891488496192 : (((((((True ∨ (((True → ((False ∨ p4) ∧ True)) ∨ (p3 ∨ (False ∨ p2))) ∧ p2)) ∧ False) ∧ p2) → False) → ((p2 → (p3 ∧ False)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667425893878513083110378582140 : (((((p5 ∨ True) → ((p3 ∧ (((((p3 ∧ False) → True) ∧ True) ∧ True) ∧ (p4 → False))) ∧ ((p5 ∨ p2) → False))) ∧ ((p5 → p3) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115180062979131698106171558918 : (((((((True ∧ p3) ∨ p5) ∧ p5) → p5) ∧ (p2 ∨ p3)) ∧ (p2 ∧ ((p3 ∧ ((p4 ∧ False) ∨ p2)) → (p4 ∨ (p4 ∨ p2))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185593351479210555796457422197 : ((p5 ∨ ((p1 ∨ p2) ∧ (p3 → ((p1 ∧ (p4 ∧ True)) → p5)))) ∨ (((False ∧ (((p5 → p1) → p2) ∧ (p3 ∨ True))) ∨ True) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655561197442505625230259005986 : ((((((True → (((p5 → (p2 → (False ∧ p3))) ∨ p2) ∧ p4)) → ((False → ((p5 ∧ p4) ∧ True)) ∨ p4)) → (p4 → False)) ∨ (True ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187241913803599937504313948234 : ((True ∧ ((p1 ∧ (((False ∨ p2) → False) → (p5 ∧ p5))) → p1)) → ((True → (p5 ∨ (p2 → (False ∨ p4)))) ∨ ((p4 ∧ p4) ∨ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317626656708880412075141062188 : (p4 ∨ ((((p2 ∨ (p3 ∧ ((((((True → p2) → p3) ∨ True) → ((p3 ∧ p4) ∨ p1)) → (p1 ∨ p5)) → p2))) → (True → p1)) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197320091292172671486393937804 : ((((True → p2) ∨ (True ∨ (p4 → p1))) → False) ∨ (True ∨ ((p2 ∨ (p5 ∧ p2)) ∧ (p4 ∧ (((p1 → p4) ∨ ((p5 ∧ p4) → p4)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675108664257759024798340342094 : (((((((True ∨ p1) → ((p5 → (p4 → True)) → (p3 → (False ∨ (False ∧ (p1 ∧ True)))))) ∨ p4) ∨ True) ∧ ((p4 → (p4 ∨ False)) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57586537272221426392021108668 : ((((p5 ∨ p1) ∧ p4) → (False ∧ (p1 ∧ ((((p2 → True) ∧ p5) → (True ∧ ((p5 ∧ p1) ∧ (p2 ∧ p2)))) ∧ ((False ∧ p2) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325875604253885139154563787135 : (p5 ∨ (p4 ∨ ((((((p4 → (p3 ∨ (p5 ∨ p4))) ∨ p1) → p1) ∨ False) → (p4 → p1)) ∧ ((False → p3) ∨ (((p4 ∧ p4) ∨ p3) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 → (p3 ∨ (p5 ∨ p4))) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667205935678183113032009629769 : (((((p1 ∧ True) ∧ ((p1 ∨ p1) ∧ ((((((p3 ∨ (False ∧ False)) ∨ (p1 → True)) → p2) ∨ False) ∨ p5) ∨ p1))) ∧ (False ∨ (p3 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234724232139285625783613757505 : ((p4 → (p4 ∨ p2)) → (p1 ∨ (((True → (p3 ∧ p2)) ∨ ((p2 ∨ True) ∧ (True ∨ (p3 → (True → ((p4 ∧ p5) → p1)))))) ∧ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747888944884120359888770196001 : ((((False → p4) → (((p2 → (True → (p1 ∧ p5))) → False) → ((((False ∨ p2) → (((p4 → False) → (p1 ∧ p2)) ∨ p4)) ∧ True) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163669665740924281721274320351 : (((p5 ∨ p5) ∨ ((p2 ∧ p4) ∨ ((p5 ∨ p1) ∨ ((((p5 → True) ∨ p3) → p1) → p1)))) ∧ (p2 → ((p2 ∧ True) ∧ ((False → p4) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776577686353569091033249363891 : (((p1 ∨ (((p1 → p5) → ((False ∧ ((p2 ∨ ((((p4 ∨ False) → False) ∧ (False → p2)) → p1)) ∧ (p5 ∧ (True ∧ p4)))) ∨ p3)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_347027889218184448730851071238 : (p3 → ((p4 ∨ (False ∧ ((p1 ∧ p4) ∧ ((p2 ∨ ((True → p4) → True)) ∨ (True ∨ p3))))) ∨ ((p4 ∧ p3) ∨ ((p3 → True) ∧ (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263457921646042198038859611369 : (True ∧ ((((True → ((p2 ∧ False) ∧ (True ∧ (p1 ∧ (p3 ∨ p1))))) ∨ (p3 ∨ (p4 ∧ p3))) ∧ ((p3 → p4) ∨ True)) → (p1 → (p3 ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    cases h4
    case inl h6 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147397624186488716837160787087 : ((((((False ∨ True) → p2) ∧ (p5 ∧ p2)) ∧ (p4 ∨ (((p1 ∨ (p1 ∧ p3)) → (True ∧ p4)) → p3))) ∨ p2) ∨ ((True → p2) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774712840010016417551145811028 : (((False ∨ ((((True ∨ p4) ∨ True) ∧ (False ∨ (p1 ∧ False))) ∨ ((p4 ∧ p1) ∨ (((p5 → (False ∨ p4)) ∨ (False ∧ (p5 ∧ p4))) → True)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620122237241687817369456183320 : (((((False ∧ p3) ∨ ((True → p2) → (((p5 ∧ p2) → (((((False ∨ True) ∧ p5) ∧ p1) ∧ p4) → p1)) ∧ (p4 ∧ (p5 → p1))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620326240114501403772960738767 : (((((p1 ∨ p3) ∨ (((p2 ∧ (((p4 ∧ p1) ∧ p1) ∨ p5)) ∨ (((True ∨ p4) → True) ∨ ((False ∨ True) ∧ (True → True)))) → p2)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209395192405732975452159942334 : ((p1 → (p4 ∧ ((p5 ∨ False) → p3))) → (((((p2 ∨ True) ∧ (p4 ∨ (((True → p1) → p2) → (p5 → (p1 ∧ p2))))) ∧ p4) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157920347590680725314530644421 : (((p4 ∨ (p5 → ((p1 ∨ ((p5 ∨ p2) ∧ p1)) ∧ p5))) → ((p1 ∨ (p3 → p5)) → (p3 ∧ p5))) ∨ (p5 → ((p2 → p1) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_150544231216911875292150766835 : ((((p2 → ((True → p3) → (p1 ∧ False))) ∧ (False ∨ (p1 ∨ ((True → (True ∧ (p4 ∧ p5))) → p5)))) ∧ p4) → ((p3 ∧ p3) → (p3 → p3))) := by
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
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181298590889924685937806071073 : ((p5 ∧ ((True → (p3 ∨ True)) → ((p3 ∧ True) ∧ (False ∨ (p2 ∨ p3))))) → ((((p3 ∨ True) → (p2 ∧ ((p4 ∧ False) ∧ False))) → False) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51185255499082955559789963536 : (((((False ∧ p2) ∨ ((p1 ∧ p5) ∧ (((p4 → p2) ∧ p2) → p4))) ∧ (False → (p2 ∨ False))) ∨ (False → (((p4 ∧ p1) ∧ p2) ∧ p1))) ∨ p3) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1540754164006089980599364011 : ((True ∧ (((p5 → (p1 ∨ (p2 → p5))) ∨ ((p4 ∨ p5) ∧ p1)) → (p3 ∨ (((p3 ∨ p2) ∧ (True → p2)) ∧ p5)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81141057028703933920261032810 : ((((p4 ∨ True) → ((p5 → ((((False ∨ p4) ∨ p2) ∧ (p2 ∧ ((p1 ∧ True) → (False → False)))) → True)) ∧ p1)) ∧ (False ∨ (p2 ∧ p2))) → p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226363696104952753509856902003 : (((True → p1) ∨ p4) ∨ ((((p5 → (p1 → ((p4 ∧ p2) ∧ p1))) ∧ False) ∨ ((p2 ∧ p4) ∨ ((True ∧ ((p2 ∨ False) ∧ p1)) → p1))) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213308140088287040446506559394 : (((True ∧ (p2 → False)) ∧ p4) ∨ ((((p2 ∧ (((p4 ∧ p4) → p1) ∨ p1)) ∧ p2) ∨ (((p1 ∨ False) ∨ p3) → False)) ∨ ((False ∧ p2) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_254292964469054745909340051064 : ((p2 ∧ p3) → ((p4 → (True ∨ (((False ∨ p2) → (True ∨ p5)) ∨ (p5 ∨ p5)))) → (False ∨ ((p3 ∨ p2) → ((False ∨ (p4 ∨ p3)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135418034726241645750761743018 : ((((p3 ∨ p4) → ((((p2 → (p3 → p1)) ∨ ((True → p3) ∧ p2)) ∧ (p2 ∨ False)) ∧ p2)) ∨ (True → (p3 ∧ False))) ∨ (True → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696442135673723548284069924673 : ((((((p3 ∧ ((p2 ∧ (False ∨ p4)) → (False ∨ False))) → p5) ∧ p3) ∧ ((((False ∨ True) ∨ True) ∨ p5) → ((p5 ∨ (p1 ∨ True)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112685046021276302218676219780 : (((((((((p1 ∧ ((p5 ∨ p2) → (p2 ∨ p5))) ∨ p3) ∨ p1) ∧ False) ∧ p1) → p5) ∧ (p4 → ((False → p1) ∧ p3))) → False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37837319028431348506676028699 : ((((p3 ∨ ((True ∧ (True ∧ (p1 ∨ (((True ∨ p1) ∧ ((p5 ∧ p1) ∧ p3)) → p2)))) ∧ (p4 ∧ (p5 ∨ (p3 ∧ p3))))) → p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357995731882353667769734216979 : (p5 → (False ∨ (((((p5 → (False ∨ (p4 ∨ (p3 → p4)))) → p4) ∧ p5) → p4) ∨ ((p2 → (p5 ∧ p5)) → (p1 → ((p3 → p5) ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181574960968453624188232136745 : ((p1 → ((((p4 → p3) ∨ (False → (p3 ∧ True))) ∨ (False ∨ False)) ∧ p2)) → ((p1 → (p3 → ((True → (p2 ∨ p5)) ∨ (p3 ∨ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254433147795014034193461210812 : ((p2 ∧ p5) → (p5 ∧ ((((p2 ∨ p1) ∨ ((p3 ∨ p4) ∨ p3)) → (True ∧ p4)) ∨ (p4 ∨ (p5 ∨ (p5 → ((p5 ∨ p4) → (p2 → p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67607014816724029245435318993 : ((p1 → (p2 ∧ (((p2 → p2) ∨ (True → (((((p2 ∨ p4) ∨ p2) → p1) ∨ p1) ∨ ((p5 ∨ p3) → (p1 ∨ (True ∨ False)))))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181072236461378211736535480479 : (((p1 ∨ p4) → (p3 ∧ (((((p2 ∧ p5) → True) ∧ False) ∧ p5) → p3))) → ((p2 ∧ ((p4 → p1) ∧ (p3 ∧ (p1 ∨ p3)))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622062769175970232308173253467 : ((((p2 ∧ ((p5 → ((p2 ∧ (((p4 ∨ p5) → (p5 ∨ p4)) ∧ (((p2 ∨ False) ∨ (p2 ∨ (False → False))) ∨ False))) ∨ p2)) → p4)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_778439998145435556170422057239 : (((p1 ∨ (p3 ∧ ((p3 → True) → (p5 → (p4 ∨ (p3 → ((((False → True) ∨ (p1 ∧ p1)) ∨ (p3 ∨ (True → (p3 ∨ p2)))) ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672482687076717639569714914318 : (((((p1 ∨ ((True ∧ ((((p4 ∨ p5) ∧ p5) ∨ p1) → (p5 ∨ False))) → (False ∧ ((p2 ∧ p2) ∧ True)))) → False) → ((False ∧ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118144604413854172411945868272 : ((False ∨ ((True → ((((((p4 → p4) ∧ p1) ∧ p1) ∧ False) ∨ True) ∧ p1)) ∨ ((True ∧ (p3 → False)) → (False → (p5 → p5))))) ∨ (p1 ∧ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110936226793978231203808011937 : ((((((True ∨ (True → (p4 ∧ p3))) → (((True → True) ∨ (p2 ∧ p1)) → p1)) → (p5 ∨ (p1 ∧ p2))) ∧ (p3 ∨ p5)) ∧ p5) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152607257552804631072174646948 : (((p4 ∧ p2) ∧ (((p4 ∨ p4) → ((((p4 ∨ True) ∧ False) ∨ False) ∧ True)) ∧ ((p2 ∨ p3) ∨ (p5 → p2)))) → (((False ∨ p2) → True) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : (p4 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h21 : (p4 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h22 := h7 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h26
      case inr h29 =>
        -- False on the left can always be used.
        apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h31 : (p4 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h32 := h7 h31
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h37 =>
        -- False on the left can always be used.
        apply False.elim h36
      case inr h38 =>
        -- False on the left can always be used.
        apply False.elim h36
    case inr h39 =>
      -- False on the left can always be used.
      apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49331193047869638906103583039 : (((p5 ∨ ((p4 ∧ (((True ∨ p5) → ((p4 ∧ (p2 → (p2 → p2))) ∧ p2)) ∨ (p3 ∨ True))) → (p5 ∧ p3))) ∨ (p5 ∨ (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135089279362582247237937162251 : (((((p3 ∨ (True ∧ ((False → p4) ∨ p2))) ∧ (p1 ∨ p1)) ∧ (p5 ∨ (p1 ∧ ((p3 → p2) ∧ p5)))) ∨ (False ∨ True)) ∨ ((p3 ∧ p1) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638254348583474395996289976567 : (((((True → (True → (((p5 ∧ p1) ∧ p2) → True))) → ((p2 ∧ (False → ((p1 ∨ p3) → True))) ∨ ((p3 ∨ True) ∨ (p1 ∧ p1)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187192102815112800160787650522 : (((False ∨ True) → ((p3 → ((p5 ∨ p1) ∨ p3)) ∧ (p3 ∧ False))) → ((((p1 → p1) → p2) ∧ (p1 ∨ (((p2 ∨ True) ∨ p1) ∧ p1))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1774962803021141543957466372 : (((p1 ∨ (((p1 → (p5 ∨ p1)) → ((p4 ∧ p4) ∧ True)) ∧ ((p2 → ((p2 → p2) ∧ p3)) → False))) → p5) ∨ (p2 → (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118362801162121500034520904790 : ((p2 ∨ ((p4 ∧ (((((p4 ∨ ((False ∨ True) ∧ True)) → (p1 ∨ p2)) ∧ False) ∨ p2) ∧ ((False ∨ p5) ∨ p4))) ∨ (p1 → True))) ∨ (True ∧ p5)) := by
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
theorem thm_5_vars_44540368308254756122512905753 : (((((p5 ∧ False) ∨ ((p3 → False) ∧ ((False → p3) ∨ p1))) → (((True → (True ∨ (p1 ∨ (p2 ∧ p3)))) ∨ True) ∨ (p1 ∨ p1))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53245058018614563796110936100 : ((((p4 ∨ (p3 → p2)) → (p4 ∧ (((p2 → False) → p4) → True))) ∨ (p4 ∨ ((((p5 ∧ (p4 → (p5 ∧ p3))) → p4) ∨ p5) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58361524900110322654528411675 : (((p1 ∨ False) ∧ ((p2 ∧ ((p1 → p5) ∧ (p3 ∨ ((p4 → ((True ∧ (((p4 ∧ (p1 ∨ True)) ∧ p3) ∨ p4)) ∨ p4)) → p1)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678734344869976790880061039596 : (((((p4 ∧ p5) → ((p4 ∨ (p5 → (p1 ∨ ((False ∨ True) ∧ ((True ∧ p4) ∨ p1))))) → (p2 ∨ p1))) ∨ (True ∧ ((True ∨ p5) ∨ p2))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_956207501263382187325526233353 : (((((p1 → True) ∨ p3) → ((((p5 ∧ ((p4 ∨ ((False ∨ (True → (p3 ∨ p4))) → (False ∨ (p3 ∧ p3)))) ∨ p4)) ∨ p2) → p1) ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114102742259495924686178986211 : (((p3 ∧ (p3 ∧ ((p1 ∨ p4) ∧ (((False → (p3 ∧ p4)) → p1) ∨ (False → (p3 ∧ (p3 → p1))))))) ∨ (p5 → (p2 → p2))) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644420148436071863614368477658 : ((((False ∨ (True ∨ (((p2 → p5) → p1) ∧ ((True ∨ p5) ∧ ((((p1 ∨ True) → p3) → p1) → ((p5 ∧ (p1 → p3)) ∧ True)))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37109822007283056929460457790 : (((((((p3 ∧ ((p5 → (False ∧ (p4 ∨ p4))) ∧ p3)) → p5) ∨ ((p4 ∧ p4) ∧ ((True ∨ (True ∨ True)) ∧ p5))) → False) ∧ True) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159213744794327186913119704594 : ((p2 → ((p2 ∧ False) ∨ (False ∧ (((False → p2) ∨ ((((p2 → p3) ∧ p2) ∨ p5) ∨ p5)) ∨ p5)))) ∨ (False → (p5 ∧ ((p5 ∧ p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57796966296502771745265026984 : (((p1 ∧ (p3 ∨ p4)) → (((((p2 ∧ p5) ∧ (False ∧ p1)) → (p5 ∨ (p3 → (True ∧ p1)))) ∨ (p4 ∧ False)) → ((True → False) → p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110936735879960973205294712926 : ((((((((p2 ∧ (False ∨ p5)) ∨ (p1 → p2)) ∨ p2) ∧ (True ∨ True)) ∨ (((p1 ∨ True) → p5) ∧ False)) ∧ (p2 ∧ p3)) ∧ p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80082382400988132181707555917 : (((((((p4 → (p1 → False)) → ((((p2 → p5) ∨ p2) ∨ True) → (p2 ∧ p3))) → (True ∧ (p4 ∨ p5))) → p5) ∨ True) → (p2 ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 → (p1 → False)) → ((((p2 → p5) ∨ p2) ∨ True) → (p2 ∧ p3))) → (True ∧ (p4 ∨ p5))) → p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232508985753247106932019093032 : ((True ∧ (p2 → p3)) → ((False ∨ (((((p4 → True) → ((True ∧ True) → (p5 ∨ (p1 ∨ True)))) ∧ (p2 ∧ p1)) ∧ False) ∨ (False ∧ p1))) ∨ True)) := by
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
theorem thm_5_vars_3962320218681389737624196498 : (p1 ∨ ((((p3 ∧ p5) ∧ (((((p2 ∨ False) → ((False ∨ p1) ∧ p3)) ∧ p4) → (p3 ∧ (p3 ∨ (p4 ∨ p5)))) ∨ p1)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_498993033005755469243055955535 : (((((False ∧ p2) ∧ p1) ∨ (((p5 ∧ p2) ∨ (((p2 ∨ (False ∧ p5)) ∧ p1) ∨ p3)) ∨ (p4 → (p3 ∨ (((p3 ∧ p5) → True) ∨ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47534990129390324235828991888 : (((p4 ∨ ((p5 ∨ p1) → (p4 → (((True ∧ ((p2 → p3) ∨ (p3 → False))) ∨ True) ∨ (False → ((True ∧ p5) ∧ p3)))))) ∨ (p2 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134866352655320477955494091979 : (((False → (True ∨ ((p5 → ((p3 ∨ (p5 → p3)) ∨ ((p3 → p1) → (True → p3)))) → ((p4 ∨ p2) → p1)))) → p5) ∨ (True ∨ (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112056316173381417613066618278 : ((((p2 ∧ p5) ∧ (p1 ∨ (((p1 ∨ ((p5 ∨ ((p5 ∨ True) ∨ (p1 ∧ p3))) ∧ ((p3 → p1) → p1))) ∨ p3) → p2))) ∨ p3) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165663849915274336478103396112 : (((False ∧ (p2 ∧ (p5 ∨ (p4 ∨ p4)))) ∨ (((True → p1) → ((False → True) ∨ p5)) ∨ p2)) ∨ (False ∨ (p4 → ((p2 → (p3 ∨ p4)) ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64957750744208071935492747020 : ((p2 ∨ (((p4 ∨ p5) ∨ (p1 ∧ ((True ∨ p4) ∨ False))) ∨ (((p3 ∧ (p3 ∧ (p3 ∧ True))) ∧ ((p5 → (False ∧ p4)) ∨ p3)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153750862740286413815177177177 : ((p4 → (((((((((p2 → p4) ∨ p4) → p2) ∨ p5) → p1) ∧ ((p5 ∨ False) ∨ p5)) ∧ False) ∧ p1) ∧ p3)) → (((p4 → False) ∨ p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



