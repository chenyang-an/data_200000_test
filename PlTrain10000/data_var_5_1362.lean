variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233114634984808082855647623771 : ((p4 ∧ (p5 → p1)) → (((p5 → (p3 ∧ ((p2 → (p2 → (False ∨ (((p5 → p2) ∧ (p1 ∨ p3)) → (p2 ∧ p2))))) → p4))) → p3) ∨ p4)) := by
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
theorem thm_5_vars_114960057218391136373692113627 : (((p2 ∨ ((((p1 → p1) ∧ ((p5 ∨ p1) ∨ (False ∧ p5))) ∧ p3) ∨ p1)) → (True → (p5 ∧ (((p2 ∧ False) ∧ False) ∧ p4)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213293645817306024447033083939 : ((((p4 → p2) → p3) ∧ p2) ∨ (((((p4 ∧ (True ∧ False)) ∧ (p1 → (p3 → (True ∧ p2)))) ∨ p1) ∨ (p3 → (False → (p5 ∨ p5)))) ∨ p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194049422141771142577908981543 : ((p5 ∨ ((p3 → False) ∧ (p2 → ((p3 → False) → False)))) → ((((((p5 ∧ (False → p4)) → p5) → (p2 ∧ p2)) → (p3 ∨ p1)) ∨ p3) ∨ True)) := by
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
theorem thm_5_vars_257393424684912627052953087187 : ((p2 ∨ p5) → ((((False ∧ (p2 ∧ True)) ∨ p2) ∨ p3) ∨ (p2 → ((p2 ∧ (True ∧ p2)) ∧ (((False ∨ p1) ∧ True) ∨ ((p2 → False) ∨ p5)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657214653939629161072393140339 : ((((((p2 ∧ p4) → p3) → ((((p4 ∧ p3) ∧ p1) ∧ ((((p2 → True) → False) ∨ (p3 ∨ False)) → p1)) → (True → p5))) ∨ (p1 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_169003583300364966116544550028 : ((p1 → ((True ∧ (False ∧ (p3 ∧ (False ∧ p1)))) ∧ ((p4 → ((p5 ∨ False) → p4)) → p5))) → ((False ∨ p2) → ((p1 ∨ (True → p4)) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42909752682693843785556954754 : (((p3 → (p2 ∧ (p1 → (((p3 → (((p2 → (p4 ∧ p3)) ∨ False) ∨ (p3 ∧ (p1 → p4)))) ∧ p2) → (p4 ∧ (False ∧ False)))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345473376028935216036445025093 : (p3 → ((((p1 → False) → ((p3 ∧ ((p3 → True) → (p1 ∧ ((False → p3) → True)))) ∨ (p4 → (p1 ∧ p1)))) ∨ (p4 → (p4 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614488168906119301332424679822 : (((((((((True ∨ (False ∧ p4)) ∨ (p5 ∧ (p5 → True))) ∧ True) → (True → (p5 ∨ p4))) → p4) ∧ (p1 ∧ ((p1 ∧ p2) ∧ True))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_214566920579027967477148038363 : (((p2 ∨ True) ∧ (p4 ∧ True)) ∨ (p3 ∨ ((((((False ∧ ((p3 ∨ p5) ∨ p2)) ∨ (False → (False ∧ (p1 ∨ p3)))) → p1) → p5) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_198578181632213127676362542646 : ((p1 ∨ (p3 ∧ (False ∨ ((True ∧ True) ∨ p5)))) ∨ ((p4 → True) → ((p1 ∧ (True ∨ p5)) ∨ (((p3 → p4) → p1) → (p1 ∨ (p2 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231959469044187684554529700275 : (((p1 ∨ p2) → p5) → ((((p5 ∧ True) ∧ ((p2 ∧ ((((p2 ∧ p5) → p3) ∧ p3) → p1)) ∧ (((p2 ∨ p4) → True) → p1))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780017496233150242962104004004 : (((p2 ∨ (((((p1 ∨ ((False ∨ (p5 → p5)) → True)) ∨ (p2 ∨ False)) ∧ (False ∧ p3)) ∨ (p5 → (p1 ∨ (False ∧ p4)))) ∨ (p1 ∨ True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_119758910533655310447430270267 : ((((p2 ∧ ((False → ((p3 ∧ ((((p5 → True) → p1) ∨ False) → (p4 ∧ p3))) ∧ ((p5 ∨ p3) ∨ False))) ∨ p5)) ∨ p1) ∧ p4) → (p1 → p1)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716437959940877111158312026544 : (((((p5 → True) ∧ (p1 → True)) ∧ ((p4 ∨ True) → (((p1 ∨ (((True → p5) → (p3 → p1)) → p2)) → p3) → (False ∨ (p1 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215986148233705970725954292678 : ((p4 ∨ (p4 ∧ (p5 ∨ p2))) ∨ ((((p2 → (p2 → (p2 ∨ p5))) ∧ (p1 → (p4 ∨ p1))) → (False ∧ p2)) ∨ ((p4 ∧ (p1 ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51891395892529832581091854127 : (((((((p1 ∧ p4) ∨ p4) ∨ False) → ((p1 ∧ (False ∨ p5)) ∧ (p5 ∧ False))) → p2) ∨ (p5 → ((p3 ∨ p5) ∧ ((p2 ∨ True) ∨ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616732993568280259487929491652 : ((((((p2 ∧ ((p1 → (p3 ∨ p1)) → p3)) ∨ (p1 ∨ True)) ∨ (((p4 → p5) ∧ ((((True ∧ p5) → p3) ∨ True) ∧ p1)) → p2)) ∨ p2) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317782979875337651103272902431 : (p4 ∨ (((((((p1 ∨ p1) → (p2 ∧ p2)) → p1) → (p3 ∧ p5)) ∧ p2) → ((((p3 ∨ (p5 ∨ (p4 ∨ p5))) ∧ p4) ∨ False) ∨ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_66735503969349336846811952635 : ((True → ((False → False) → (p2 ∧ (p2 → (p3 ∧ (((((p1 ∨ p1) → p5) ∨ (p5 ∧ ((p2 → p4) → (p5 → p5)))) → p3) → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932101897745522482041210275849 : ((((((p1 ∨ True) → (p1 → (p1 ∧ True))) → False) ∧ ((False ∨ (((False ∧ (p3 ∧ p4)) ∨ False) → p3)) ∨ (True ∧ (p5 ∨ (False → p3))))) → p5) ∧ True) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : ((p1 ∨ True) → (p1 → (p1 ∧ True))) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h7
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : ((p1 ∨ True) → (p1 → (p1 ∧ True))) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h18
      -- False on the left can always be used.
      apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622725648053902952027500073273 : ((((p4 ∧ ((p5 ∨ p5) ∨ ((p2 → (p1 ∨ p4)) ∨ ((False → False) → ((False ∧ ((True ∧ (True ∧ p2)) ∧ p2)) ∧ (False → p2)))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145347748241807851404454151195 : (((p2 ∧ ((False ∨ (p2 ∧ p3)) → p4)) → ((False → ((p1 → True) ∧ (False → True))) → ((p4 ∨ p5) ∨ True))) ∧ (False ∨ ((True ∨ p4) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_116378238720637267638647940651 : ((((False → p5) → True) → (True ∧ (((p3 ∧ ((p2 ∨ p2) ∨ ((p1 ∨ (p3 → False)) ∨ True))) → ((p5 ∧ p3) ∨ p2)) ∨ True))) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205158457119846084478397854227 : (((p2 ∧ (p5 ∧ p4)) ∧ (p3 ∨ p1)) ∨ (p4 → ((p5 ∧ ((p4 ∨ (p1 ∧ (((True ∨ p1) ∨ (p1 ∧ False)) ∨ p5))) ∨ p1)) → (False ∨ True)))) := by
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42365081581077669378415682413 : (((p3 ∧ (p1 → ((((((True ∨ p2) ∧ p4) ∧ (p4 ∧ (p3 ∨ p4))) ∨ ((p1 ∨ (p3 ∨ p1)) → p3)) ∧ (p5 → p2)) ∨ p4))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691866041021138680020790907798 : ((((False → (((True ∨ ((p1 ∧ p3) ∨ p3)) ∧ True) → ((p1 ∧ (p2 → False)) → p2))) → ((((p2 ∧ p5) ∧ True) ∧ p2) → (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52177800580680306226896126681 : ((((((p1 ∧ False) ∨ (p4 → p1)) ∨ p1) → ((p4 ∧ (True ∨ False)) ∨ (False ∨ p5))) → ((p2 ∧ (p4 → (True ∨ (False → p5)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672910938766062331643933092832 : ((((((False → (p5 → ((p3 ∨ ((p1 → p4) ∧ p4)) → (p4 ∨ p2)))) ∨ (p2 ∨ p4)) → (True ∧ (p3 ∧ False))) → ((p5 ∨ p5) ∨ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (p5 → ((p3 ∨ ((p1 → p4) ∧ p4)) → (p4 ∨ p2)))) ∨ (p2 ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777493144066241108025961803957 : (((p1 ∨ ((((p2 ∨ (p1 ∧ (p5 ∨ (p5 ∨ False)))) ∨ (p2 ∧ True)) ∨ (False → p5)) ∨ (p2 ∧ (p3 ∨ (p4 ∨ (p3 ∧ (p5 → True))))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44637917582919003312048571779 : ((((False → ((True → (p5 ∧ True)) ∨ False)) ∧ (((p2 ∧ ((False → (True ∧ p5)) ∧ p4)) ∧ p4) ∨ (((p1 ∨ p3) → p2) → p1))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309927295731224415866415623634 : (p2 ∨ (((((p5 → p4) ∨ (p2 ∨ False)) → True) → (p3 ∧ (((False → (p5 ∧ p4)) ∨ p3) ∧ False))) ∨ ((p2 ∨ (False → p5)) ∨ (p2 → True)))) := by
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
theorem thm_5_vars_52486153718355050390186672217 : (((p1 → ((True ∧ p2) ∧ ((p2 ∧ ((p2 ∨ (p2 ∨ p1)) ∨ True)) ∧ True))) ∧ ((p5 ∧ (p4 ∨ (p5 ∨ p3))) ∧ ((p5 ∨ True) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41444182865264407933921682074 : ((((p5 ∨ (((True → p4) ∧ p5) → (p3 ∧ (p2 ∧ (p1 ∧ (False ∧ p1)))))) → (p4 → (False ∧ (False → (False ∨ (p4 → p2)))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319460226169322069641123236227 : (p4 ∨ ((((p3 → (p3 ∨ False)) → False) → ((p5 ∨ p4) ∨ (p4 ∨ p5))) ∨ (p2 ∨ (False ∨ ((False ∨ (p3 ∨ p4)) → (p4 ∨ (p5 ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p3 ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221550580984532476245940779053 : (((p3 → True) ∨ p4) ∧ (((p4 ∧ (True → (((False ∨ True) ∧ p2) → p1))) ∧ (p2 → p4)) → (((p1 ∨ p1) ∨ p1) → ((p2 ∨ p3) → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h2.left
        let h9 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h2.left
        let h14 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h2.left
      let h19 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h2.left
        let h26 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h25.left
        let h28 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h2.left
        let h31 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h30.left
        let h33 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h29
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h2.left
      let h36 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- One of the premise coincides with the conclusion.
      exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2085363001450044320731968767 : (((((p1 ∨ (p5 ∧ (False ∨ p5))) → p3) ∨ p1) → ((p3 ∨ ((p1 ∨ p2) → True)) → p1)) ∨ (p3 ∨ (True ∨ (p1 ∨ (p2 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133840294749269969477015188658 : ((((p3 → True) → ((True ∧ ((((p4 → ((p3 ∨ True) → p1)) ∧ p3) → p2) ∨ p4)) ∧ (p3 ∨ (False → p2)))) ∧ p1) ∨ (False → (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343321544003301319063206991052 : (p2 → ((p3 ∨ p2) ∧ (((((((True → p4) → (p1 → p1)) ∨ False) ∨ p2) ∨ p2) → p1) ∨ (((p3 ∨ (p3 ∧ p5)) → (True ∨ p2)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_619453163708931625869263752571 : (((((p1 ∨ (p2 ∧ p2)) → (((p4 ∨ p5) → (((p1 ∧ (False ∧ (p5 ∨ p1))) ∧ (p5 → p2)) ∧ (False ∧ (p1 → p3)))) → p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_56211907558901259240414496745 : (((p1 ∨ ((p1 ∧ p2) → False)) ∨ (p2 ∨ (p2 ∨ (p3 ∨ ((((((p3 ∨ p3) → (p5 → p2)) → (p4 → p4)) ∧ p2) → p5) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91001206288077864776690140018 : (((p1 → False) ∧ (p1 ∧ (p2 → ((((p5 ∨ ((p1 ∧ p3) ∨ ((False ∨ False) ∧ p5))) → ((True → p3) ∨ p4)) ∨ p2) ∨ (p3 ∧ p3))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799582394839919655490375420529 : (((p1 → (p4 ∨ ((p2 ∧ p5) ∧ (((p5 ∨ ((p4 → p5) ∧ ((p4 → False) ∨ p1))) → (p1 → p1)) ∧ (p2 → ((False ∨ p5) → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166579948711397077247030942099 : ((True → (((((p1 → p3) → (p5 ∧ p1)) → p1) ∨ ((p2 ∧ p1) → p3)) → (p5 → p5))) ∨ ((p1 → ((p5 ∧ (True ∧ p3)) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807387879346283916906599034206 : (((p4 → ((p5 ∧ ((p2 ∨ (p3 ∧ ((p1 ∧ p5) ∧ True))) ∧ p5)) ∨ ((True ∧ (((p3 → p5) → p5) ∧ False)) ∨ ((p4 → p2) → p2)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647625969778036359798997897119 : ((((p5 → (((((p2 ∧ p4) ∧ (p5 ∧ ((p3 ∧ p1) ∧ p2))) → (p5 ∨ p3)) ∨ p1) → ((False → ((p2 ∧ False) ∨ False)) ∧ True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262081604622340712887327025012 : (True ∧ ((p3 → (((((((((p5 → True) → (p4 → p2)) ∨ p2) → p4) ∨ p2) ∨ (p3 ∨ (True → p2))) ∧ True) ∨ p4) ∨ (p1 ∧ p4))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201170753157416108133143583624 : ((p1 → ((p5 ∧ (p3 → (True → p2))) ∧ True)) → (p2 → ((((((p5 ∧ False) ∧ p2) ∨ p1) ∨ p3) ∨ (p4 → p5)) ∨ ((p2 ∧ True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58689506012861774533221050606 : (((p2 → p2) ∧ ((((p5 → p5) → p4) ∧ True) → (True → ((p3 ∧ p5) ∨ (((p5 ∨ p2) ∧ True) ∨ ((False → (False → False)) → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186918090917808022041914036364 : ((((p3 ∨ p2) → p3) ∧ ((((True → p2) ∨ True) ∧ p2) ∨ p2)) → ((p3 → False) ∨ ((p4 → (((p3 ∨ p3) ∧ p4) ∨ (p2 ∨ p3))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50543134950178836709565960782 : (((((p1 ∨ (p2 ∧ (True ∨ (p2 ∨ p4)))) ∨ (((p3 ∧ p5) ∧ ((False ∧ p3) → p1)) → p5)) ∨ True) → (((False ∧ True) → p5) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259156591959842685148034925478 : ((False → True) → ((p1 ∧ (False ∨ (p5 ∨ p3))) ∨ (p2 ∨ (((False ∨ (True ∨ True)) ∨ True) ∨ (True → ((p3 ∧ True) ∨ ((True → p1) ∧ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_764807713771871058114747044788 : (((p4 ∧ ((((((p2 ∨ True) ∨ (p4 ∨ ((p4 ∨ (p4 ∨ (p2 ∨ ((p4 ∨ p3) ∨ (False → p3))))) ∨ p5))) → p4) ∨ p1) → p3) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246785577316229902077086860721 : ((p5 ∧ p5) ∨ (p3 ∨ (p1 → (((p5 ∧ p1) ∨ ((p3 ∨ (p2 ∧ True)) ∨ (False → (p2 ∧ (p5 → p5))))) ∨ (((True ∧ p2) → p4) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47979321856129641196701644463 : (((((p3 ∧ ((((p4 ∨ (p2 ∧ (False ∧ True))) ∧ p4) ∨ p1) ∨ (p1 → p4))) ∧ False) → (p3 ∧ ((False → p2) ∨ p4))) → (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148036766698924323235260257768 : ((((False ∧ p5) ∨ (((p4 ∨ True) → (((True ∧ (False → p5)) → (p3 ∧ p4)) ∨ True)) → p2)) ∨ (p5 ∧ p2)) ∨ (((p5 ∨ p4) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300911518612204429778718267026 : (False ∨ ((((p5 ∧ p3) → p5) → (True → (False ∨ (((False ∧ p4) ∧ p3) ∨ p5)))) → (((p5 → True) ∧ False) ∨ ((True ∨ (p1 ∨ p3)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ p3) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336259002717221429111871606603 : (p1 → (((p3 ∨ ((p3 ∨ (p3 ∧ (((p2 → p1) → p1) → (p3 → (p2 ∨ p5))))) ∨ p4)) → ((False → ((True ∧ p4) ∧ p2)) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336468659805931379490463820384 : (p1 → ((p2 → (((((p4 ∧ p3) → (p5 ∨ True)) ∧ ((p3 ∨ ((p3 ∧ (p1 ∧ (p4 → True))) ∨ p1)) ∧ (p3 ∨ False))) ∧ p1) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149280934921926904964445282042 : (((p2 → False) ∨ (((False ∨ False) ∨ ((False ∨ ((p2 → (p1 ∨ (p1 → (p3 → False)))) ∧ p4)) → p1)) ∨ True)) ∨ (p4 → ((p3 ∨ False) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707685545245651117397510644043 : (((((p1 → p5) ∨ (((p1 ∨ p1) → True) ∧ p5)) ∨ (p1 → ((p5 → (((p3 → (p2 → p4)) ∨ ((p3 ∧ p3) ∧ p3)) ∨ p2)) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118389264902816031369608203163 : ((p2 ∨ ((p2 ∧ ((p4 ∨ (p4 ∨ p2)) → p1)) ∨ ((((((((False ∨ p3) ∧ True) ∨ p1) ∧ p5) ∧ p3) ∧ False) ∧ p2) ∨ True))) ∨ (False → False)) := by
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
theorem thm_5_vars_769893557310223086309503453624 : (((p5 ∧ (True → ((((p1 → (((p2 ∨ (p2 ∧ p3)) ∧ (p2 ∨ False)) ∨ p1)) ∨ (p3 → (p2 ∨ True))) ∨ p1) → (p5 ∨ (p4 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40972496149926425556557479738 : ((((((p1 → p3) ∨ p5) ∨ (p2 ∨ ((p1 ∨ ((True ∨ p1) ∧ (p4 → p3))) ∧ ((p1 ∧ p4) ∨ (p3 → True))))) ∨ (p2 → p2)) ∨ p5) ∨ False) := by
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
theorem thm_5_vars_200884908509202922816689941336 : ((False ∨ ((p1 ∨ (p5 ∨ False)) ∨ (p4 → p4))) → (((p1 → (False ∧ p5)) → p4) → (False ∨ (((p4 ∨ p4) ∨ (False → False)) ∧ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177956334873072314184381021689 : ((((p1 → p2) ∧ ((p2 ∨ (p1 ∨ p5)) ∨ (p4 ∨ (p5 ∧ p4)))) ∨ p1) ∨ (((p3 ∧ False) ∨ False) → (p1 → (p4 ∨ (p5 ∨ (p2 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307244689915754613727868890405 : (p1 ∨ (p2 ∨ ((p4 ∨ ((True ∧ ((True ∧ p5) ∧ p4)) → (False ∧ (((p2 → False) ∨ ((p5 ∧ ((p2 → p2) ∧ False)) → p2)) ∧ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192379063325193290761865732506 : (((((((p2 → False) ∨ False) → p1) ∨ p2) ∧ True) ∨ p3) → (((p4 ∨ (True → p1)) ∧ True) → ((((p5 ∨ True) ∨ (True → True)) ∨ True) ∨ p3))) := by
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
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22353369972892336664161208809 : ((((((True ∨ p4) ∨ p5) → False) → (p4 ∧ p1)) → ((p4 ∧ ((p4 → False) → p5)) → ((((p5 ∧ p5) ∧ p4) → (p1 ∧ p3)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48077555827665069866589513728 : (((((p2 ∨ (True ∧ (p4 → p2))) ∧ p3) ∨ (p2 ∨ ((True ∨ ((p1 → (p4 → (True → p2))) ∨ (True ∧ True))) ∨ p2))) → (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56080601795683604813927329993 : ((((p5 ∨ (p5 ∨ p3)) → False) ∨ ((True ∧ p5) ∧ (((p4 → (p5 ∧ p4)) ∧ ((False ∧ False) ∨ False)) ∧ ((p1 ∨ p5) ∧ (False → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113541594635538399318186245261 : (((((p3 ∨ (True ∨ p5)) ∨ True) → (p5 → ((((p5 → p3) → p3) ∧ True) ∧ ((True → p3) ∨ (p4 ∨ p3))))) ∨ (False ∨ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329238108694970754605986214023 : (True → ((p1 ∨ (p5 → True)) ∧ (((((((p3 → p5) ∨ (p5 → True)) ∨ p3) → (p4 ∧ ((p5 ∨ (p1 → p3)) ∨ p4))) ∨ True) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782972497373233690153411125121 : (((p3 ∨ ((((p4 → p3) ∧ ((((p2 → False) ∨ p5) ∨ (p2 ∨ (p4 ∧ (p3 ∨ p1)))) → ((p4 → False) ∧ p5))) ∨ p2) ∨ (True ∨ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_55124431655796257045176784901 : (((((True ∨ p1) → (False ∧ False)) ∧ True) ∨ ((True ∧ p1) → ((p4 ∨ (((False ∨ p5) → p1) ∨ False)) ∧ (False → ((p5 → p4) → p4))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61353334872830664518319385480 : ((p1 ∧ ((((p5 → (p3 ∨ p4)) ∨ p2) → (((p2 ∨ (True ∧ ((((p4 → (True ∧ p3)) ∧ p4) → p4) ∨ True))) ∨ p2) ∧ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_512661220817895420624354515465 : ((((p4 ∧ False) ∨ ((False ∨ ((p5 → p5) ∨ p4)) ∧ ((((p3 ∧ p3) ∧ p4) ∧ (p3 ∧ p4)) ∨ (False → ((True ∨ (p1 ∨ p3)) ∨ p2))))) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117172255238140626364837923400 : ((True ∧ ((((p2 → p4) ∨ True) → (True ∧ (((p2 ∧ p2) → ((p1 → True) → ((p3 ∧ p5) ∧ p3))) ∨ (p1 ∨ p3)))) → p2)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185491419145420309768900033733 : ((p2 ∨ ((p2 ∨ ((p4 ∧ p2) ∨ ((False → p1) ∧ p2))) ∨ True)) ∨ (((False ∨ p4) → False) → (True → (p4 ∨ (p5 ∧ ((p4 ∨ p5) → p3)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247633927591008802429783579805 : ((False ∨ p5) ∨ (p1 ∨ (((p2 ∨ p2) → p1) ∨ ((False → p3) → (((True ∨ ((p5 ∧ ((p5 ∨ (p3 ∨ p2)) ∨ p2)) → p4)) → p2) → p2))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ ((p5 ∧ ((p5 ∨ (p3 ∨ p2)) ∨ p2)) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185609067326658919465480303874 : ((True → (((p2 ∨ ((p1 ∧ (p4 ∨ p4)) ∧ p2)) ∧ True) ∨ True)) ∨ ((p5 ∨ (p5 → p1)) ∨ ((((False ∨ p1) ∨ p5) ∨ False) → (False → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301278482247565325471274449449 : (False ∨ ((((p5 ∨ (False ∧ p2)) ∧ p1) ∨ p4) → ((p1 ∨ ((((((p2 ∨ p1) ∨ p4) ∨ p2) ∧ True) → False) ∧ p5)) ∨ ((p4 → True) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343256630954441933296811844640 : (p2 → ((p5 → (p2 → p1)) → (p3 → ((((p3 ∨ p5) ∧ p1) → (p5 ∧ (((((p1 ∧ p3) → p3) → False) → (p5 ∨ p3)) ∧ p5))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198174453837924586998405035081 : (((p3 ∨ p5) → (False ∧ ((p3 ∨ p4) ∧ p5))) ∨ ((((p4 → p5) ∨ (p3 → p2)) ∨ ((((p2 ∨ (p4 → p3)) ∧ p5) ∧ p4) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48639231118385395267181055262 : (((((p4 ∧ ((p3 ∧ p1) ∨ (p2 ∨ p4))) ∨ (((False ∨ (p4 ∧ p4)) → p2) ∨ p3)) → (p4 → (p2 ∧ True))) ∧ (p4 ∨ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136006728698903688292207948597 : (((p1 → (p5 ∨ ((True → True) → ((p4 ∧ False) ∨ p5)))) ∨ (p2 → (p2 ∨ (((True → (p5 ∧ p4)) ∨ p3) → p3)))) ∨ ((p5 ∧ p1) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69119137389533759388968609387 : ((p5 → (((p4 → p2) → (p3 ∧ ((p1 ∨ (p5 ∨ p5)) ∧ (p1 ∨ (p4 ∧ ((True ∨ (p1 ∧ (p5 → p1))) ∧ p4)))))) ∨ (p3 → p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738503877422330199831506863112 : ((((p1 ∧ p4) ∨ ((((p2 → p3) ∨ (False ∧ ((((True ∧ (p5 ∨ (False → p5))) ∧ (p1 → True)) ∧ p4) → p5))) → (p5 ∨ p4)) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_254332330198962086316459609416 : ((p2 ∧ p4) → ((((p1 ∨ p5) ∨ False) ∧ ((p2 ∧ (((p2 → True) ∧ ((False ∨ p4) ∧ ((p3 → True) ∧ p4))) → (p1 ∧ p4))) ∧ True)) ∨ True)) := by
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
theorem thm_5_vars_225543802458782242039564684361 : (((True → p2) ∧ p5) ∨ ((True → ((True ∨ (p5 → p2)) → ((p1 ∧ p4) ∧ (False ∧ p5)))) → (p1 ∧ ((False ∨ ((p4 ∧ False) ∧ p3)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p5 → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (True ∨ (p5 → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147154934831695306158093324145 : (((p3 ∧ ((False ∧ (False → p1)) ∨ ((((((p3 ∧ p2) ∨ p2) ∧ p1) ∧ (p1 ∧ True)) → p3) → p2))) ∧ p5) ∨ (((p4 ∨ True) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314958478000268686708514003966 : (p3 ∨ (((p4 ∨ p4) ∧ ((p1 → ((p5 → True) ∧ p2)) ∧ p5)) → ((((p3 → p1) → (True ∨ (False ∨ p2))) → False) → (p3 → (p1 ∧ p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 → p1) → (True ∨ (False ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : ((p3 → p1) → (True ∨ (False ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h15
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h23 : ((p3 → p1) → (True ∨ (False ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h25 := h2 h23
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h19.left
    let h28 := h19.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h29 : ((p3 → p1) → (True ∨ (False ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h31 := h2 h29
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135608399182681262650584719282 : (((True ∧ (p5 → ((p1 → ((p4 ∨ p1) ∨ ((False ∨ p2) ∧ (False → False)))) → False))) ∨ (((p4 ∨ p4) ∧ p4) → p4)) ∨ (p1 ∧ (p4 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150191813222805740106527731547 : ((p2 → ((((p4 ∧ (((p3 → (p3 ∨ False)) → (p1 → p2)) → True)) ∧ p5) ∧ ((p1 ∨ True) ∨ p3)) ∨ p3)) ∨ (p2 ∨ (p4 → (p1 → True)))) := by
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
theorem thm_5_vars_171541238447447971362922580535 : ((((p2 ∨ (p5 → ((((p2 → p3) → p5) ∨ (p2 → p5)) → p2))) ∨ p5) ∨ True) ∨ (p5 ∧ ((((p5 → p2) → False) ∧ False) → (False ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310147624410016471829317954305 : (p2 ∨ ((((True ∧ p1) ∨ (p5 ∨ ((p2 → p5) ∨ (p4 → (p3 → True))))) → False) → (p2 ∧ (p5 → (p5 → (p4 ∧ ((p1 ∨ True) → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ p1) ∨ (p5 ∨ ((p2 → p5) ∨ (p4 → (p3 → True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((True ∧ p1) ∨ (p5 ∨ ((p2 → p5) ∨ (p4 → (p3 → True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : ((True ∧ p1) ∨ (p5 ∨ ((p2 → p5) ∨ (p4 → (p3 → True))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342662904401828500902677583906 : (p2 → (((False ∨ (p1 ∧ (p1 ∨ p5))) ∨ ((p3 ∧ p3) ∨ p4)) ∨ (False ∨ (((p1 ∨ (p1 ∧ (((p1 ∨ p1) ∧ False) ∧ False))) ∨ False) → True)))) := by
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
theorem thm_5_vars_303200291926556297723525054985 : (False ∨ (p4 → ((p4 ∧ p2) → (((p1 ∨ (p3 ∧ ((p2 ∨ p3) ∧ False))) ∨ ((p2 → p4) → (False ∧ p1))) ∨ ((p4 ∧ p5) ∨ (False → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40150496320744200856465262935 : (((((((p3 ∧ (p4 ∧ (p1 → False))) → p2) ∨ ((p5 ∨ True) ∧ False)) ∧ ((((p1 ∧ p4) → False) ∧ (p4 ∧ p2)) ∧ False)) ∧ p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



