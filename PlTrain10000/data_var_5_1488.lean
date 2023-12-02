variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758255109388225940889981552410 : (((p2 ∧ ((((False ∨ (p1 ∧ (((((False → (p1 ∨ p4)) ∨ (p4 ∨ p5)) ∧ p3) ∧ p2) ∨ ((False ∧ p3) → p3)))) ∨ False) ∧ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166993457984043229182447545728 : (((p3 ∨ (p4 ∨ (((p4 → p4) ∨ (p5 ∨ ((True → (True ∨ p3)) ∧ p1))) ∨ False))) ∧ p2) → ((p3 ∨ p2) → (((p1 ∨ p5) ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
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
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
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
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201155807461413613827308910177 : ((False → (p1 ∧ (True ∧ (p1 ∨ (False ∨ p2))))) → (((((p5 ∧ p3) ∧ p1) ∨ p5) ∧ (((True ∨ (True ∧ False)) → p1) ∨ p5)) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246685786709294692512036279645 : ((p5 ∧ p4) ∨ ((((p3 ∨ True) ∨ (p1 → (False ∨ True))) → ((((p4 ∨ p4) → (p5 ∨ (False → (True ∨ (p3 ∧ p4))))) ∨ p4) → p5)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ True) ∨ (p1 → (False ∨ True))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∨ p4) → (p5 ∨ (False → (True ∨ (p3 ∧ p4))))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47025591468331499770866576541 : ((((False → ((False ∨ ((False ∧ p2) ∧ True)) ∨ ((p1 ∧ ((False ∧ (((True ∨ p5) ∨ p2) ∨ p4)) → p2)) ∨ True))) → p3) ∨ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69369295796804281844510880047 : ((p5 → (True → (((p2 ∨ p5) ∨ ((((((p5 ∨ p4) → (p5 ∧ p1)) → p5) ∨ ((p3 ∨ p1) ∨ (True → p1))) → p4) ∨ p2)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717131970715385468945069253088 : ((((False ∨ (p3 ∨ (p3 ∧ p2))) ∧ (p3 ∧ (True ∨ ((p5 ∨ (((p2 → (p3 ∧ False)) → (p2 → (p2 ∨ p4))) → (p4 → True))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595401599416517271021547431997 : (((((p3 → (p1 → (p4 → (((p4 ∨ (p5 → p2)) → False) → False)))) ∧ ((((True ∨ p2) ∧ ((p4 ∧ True) → p2)) → p4) ∨ p3)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651283490472228735019686613630 : (((((False ∨ (p1 ∨ p2)) ∧ ((((p1 ∨ (p2 ∨ True)) → (True → (p3 ∨ (False → (p4 ∧ p5))))) ∨ (p5 ∧ False)) → False)) ∧ (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321192922234727298875098462273 : (p4 ∨ (p3 ∨ ((p4 ∧ ((p1 ∨ (((((p3 → False) ∧ p1) → p4) ∧ p1) ∨ p2)) ∨ True)) → (p2 ∨ (p5 → (((p3 ∧ p4) → p5) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234359963226610861892470917799 : ((p1 → (p2 ∨ p4)) → (((((True → p5) ∧ (((p2 ∧ p4) → p5) → (p4 ∨ p1))) → p4) ∧ (False ∨ (True → p5))) ∨ (True ∨ (False ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304693994478400998933728704282 : (p1 ∨ (((p2 → ((True ∨ (p3 ∨ (p5 → p4))) ∧ (((p5 ∨ p1) ∧ True) ∨ (((False ∨ p1) ∨ (True ∧ p2)) ∨ False)))) ∨ p1) ∨ (p3 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66387266615728735671488305973 : ((p5 ∨ (p5 ∨ (((((p3 → True) → (((p5 → ((p1 ∧ p2) → p5)) ∧ p4) → p1)) → True) → ((p4 ∧ (p3 ∨ p4)) → p5)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56507859130309276149432437374 : (((p3 ∧ ((p2 ∧ p2) → p4)) → ((False ∧ p3) ∨ ((True → (p2 ∨ ((p3 ∨ p4) ∧ p4))) ∨ (p2 ∨ (((p3 ∧ False) ∧ p3) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244383550521518929890274623824 : ((False ∧ p1) ∨ ((True → ((((p4 → p1) → p2) → p5) ∨ (((False ∨ p4) → (False ∧ (p1 → p5))) ∨ ((p2 → p5) → p2)))) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137312882310050022946294005925 : ((p2 ∧ ((p3 → ((p2 ∨ p4) ∧ ((True → p2) ∨ p2))) ∧ ((p4 ∧ (p4 ∨ p1)) ∨ (p3 ∨ ((False ∧ True) → p2))))) ∨ ((False ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41499577304563589158139348198 : (((((p1 ∨ (p5 ∨ (True ∨ p1))) → ((p5 → (False ∨ False)) → p3)) → (((p4 ∨ p5) ∨ (False ∨ (p2 ∧ (p2 → p4)))) ∨ p1)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227925515286481991962710304132 : ((p3 ∧ (True ∧ p2)) ∨ ((p1 → (((p4 ∧ False) ∧ (p3 ∨ ((True ∧ p4) ∧ (p2 ∨ (p1 ∨ p5))))) ∧ (p4 ∨ p4))) ∨ (False → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720014754945312333397544368015 : ((((((p2 ∧ p4) ∨ p2) ∧ p1) → ((((((p3 ∧ True) ∨ False) ∧ (p2 → (p2 ∨ p5))) → ((True ∧ p2) ∧ (p4 → p3))) → p4) ∨ p2)) ∨ p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178862659756160614224543327171 : (((True → (True ∨ p3)) → ((p1 ∧ ((p1 ∨ p2) ∨ p2)) → (p3 → p2))) ∨ (p2 ∨ ((p2 ∨ (True ∨ (False → False))) ∨ ((p2 ∧ p2) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_216032235477091749619622741302 : ((p5 ∨ ((p5 → p4) ∨ False)) ∨ ((((False → False) → (((True ∨ p1) ∧ (False ∧ (((False ∨ p5) → False) → False))) → p5)) ∨ p2) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157440790862463577288438295875 : (((p2 ∨ ((p4 ∧ (p1 ∧ ((((p3 ∧ False) ∨ False) → p2) ∨ p5))) ∧ (True ∧ p5))) ∧ (p5 ∧ p3)) ∨ ((False ∨ (p2 ∨ True)) ∧ (True ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705763337499160593954617389010 : (((((p3 → ((p5 ∧ p1) ∨ False)) ∨ (p1 → True)) ∧ (((p5 → (p4 ∨ (False ∨ p5))) → p1) → ((False → ((p5 → p5) ∨ p2)) ∧ p1))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (p4 ∨ (False ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147697899134508266604025788892 : (((((p4 ∨ True) ∨ (((((False ∧ p5) ∧ p5) ∧ p2) ∨ p3) ∨ p3)) ∨ ((p2 → (True → p5)) → True)) → p3) ∨ ((p3 ∧ False) → (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176278807528024722664273879992 : ((((((p3 → p5) ∨ (p4 ∨ p5)) ∧ p3) → (p1 → False)) ∨ (p1 → p1)) ∧ (((((p4 ∧ (p2 → p5)) ∨ p4) ∧ (p1 ∧ p3)) ∧ p5) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h6.left
    let h11 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h6.left
    let h14 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135638351337711576803295501950 : ((((p5 ∧ (((((((p1 → False) → False) ∧ False) ∨ p2) → p5) ∨ p1) → False)) → p5) → (p3 ∧ (True ∨ (p3 ∨ False)))) ∨ ((p3 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111745024817849612537669805072 : ((((p4 ∨ ((((True ∨ p5) ∨ (p4 ∨ p2)) → (p3 → (False ∧ p3))) ∧ (((p5 ∧ p4) ∧ p3) ∨ (p1 ∨ p4)))) → False) ∨ p1) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180762473314957733287884995185 : (((p5 → ((p3 ∨ False) ∧ p3)) ∨ ((((True ∧ False) ∨ False) ∨ p1) ∧ p1)) → (((((p2 ∧ ((p4 ∧ p2) ∧ p4)) ∨ p2) ∨ True) → p4) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763862410559196949554191926701 : (((p3 ∧ (p4 ∨ ((((True → p4) ∨ p1) ∨ ((p5 ∨ (p2 ∧ (p5 ∨ p4))) ∧ (((p2 ∧ p1) → p3) ∧ True))) ∧ (p5 → (True ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787837958844604796760344438537 : (((p4 ∨ (p1 → ((p4 ∧ p5) ∨ (((((True → p3) ∨ p2) ∨ (((((True ∨ (True → p3)) → p2) ∧ p2) ∨ p4) ∨ p4)) ∧ False) ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179904716196903591937917313931 : (((((p3 → ((False → (True → p5)) ∧ (p3 ∧ False))) → False) ∨ p5) ∨ p2) → (((p4 ∧ (True → False)) ∧ p3) ∨ (False → (p2 → (p3 → False))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h8
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111053972247185307820108539057 : (((((p1 ∧ True) ∨ ((p4 ∧ ((p2 → False) ∧ ((False → p1) → (p3 ∧ p5)))) ∨ p4)) → (((p4 ∧ False) ∧ p2) ∨ p2)) ∧ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184325513676220086232488706392 : ((((p4 ∧ False) → (((False ∨ p1) ∧ (p3 ∨ p3)) ∧ True)) → p2) ∨ (((p4 ∨ (p1 ∧ (p4 → (p5 ∧ True)))) ∨ (p1 ∨ True)) ∨ (p5 → True))) := by
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
theorem thm_5_vars_150204216999117035259210059353 : ((p2 → ((p1 ∧ (((False → p2) → ((p4 ∨ (p5 ∨ True)) ∧ False)) ∧ (True ∨ True))) ∨ (p1 ∨ (p2 ∨ True)))) ∨ (p2 ∨ ((p1 ∨ p2) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_160190291662029267441008443867 : (((p4 ∨ (((p1 → p4) → (p1 ∧ True)) ∧ (((True → (True ∧ p5)) ∧ p3) ∨ p3))) ∧ (p1 ∧ p2)) → ((False ∨ p4) ∨ ((p5 → p3) ∧ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h16
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727996348585693490162079741472 : ((((p3 ∨ (p3 ∨ p4)) ∨ ((((p5 ∨ (((p5 ∧ p1) → p1) → p5)) → (p3 ∨ p2)) → p2) ∧ (((p4 ∧ (p5 ∨ p4)) → p2) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690232040478737092709196034183 : ((((p5 ∨ ((p1 → ((False ∨ p4) ∧ False)) ∨ ((p2 → (True → p1)) → (False ∨ True)))) ∨ (((p4 ∨ p4) ∨ True) ∧ ((p5 ∧ p5) ∨ p5))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308537833639259091698964165703 : (p2 ∨ (((((False → (p1 → True)) ∨ (p2 → (p3 ∧ p2))) ∨ (p2 → p3)) → ((p3 ∨ (False ∨ (p2 ∨ True))) ∨ ((p2 → p3) ∧ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
    case inr h4 =>
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
  case inr h5 =>
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
theorem thm_5_vars_156817846441448790628548737614 : (((p3 ∨ (((p5 ∧ ((((p3 ∧ p1) ∧ (p5 ∨ (p1 → p4))) ∨ p4) ∨ True)) → p4) → p2)) ∧ False) ∨ ((True ∨ ((True → p4) ∨ p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788627568744474234678225269744 : (((p5 ∨ ((((True → p3) ∧ (p3 ∨ ((p3 ∨ (p3 → p4)) → ((((False ∨ p1) → p3) → p1) ∨ ((p3 ∧ p2) ∧ p5))))) → p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350096835908417664825056487973 : (p4 → (((p3 ∧ ((p1 ∨ (((True → True) → (p2 ∨ (True ∧ (False ∧ p5)))) ∨ True)) ∨ ((False → p5) ∧ p2))) ∨ ((p3 ∧ False) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156674270058645936255772530221 : ((((p2 → ((p5 ∨ (False ∨ False)) → ((True → (False ∨ p4)) ∨ (p1 ∧ p1)))) ∧ (p5 ∨ p2)) ∧ True) ∨ ((p1 ∧ p4) → ((p5 ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_111663543885855702908906378822 : ((((False ∨ ((((p5 ∧ (True ∧ (((p5 → (p4 ∨ p1)) ∧ False) → (True → p2)))) → p4) ∧ False) ∧ (p4 ∨ False))) ∨ p5) ∨ p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48977034198085755492358855781 : (((((((((((p2 ∨ (p2 ∨ p3)) ∧ True) ∨ True) → False) → p2) ∧ p1) ∨ p1) → (p3 ∧ (False ∨ False))) ∨ p2) ∨ (p5 → (False → p5))) ∨ False) := by
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
theorem thm_5_vars_232399590602937732239303242575 : (((p5 → p4) → True) → (p5 → ((p2 ∨ (p1 ∨ ((p1 ∨ ((p5 → (p1 ∨ p1)) ∨ ((True → True) → (p1 ∨ p4)))) → (p1 → p3)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45500648392216550653757712131 : (((False ∨ (p5 → (((p2 → p4) → p1) → (((p3 ∧ p4) ∨ True) ∧ (p1 ∨ (((False ∧ p5) ∨ True) ∨ (True → (p4 → p1)))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139928458525641867910915068517 : (((((False ∧ (p2 → (False ∧ p4))) ∧ p5) → (((False ∧ True) → (p4 ∨ p4)) ∧ (p5 → (p5 → p1)))) ∧ (True ∧ p3)) → (p4 → (p4 ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609578724862140268722950492120 : (((((p4 ∧ ((p5 ∨ p2) ∨ (False ∧ (((False → ((p4 → p5) → (p3 ∨ p2))) ∨ (p1 → p1)) → ((p4 ∧ True) ∧ False))))) ∨ False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_149841314043856737173339818998 : ((p1 ∨ ((True → (p1 ∨ False)) → ((((p5 ∨ (True ∨ p3)) → p5) ∧ (False ∧ p4)) ∧ ((p1 ∧ p1) ∧ p1)))) ∨ ((p1 ∧ p4) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177757581954161250617291992731 : ((((True → p1) ∨ (p5 → (False ∨ ((p3 → p3) ∧ (p2 ∨ p3))))) ∧ p4) ∨ ((p2 ∨ ((p3 ∧ (p3 ∧ False)) → p4)) ∧ ((p3 → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137655525747647825084771832918 : ((False ∨ ((p5 → p3) ∨ (p1 ∧ ((p3 ∧ (p3 ∧ (((p2 ∨ (p1 → p2)) → (p1 → p2)) ∨ (p1 → p5)))) → False)))) ∨ (p2 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44943221237955479172332922218 : ((((True ∨ p3) ∧ ((p1 ∨ ((True ∧ True) ∧ (p2 ∧ (p4 ∧ False)))) ∧ (False → (((True ∨ p1) ∧ p3) ∧ (True ∨ (p5 ∨ True)))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103348045054987622289003606352 : (((True → (((((((p2 → (p1 ∧ ((True ∧ p1) ∧ (p5 → False)))) ∨ p5) ∨ p3) ∧ p3) ∨ p4) ∧ False) ∨ (True ∨ p5))) ∨ p3) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259416640552273840027617860733 : ((False → p3) → (p3 ∨ (((p2 ∨ ((p4 ∧ p2) ∧ p4)) ∨ (((((p2 ∨ p5) ∨ p5) ∧ True) → p3) → (p5 → ((p4 ∧ p2) → True)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67895835242397454118242516188 : ((p2 → (((p1 → (False → p2)) → (True → (((False ∨ (p1 → (p4 → p2))) → p4) ∨ p4))) ∨ ((((True ∧ True) → p5) ∨ False) → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303127701715246487457989563026 : (False ∨ (p3 → (((p3 → ((p3 ∧ (False ∨ (p2 ∨ False))) ∨ p1)) ∧ p2) ∨ ((True ∨ ((True ∨ p3) ∧ p3)) ∨ (p2 → ((p2 ∨ p2) ∨ p3)))))) := by
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
theorem thm_5_vars_67299563366143120780523620543 : ((p1 → (((False ∨ (p5 ∨ ((p3 ∧ p4) ∨ ((p5 ∧ (p5 ∨ True)) → (p2 ∧ False))))) ∨ ((p2 ∨ (p5 ∨ True)) ∧ (p2 → False))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760396615696891679717548800722 : (((p2 ∧ ((p5 → True) → (p4 ∨ (((False → p3) → (p4 → True)) ∧ (((((p3 ∨ True) → p2) ∨ True) → (p5 ∧ (p5 ∧ p1))) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50223917119260023921491275442 : ((((p3 ∧ ((False ∧ ((p4 ∨ p3) ∧ (True → p2))) ∧ (True ∨ ((p2 → (p2 ∨ True)) ∨ p5)))) ∨ p1) ∨ (True ∨ ((p1 ∨ False) → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753581992249190150558715092988 : (((False ∧ (((((((p2 ∧ p2) ∧ (((False ∨ p3) ∨ False) → p1)) → False) ∨ True) → p2) ∧ p5) ∧ (((p1 → True) ∨ p1) ∧ (False ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65635027733936316490808902103 : ((p4 ∨ (((((False → (False ∨ (p4 ∨ p2))) ∨ ((p5 ∧ (p2 ∧ False)) ∨ p2)) → ((p2 ∨ True) ∨ p4)) ∧ (p5 ∨ (True → False))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225296963254038430062422471229 : (((False ∨ p1) ∧ True) ∨ (((((p4 → (((p2 ∧ (p4 → ((p5 ∧ True) ∨ (p1 ∨ p3)))) ∨ False) ∧ p3)) → p3) ∨ (False → p4)) → False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → (((p2 ∧ (p4 → ((p5 ∧ True) ∨ (p1 ∨ p3)))) ∨ False) ∧ p3)) → p3) ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140747254566672776876729711652 : (((((p3 → ((False ∧ p2) ∨ p5)) ∧ p2) ∨ ((p4 ∧ False) → (False ∧ False))) → (((False ∨ True) ∧ False) ∧ (p4 ∧ p3))) → (p3 ∧ (p4 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → ((False ∧ p2) ∨ p5)) ∧ p2) ∨ ((p4 ∧ False) → (False ∧ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (((p3 → ((False ∧ p2) ∨ p5)) ∧ p2) ∨ ((p4 ∧ False) → (False ∧ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h12.left
    let h16 := h12.right
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h11
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111131713724598948034078142934 : ((((p1 → (((p5 ∨ p5) ∨ False) ∧ (p4 → False))) ∨ ((p2 → (((p4 → p5) → p4) → (p1 ∧ True))) ∧ (p5 ∧ p2))) ∧ True) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646883394093686684741937018931 : ((((p2 → (p2 ∧ ((p4 → ((False ∨ p1) ∧ ((p1 → p1) ∧ (True ∧ (((p2 ∨ p3) → p3) ∧ (p4 ∧ (p3 ∧ p5))))))) ∧ False))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246028636192986991881583099452 : ((p4 ∧ False) ∨ ((((p4 ∨ True) ∨ p2) ∧ (((p3 ∧ (p5 ∧ (((p5 ∨ True) ∧ p1) → p2))) → p2) ∨ p3)) ∨ ((p5 → True) ∧ (False ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160156658048860578562889061303 : ((((((p4 ∨ ((p5 ∧ p1) → p1)) ∨ p3) ∧ p1) ∧ (True → (True ∨ (p1 → True)))) ∧ (p3 ∧ p3)) → (((False ∨ False) ∧ (p3 ∧ p4)) ∨ p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111422609362632173147209627008 : (((p3 ∨ (p1 → ((p5 → True) ∧ (((p2 → p5) → p4) ∧ (((((False → p4) → p2) ∨ False) ∨ p1) ∨ (True → p3)))))) ∧ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64628731898969754398547795298 : ((p1 ∨ (p1 ∧ (p5 ∧ ((p1 ∨ ((((p1 ∧ True) ∨ p2) → p2) ∨ (((p4 → p2) ∧ True) → (p5 ∧ (False ∧ (False ∨ p1)))))) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136363358609824761387302022355 : (((((p2 ∧ False) ∧ p3) ∨ p1) ∨ (p5 → (p4 ∨ ((p2 ∧ (((False ∨ (p4 ∨ p2)) ∧ p4) ∨ (p1 ∨ p4))) → p5)))) ∨ (p4 ∧ (p3 ∧ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65349894913379392927721331641 : ((p3 ∨ ((False → (((p2 ∧ ((p2 → p1) ∨ p3)) ∧ (p5 ∧ (False ∨ p5))) ∨ (p2 → p1))) → (((p5 ∨ p1) ∧ (True → True)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_935297637575768444023884536545 : (((((p2 ∧ ((False ∧ (True → True)) → False)) → p2) → ((((p1 ∧ p2) → (p4 ∧ (p1 → (p2 ∧ p2)))) ∨ (p5 → p4)) ∧ (p2 ∧ True))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ ((False ∧ (True → True)) → False)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131200414545159324368023710794 : (((False ∨ ((p1 → (p5 ∨ (p5 → p2))) ∧ p5)) → ((((False → ((True ∨ p1) → p2)) → False) ∧ (p4 ∨ True)) → False)) ∧ ((p4 → True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : (False → ((True ∨ p1) → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h11
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h10
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h21 : (False → ((True ∨ p1) → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- Implications on the right can always be decomposed.
        intro h23
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h22
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h22
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h26 := h3 h21
      -- False on the left can always be used.
      apply False.elim h26
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305793785010662081182680738302 : (p1 ∨ ((((p4 ∨ (p5 ∨ (True ∨ p4))) ∨ False) ∨ p3) → ((p5 ∨ ((p4 ∧ (True ∧ p1)) ∧ ((p1 → p1) ∨ p1))) → ((False ∨ p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h9 =>
            -- Disjunctions on the left can always be decomposed.
            cases h9
            case inl h10 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h11 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h25
            case inl h26 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h26
            case inr h27 =>
              -- Disjunctions on the left can always be decomposed.
              cases h27
              case inl h28 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h20
              case inr h29 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h20
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h36
            case inl h37 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h37
            case inr h38 =>
              -- Disjunctions on the left can always be decomposed.
              cases h38
              case inl h39 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h32
              case inr h40 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h32
        case inr h41 =>
          -- False on the left can always be used.
          apply False.elim h41
      case inr h42 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136175852733303836065483013164 : (((((p4 ∨ p5) ∧ (p5 ∨ p5)) ∨ p5) ∧ ((((True → (True ∧ p4)) ∧ True) → p5) ∨ (((p2 ∧ p2) ∧ p1) → p2))) ∨ ((p2 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115561265598051828979801071920 : (((((p1 ∨ (p1 ∧ p5)) → False) ∨ p4) ∧ ((False ∨ ((p4 → p3) ∨ ((((p2 → False) ∨ True) → p1) → (True → True)))) → p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620914254773841185220726067594 : (((((p3 ∨ p2) → ((((((p4 ∧ p3) ∧ p2) ∨ True) ∨ p4) ∧ (p3 ∧ ((p4 ∨ p1) ∧ (False ∧ (False ∧ p5))))) ∧ (False → p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_186925887346354371389394890095 : (((p3 ∧ (p2 ∧ p5)) ∧ ((p2 ∨ p3) ∨ (True → (p5 → p2)))) → ((p3 → ((p1 ∨ (p4 ∧ False)) ∨ (True ∨ p2))) ∨ (p4 → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158573292745880002079752153335 : ((True ∧ ((p4 → ((False → p3) → (False ∨ False))) ∨ (True → (((p2 ∨ p5) ∧ p1) → (p5 ∨ True))))) ∨ ((p5 → (False ∧ (p3 → True))) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42084420532485681856094280315 : ((((p3 → p2) ∨ ((((p2 → p5) ∧ (p4 ∨ True)) ∧ (p1 ∨ ((p3 → p2) ∧ ((True ∧ p1) → (p3 → False))))) → (p3 → False))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137962015222521186374995502917 : ((p5 ∨ (((p2 ∧ ((p3 → True) ∨ p4)) → (p5 ∨ ((p4 ∨ (p3 ∧ (p2 ∧ True))) ∧ (p2 → True)))) ∨ (p4 → p5))) ∨ ((p3 ∧ False) → p3)) := by
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
theorem thm_5_vars_115869463571738070673280312716 : (((p5 → (p1 → (p5 → p1))) ∧ ((p4 ∨ (p1 → ((True → ((((True ∨ p2) ∧ p1) → p4) ∨ (p5 ∨ p3))) → True))) → p1)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111968841384825014242364214422 : (((((p5 → (p4 ∨ True)) ∨ (False ∨ False)) ∧ ((p2 ∨ (p1 → (p5 → ((p3 → (True ∨ True)) ∨ p3)))) → (p5 ∧ p5))) ∨ True) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142510203875059122219189273607 : ((True ∨ (((((p5 ∧ ((((True → False) ∨ p1) ∧ False) ∧ (p4 ∧ p5))) → (True ∨ (p4 ∧ p1))) ∧ p5) ∨ p1) ∨ p3)) → ((p5 → p3) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314690806397805424269811015066 : (p3 ∨ (((p1 ∨ p3) ∧ ((p4 ∨ ((True → p1) ∨ (p1 ∨ (p2 ∧ (False ∧ p2))))) → False)) → (((p5 ∨ p3) ∧ ((p2 ∨ p4) ∨ p1)) → p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h1.left
        let h9 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h11 : (p4 ∨ ((True → p1) ∨ (p1 ∨ (p2 ∧ (False ∧ p2))))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h12 := h9 h11
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h18 : (p4 ∨ ((True → p1) ∨ (p1 ∨ (p2 ∧ (False ∧ p2))))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h19 := h16 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h25 : (p4 ∨ ((True → p1) ∨ (p1 ∨ (p2 ∧ (False ∧ p2))))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h26 := h23 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h1.left
        let h32 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h34 =>
          -- One of the premise coincides with the conclusion.
          exact h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h1.left
        let h37 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h38 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h39 =>
          -- One of the premise coincides with the conclusion.
          exact h39
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h1.left
      let h42 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h43 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h44 =>
        -- One of the premise coincides with the conclusion.
        exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117484779375782054737904165423 : ((p1 ∧ (p4 ∨ (p3 ∨ (False ∧ (p1 ∨ ((p4 → (False ∧ p4)) ∧ (p2 ∨ (p3 ∧ (((p4 ∧ (p1 → p3)) → p4) ∨ p3))))))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148274900428192433937258411067 : ((((False ∨ (p3 ∨ ((((p2 ∧ p1) ∨ (False ∨ p5)) ∧ (p1 ∧ True)) ∧ p1))) ∧ p4) → ((p1 → False) ∧ p2)) ∨ (p5 → ((False → p2) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735722589150344840768367738360 : ((((p5 ∨ p3) ∧ ((((p3 → (True ∨ p1)) → (p5 → (False ∧ p5))) ∨ (p5 ∨ p2)) ∧ ((p1 → (p3 → ((p2 → False) ∨ p1))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148191195685468879199730032025 : ((((p3 → ((p3 ∧ p3) ∧ p2)) ∧ (p3 ∧ (p5 → (p3 → ((p2 → p4) → p1))))) ∧ (p5 ∧ (p2 ∧ p3))) ∨ (p3 → (p5 ∨ (False → p4)))) := by
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
theorem thm_5_vars_233982067630971814551273209704 : ((p5 ∨ (p5 ∧ p2)) → (p2 → ((((p2 ∨ p5) ∧ False) ∨ ((((p4 ∧ False) ∨ p4) ∧ p1) → (p3 ∧ False))) → (p3 ∨ ((p1 ∨ True) → True))))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145568857228598887930051136456 : (((False ∨ (p3 ∧ p5)) ∨ ((p2 ∨ (((p1 ∧ (p4 ∨ p4)) → ((p3 → (p3 → True)) → p1)) ∧ p2)) → True)) ∧ (((p5 ∧ p3) ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300905772907503652190405923021 : (False ∨ ((((p2 ∨ True) ∨ (p5 → ((p5 ∧ True) ∨ p2))) ∧ (p2 → (False ∧ False))) → ((p1 ∧ (p1 ∧ ((True ∨ False) ∧ p2))) → (p4 ∨ p5)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h14 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h15 := h11 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h18 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h19 := h11 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h22 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h23 := h11 h22
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39436426922336903586844053071 : (((p5 ∧ (((p3 → (((p5 → p5) → ((((p4 ∧ p5) ∨ p3) → (p5 → p3)) ∧ False)) ∨ p3)) → ((p5 ∧ True) ∧ p3)) ∨ p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226932586465716236215638002964 : (((True ∨ p4) → p5) ∨ ((p5 ∨ (p3 ∨ (p4 ∧ ((True ∧ (p2 → ((p2 → p5) → p3))) → (((p1 ∧ p2) → p3) → p2))))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57619554369694433054128813632 : ((((False ∧ p1) ∨ p4) → (((((((p4 → p5) → p3) ∧ (p2 ∧ False)) → (p3 → p3)) ∨ (p1 → ((p3 → True) ∨ p1))) → p1) ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47222860582801591911778271906 : ((((((p3 → ((p1 ∧ p5) → True)) ∧ p2) ∧ p4) ∧ ((True ∧ (False ∧ ((p2 ∧ (False ∨ p4)) → (p2 ∨ p1)))) ∨ p1)) ∨ (p5 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386380055668998218503914042770 : (((((p3 ∨ ((p5 ∧ ((p5 → ((p5 ∨ (p2 ∨ (p5 ∧ False))) ∨ (p1 → (p4 → (False ∨ p5))))) → p5)) ∧ p5)) ∨ (True → p4)) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60397754468718665470387331139 : (((p3 → p5) → (((((((p5 → p2) ∧ ((p4 ∧ (False ∨ p3)) ∨ p4)) ∧ (True ∨ p3)) ∨ True) ∧ True) ∨ True) ∨ (p1 → (p1 ∧ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119853904006378098225380775202 : ((((p5 → ((((p5 ∧ (p3 ∧ (False ∧ ((p3 → p4) ∨ (True ∨ p5))))) ∧ p2) ∨ True) ∧ ((p4 → p3) ∨ p3))) → p5) ∧ p3) → (p5 ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → ((((p5 ∧ (p3 ∧ (False ∧ ((p3 → p4) ∨ (True ∨ p5))))) ∧ p2) ∨ True) ∧ ((p4 → p3) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (p5 → ((((p5 ∧ (p3 ∧ (False ∧ ((p3 → p4) ∨ (True ∨ p5))))) ∧ p2) ∨ True) ∧ ((p4 → p3) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209165901073573080868063649010 : ((p3 ∨ (p2 ∨ ((True → p4) ∨ p4))) → (((p4 ∧ p5) → (True ∨ p4)) ∧ (((p1 ∧ ((p1 ∧ False) → p5)) ∧ False) ∨ ((p3 → True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro



