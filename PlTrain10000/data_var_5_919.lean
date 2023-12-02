variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317684937615074411548160870981 : (p4 ∨ (((False ∨ ((p5 ∨ p2) → (((True → True) ∨ False) ∨ (False ∨ ((p1 ∧ (p5 → ((False ∧ p4) ∧ p4))) → (p3 → p3)))))) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143962745175613987659057845152 : ((((p5 → (p5 → p3)) → ((p3 ∧ False) ∧ (((p4 ∨ False) ∧ (p5 → (p3 ∨ (p1 ∨ p4)))) ∨ False))) ∨ True) ∧ (((p3 ∨ p5) ∧ p3) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181221734570819884600532829294 : ((p2 ∧ (p3 → (((p4 ∧ p4) ∨ False) ∨ (p3 ∧ ((p1 ∧ p2) ∨ True))))) → (p4 ∨ ((((p2 ∨ p2) ∨ (p4 ∨ p3)) → (p3 → p1)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147665520234557724795554949811 : ((((p5 ∨ (p1 ∨ ((((p2 ∧ ((p3 ∧ p2) ∧ False)) → (p4 ∨ p5)) ∧ p1) → True))) ∨ (p3 → p4)) → p2) ∨ ((p4 → True) ∨ (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134900348858850083345201347626 : ((((((True ∧ ((p3 ∨ (True ∧ (p4 → (p1 ∧ p5)))) → p3)) ∨ ((p5 → p2) ∧ p2)) ∨ False) ∧ False) ∧ (p3 ∨ True)) ∨ ((p3 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203749609338140877452044766246 : ((p5 ∨ ((True ∧ True) ∨ (p4 ∨ p2))) ∧ ((True ∧ ((p1 ∨ (((True ∧ p3) ∨ (p5 → p5)) ∧ (p1 → p3))) ∨ (True → (p3 ∨ p4)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668093215011351894487374058099 : ((((True → ((((p3 ∧ p3) ∨ True) ∧ p1) ∧ (False ∧ ((((p3 ∧ True) ∨ (p1 ∨ p1)) ∨ p4) → (False ∨ p5))))) ∧ (p3 ∨ (p5 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158451067407986191763022161696 : (((p5 ∨ p2) ∨ (True ∧ ((p4 ∧ p2) ∧ (p1 → ((p1 ∨ ((p3 ∨ (True ∧ p5)) ∨ p5)) ∧ p4))))) ∨ (True ∧ ((p4 → True) ∨ (p2 ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227689290131567088747066558315 : ((p1 ∧ (True ∧ p2)) ∨ (((((True → True) ∧ False) → True) ∧ (p1 ∧ ((((p5 ∧ p1) ∨ p5) ∧ (p5 ∨ (p1 → p3))) ∧ p4))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667323287534284550541401671257 : (((((p1 ∨ p1) ∨ (((p4 ∧ (((p1 ∨ p1) ∨ (p5 ∧ p1)) ∧ p5)) ∧ p1) ∨ ((p5 ∧ (False ∧ p1)) → p1))) ∧ ((True ∧ p2) → True)) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355620154050907484646150411776 : (p5 → ((p4 ∧ (p5 ∧ (p5 → (p5 ∧ (((p5 ∨ (((True → p1) ∧ True) → p3)) → (p2 ∧ (p5 → (p1 ∨ True)))) → False))))) ∨ (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112577627804884047177241009315 : ((((p3 → ((((True ∧ p4) ∨ (p3 ∨ p2)) ∧ ((True → (p3 ∨ (((p1 → p5) ∧ p4) ∧ p1))) → p1)) → False)) → False) → False) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351553418500504091324553755651 : (p4 → ((((p3 ∨ (((p3 ∨ False) ∨ p5) → ((p3 ∨ ((False → p5) → p3)) → p4))) → False) ∧ p1) → (p5 ∧ (False ∧ ((True ∨ True) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ (((p3 ∨ False) ∨ p5) → ((p3 ∨ ((False → p5) → p3)) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h18 := h3 h5
  -- False on the left can always be used.
  apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h21 : (p3 ∨ (((p3 ∨ False) ∨ p5) → ((p3 ∨ ((False → p5) → p3)) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
      case inr h33 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h34 := h19 h21
  -- False on the left can always be used.
  apply False.elim h34
  -- Implications on the right can always be decomposed.
  intro h35
  -- Disjunctions on the left can always be decomposed.
  cases h35
  case inl h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h2.left
    let h38 := h2.right
    -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
    have h39 : (p3 ∨ (((p3 ∨ False) ∨ p5) → ((p3 ∨ ((False → p5) → p3)) → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h40
      -- Implications on the right can always be decomposed.
      intro h41
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h45 =>
            -- False on the left can always be used.
            apply False.elim h45
        case inr h46 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h48 =>
          -- Disjunctions on the left can always be decomposed.
          cases h48
          case inl h49 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h50 =>
            -- False on the left can always be used.
            apply False.elim h50
        case inr h51 =>
          -- One of the premise coincides with the conclusion.
          exact h1
    -- We have shown the premise of h37, we can now drive its conclusion.
    let h52 := h37 h39
    -- False on the left can always be used.
    apply False.elim h52
  case inr h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h2.left
    let h55 := h2.right
    -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
    have h56 : (p3 ∨ (((p3 ∨ False) ∨ p5) → ((p3 ∨ ((False → p5) → p3)) → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h57
      -- Implications on the right can always be decomposed.
      intro h58
      -- Disjunctions on the left can always be decomposed.
      cases h58
      case inl h59 =>
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h60 =>
          -- Disjunctions on the left can always be decomposed.
          cases h60
          case inl h61 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h62 =>
            -- False on the left can always be used.
            apply False.elim h62
        case inr h63 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h64 =>
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h65 =>
          -- Disjunctions on the left can always be decomposed.
          cases h65
          case inl h66 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h67 =>
            -- False on the left can always be used.
            apply False.elim h67
        case inr h68 =>
          -- One of the premise coincides with the conclusion.
          exact h1
    -- We have shown the premise of h54, we can now drive its conclusion.
    let h69 := h54 h56
    -- False on the left can always be used.
    apply False.elim h69



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54212683521099713711582865972 : ((((p2 → (((p5 ∧ True) → p1) ∨ p5)) ∨ p3) ∧ (((p4 ∨ (p4 ∨ False)) ∨ ((p1 → p3) ∨ (p2 ∨ p1))) ∨ (p4 ∨ (p1 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225046468563660946295799071065 : (((False ∧ p5) ∧ p2) ∨ ((((True → ((((p4 ∨ (p1 → p1)) → (True → (p1 ∧ True))) ∧ p1) ∨ p2)) → p2) ∨ p5) ∨ (p5 → (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809907771506399054835835162373 : (((p5 → ((((p1 → False) → ((p2 ∧ False) ∨ (True → ((p1 ∨ (p5 ∧ (p3 ∧ p5))) ∨ (p2 ∨ p3))))) → p3) ∧ (False → (p2 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47131026488640777851791238113 : ((((p2 ∧ (((p2 ∨ True) ∨ p4) ∨ (((p4 ∧ True) ∨ (True → (p1 ∨ True))) ∨ (True → p5)))) → (p1 ∧ (p4 → p1))) ∨ (p5 → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249642308805566685434981458754 : ((p5 ∨ p3) ∨ (True → (p3 → (p5 ∨ ((((p3 → p3) ∧ p5) → (((p4 ∧ p2) ∨ False) ∨ (p5 ∨ (p5 → ((True ∧ p5) → p5))))) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178473548307393745648375594286 : (((((p5 → (False ∨ (True ∧ p1))) ∨ False) ∨ p2) ∨ (p3 ∧ (p3 → p1))) ∨ ((p4 → ((((p1 → p2) → (p2 → False)) → False) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137200410047423446098343572758 : ((False ∧ (p5 ∧ ((p3 → p2) → ((p4 ∨ (p2 → False)) ∨ ((p3 ∧ p5) ∧ ((True ∨ (p5 ∨ (p1 ∨ p3))) ∨ p3)))))) ∨ ((False ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751868256600964690535506549195 : (((True ∧ (p2 ∨ (((True → ((p3 → p3) ∨ p5)) ∧ (p5 → (p1 → ((p5 ∧ (False ∧ p3)) ∧ (((p1 ∨ p4) ∧ True) → p4))))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609771169708629019235666640489 : (((((p5 ∨ ((p1 ∧ (((p4 → p5) ∧ ((True ∨ p5) ∧ ((p4 ∧ p3) ∨ (((p5 ∧ p2) → p1) ∨ p4)))) ∨ p1)) ∨ True)) ∨ p2) ∨ p5) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_808954148685715824220857555701 : (((p5 → (((((p4 → p4) ∧ (p3 ∨ (((p3 ∨ p3) ∧ True) ∨ False))) ∨ ((p1 ∨ p2) ∧ p5)) ∨ ((p4 ∨ (p5 ∨ p5)) → False)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83927614205956721007601975201 : (((p1 ∨ ((((False ∧ p1) ∨ p1) → (p4 ∨ p3)) → ((False → (True → p1)) ∨ (p2 ∧ p5)))) → ((False ∨ ((p3 → p2) → p4)) ∧ False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((((False ∧ p1) ∨ p1) → (p4 ∨ p3)) → ((False → (True → p1)) ∨ (p2 ∧ p5)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187152355814639888466648561003 : (((p1 → p2) ∨ (p2 → (((True → (p3 ∨ True)) ∧ p4) ∨ p2))) → (((p1 ∧ (p1 → (False ∨ False))) ∧ ((False ∧ (p4 → p3)) → True)) → p2)) := by
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
  cases h1
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747624673007629879962167560207 : ((((True → p4) → (p1 ∨ ((((p5 → (True → p2)) ∨ (p3 ∧ False)) ∨ ((p3 → (True ∧ (p5 ∧ ((p5 ∨ p1) ∨ p3)))) ∧ p4)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9730357868453791769995067672 : ((((p5 → p2) ∨ ((((((False → ((((p3 → p5) → p1) → True) ∧ p3)) ∨ p5) ∧ ((p2 ∨ p5) ∨ p4)) → False) ∨ p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157566940758773484089376821265 : ((((p2 ∧ (((True ∨ True) ∧ p1) → True)) → (p5 → (((p1 ∧ p1) ∨ p5) → False))) → (True ∧ p4)) ∨ (True ∧ (True ∨ ((True → p3) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777502694211333641685480120159 : (((p1 ∨ ((p3 ∧ (p5 → ((((p3 ∨ p5) ∧ (p5 ∧ p5)) ∧ (True → True)) → p2))) ∨ (p4 ∨ (((True ∨ (p5 → True)) ∨ p5) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68633800132329058414445394052 : ((p4 → ((p2 → ((True ∨ (((((p3 → False) ∧ p4) ∧ (p3 ∧ p1)) → (p3 ∨ ((p3 ∧ False) ∧ (p1 ∧ False)))) ∧ p4)) → False)) ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118895605097614928800908459761 : ((True → (False ∨ (p1 → ((((((False → False) ∧ False) ∨ (p3 → p4)) → (True → (p2 → (p5 ∨ True)))) → p4) → (p1 ∧ False))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313364664976820942327933170962 : (p3 ∨ ((p4 → (((((p2 ∨ (p1 ∨ (((True ∨ p3) → p2) ∨ p5))) ∧ p3) ∧ (p1 ∧ (((False ∧ False) ∨ p3) → False))) ∧ p1) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678439670602702448881411701024 : ((((((p2 → p1) → (p5 ∨ False)) ∨ (p5 ∨ (((p4 ∨ p1) ∧ (p5 → True)) → ((p4 → True) → False)))) ∨ ((p5 → True) ∨ (p2 ∨ p5))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468071006881776626574061814684 : ((((p4 ∧ ((p1 → (p5 → ((p4 ∨ (p5 ∧ p5)) → False))) ∧ (p4 ∧ p4))) ∨ ((p3 → (False → p2)) ∨ (((False ∨ p2) ∧ p2) ∧ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42347922851255386975447306448 : (((p3 ∧ (((False ∧ (p2 ∨ ((p1 ∨ p1) ∧ p5))) ∨ (False → False)) ∨ ((False ∧ (True ∧ True)) → ((p3 ∧ p3) ∨ (p1 → p3))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302814119381032801044507368603 : (False ∨ (p5 ∨ ((((True ∨ False) → (False ∨ False)) ∧ (((p1 → ((((True ∧ p1) ∨ p5) → p3) → p3)) ∨ p1) ∨ (p4 ∨ p2))) → (True ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      have h6 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h22
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147111082404232826389518606647 : ((((False ∨ p2) ∧ (p4 ∧ (p3 ∧ ((p3 ∧ (p1 ∨ p3)) ∧ ((False ∧ p4) ∧ (True ∧ (False ∨ p3))))))) ∧ p2) ∨ (p4 → (p1 ∨ (p5 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183971666392661877587866615563 : (((p4 → (((p3 ∨ (p2 → False)) ∧ (p5 → p5)) ∧ False)) ∧ True) ∨ (((p4 ∧ False) ∧ p5) ∨ (p3 → ((p4 ∧ (p1 → (p1 ∨ True))) → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326842655718425767537736423612 : (True → (((((p1 ∨ True) → (False ∧ True)) → (p3 ∧ (((p4 ∨ (p1 → (p2 ∧ p2))) ∨ (p1 ∧ (p3 ∨ (True ∨ p5)))) → p4))) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641830816724378933902676544517 : (((((True → p4) → (p3 ∧ (p2 ∧ (False → (((p4 → ((True ∨ p1) ∧ p3)) → p5) ∧ (p4 ∨ (p3 ∧ ((p5 ∨ True) → p5)))))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37385606281570697826126408741 : (((((((((p2 ∧ (p4 ∨ p5)) → False) ∧ True) → (p2 ∧ p5)) → (((p5 ∨ True) ∨ (p4 ∨ (False ∨ p1))) ∨ p4)) → p4) ∨ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743622282002569529339237622367 : ((((True ∧ p1) → ((True ∧ ((p3 → p5) ∨ (((p1 ∧ p5) → False) ∨ (((p5 → (p2 → (False ∨ (p3 → p4)))) → p5) ∨ p1)))) ∨ p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347970031536357302135846787578 : (p3 → ((p1 → True) ∧ ((((p2 → (p1 → (p2 ∨ False))) ∧ False) ∨ (((((p4 ∧ p3) ∨ p2) ∨ (p4 ∨ p5)) ∨ (p2 ∨ p5)) ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118345218822668572377687549369 : ((p2 ∨ ((True → ((((True → (p4 → p4)) ∧ p4) ∨ (p4 ∧ (((p1 ∧ (p3 ∨ p3)) ∨ p3) ∨ True))) ∧ (False ∧ p4))) ∨ True)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115996483320998524828756674166 : ((((True ∨ (p5 ∨ True)) → True) → ((((True → ((((False ∨ p5) → (False → p1)) ∨ p2) ∨ p1)) ∧ p2) ∨ (p2 → p3)) ∧ True)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308080569137099241035842792398 : (p2 ∨ (((p1 → ((p1 → (p4 ∨ p5)) → (p3 ∧ ((False ∧ (p2 ∧ ((False ∨ p2) ∧ p1))) ∨ p4)))) ∨ (p3 → (p5 ∨ (p3 ∨ p5)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397871565532861280285315445555 : ((((p3 ∨ (p2 ∧ (((False ∨ True) → (p5 ∧ ((False ∨ ((p5 ∨ ((False ∨ (p4 ∧ False)) → True)) ∧ p5)) ∨ False))) → (p1 ∧ p2)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_173324557747839999361102489294 : ((p2 → (((p1 → (((p3 ∧ p5) ∧ (p2 → p3)) ∨ False)) ∧ p4) ∨ (p4 ∧ p2))) ∨ (p3 ∨ (p5 → (p3 → (((p1 → p5) ∧ p5) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720611472787150855241529075080 : ((((((p4 → True) ∧ p3) → p4) → (p5 ∨ ((((p4 → ((p4 ∧ p2) → ((p1 → p1) → p1))) → False) ∨ p4) ∨ (True → (p5 → p5))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338975763010352490089964236181 : (p1 → ((p3 → p4) → (((True ∨ p2) → p4) → (p1 → ((p4 → p2) → (p4 → (p5 ∨ ((((True ∨ p2) ∨ False) → (p3 ∧ p4)) ∨ p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788591013621524744259623307236 : (((p5 ∨ (((((False → (((True → (p2 → True)) ∧ p3) ∨ (p3 ∨ True))) → ((False ∨ (p5 → (p2 ∧ p4))) ∨ True)) → p4) ∨ p5) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201254757138644654818600360091 : ((p3 → ((p3 ∨ ((p3 ∨ p3) ∧ p3)) → p3)) → ((p5 → (p2 ∨ p2)) ∨ (((p4 ∧ (True ∨ p4)) ∨ ((p3 → p4) → p3)) → (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303768584762535478207071092101 : (p1 ∨ ((((p1 ∨ (True ∨ p1)) → (p4 ∨ ((p1 ∧ ((((True ∨ p2) ∧ p1) ∧ p3) → p2)) ∨ ((p3 → p5) ∨ (p1 ∨ p1))))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768832286146262814181396451901 : (((p5 ∧ (((p5 → (p2 ∧ p2)) ∨ (p2 ∨ p4)) ∨ ((p3 ∧ p5) ∧ (p2 ∧ ((False → ((p4 → (False ∧ p3)) ∨ True)) ∧ (False ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231033296996863619572176076764 : (((True ∨ True) ∨ False) → ((((p1 ∨ (False ∧ p2)) ∧ (False ∨ True)) ∨ (False ∨ (p5 → (p2 → (p4 → ((False ∧ (p2 ∨ True)) ∨ True)))))) ∨ p3)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647527624422460432107196972169 : ((((p5 → ((((p4 → p5) ∨ ((p5 ∧ (((p5 ∨ (p4 ∧ ((p3 ∨ p4) ∧ p2))) → False) → (p4 ∨ True))) ∨ p4)) ∧ p4) ∨ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132890253290754032831892123398 : ((p3 ∨ (((p3 → p4) → p5) → ((p5 → (((p2 ∧ (p5 → p3)) ∧ (False → (p3 → p2))) ∨ True)) ∨ (p4 ∧ False)))) ∧ ((p2 ∧ p3) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623904038725211402453747549034 : ((((p1 ∨ (p3 → (((((False → p2) ∨ ((p3 ∧ p4) ∧ ((p5 ∧ ((p3 ∨ True) ∨ True)) ∨ False))) ∧ (False → False)) → p5) ∨ p3))) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309384785232713648341995132924 : (p2 ∨ ((p1 ∧ ((False ∨ p4) → ((((((p3 ∨ ((p4 → (False ∧ p2)) ∨ True)) ∧ p3) ∧ True) → (p3 → False)) → False) ∨ p2))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657915111064013076865771003341 : ((((p1 ∧ (((p4 → (((True ∧ p4) → (True → p1)) ∨ (True ∨ (True → False)))) → p1) ∨ ((True ∨ p3) → (p4 ∨ p1)))) ∨ (p1 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787222648503464800174158175418 : (((p4 ∨ (False ∧ ((((p5 ∨ ((True → p1) ∨ (p1 → (False ∧ (p5 → p4))))) ∧ p1) ∨ ((((True ∨ p3) ∨ p4) → p1) ∧ p1)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192149715788303413990998881481 : ((((((p4 → p4) → (p3 ∧ p2)) ∧ p4) ∧ p2) ∧ p5) → (((((False → False) ∧ (p3 → p2)) ∧ ((p1 ∨ p2) → False)) → (p1 ∧ p2)) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324087269491129266167662622429 : (p5 ∨ (((p2 → p1) ∨ (((p4 ∧ ((p1 → p5) ∧ True)) ∨ False) ∨ p3)) ∨ (False → ((p4 → (p2 ∧ p2)) ∨ ((False → (True → p3)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187623866794357428859386512185 : ((p5 ∨ (((((p5 ∧ p3) ∧ p4) → (p1 → True)) ∨ p5) ∧ p3)) → (((p2 ∧ ((p5 ∨ p1) → ((p1 ∨ p1) ∧ p5))) ∧ (True → False)) → p5)) := by
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
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77044725757968721815059833524 : ((((p2 ∧ ((p2 ∨ p5) → (True ∧ False))) → (p5 ∨ ((((True → p1) ∨ True) ∧ (((p5 → (p2 ∨ p3)) ∨ p1) → p4)) ∧ p3))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ ((p2 ∨ p5) → (True ∧ False))) → (p5 ∨ ((((True → p1) ∨ True) ∧ (((p5 → (p2 ∨ p3)) ∨ p1) → p4)) ∧ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p2 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709501549517647613429153002454 : ((((p4 ∧ (p2 → ((p1 ∧ p2) → (p1 ∧ p1)))) → ((p4 → ((False → p1) ∧ (p2 ∧ p5))) ∨ (((p2 ∧ p2) → p4) ∨ (p3 → p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199573924413414076516256836149 : ((((False ∧ (p4 → (p3 ∨ True))) ∨ True) → p5) → (((p3 ∧ ((True ∨ (((True → p3) ∨ p3) → p2)) → p5)) ∧ p2) ∨ ((True → p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (p4 → (p3 ∨ True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311150680635648871438152425695 : (p2 ∨ ((p2 ∧ p1) → (((p4 ∧ p3) ∨ (p4 ∨ False)) ∨ (p1 ∨ ((((True → (p2 ∧ p2)) → p5) ∧ False) ∨ (p1 → (False → (p4 ∧ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51636531440558769731265197616 : (((((p1 → (p3 ∧ ((p3 ∧ p1) ∧ (((p5 ∨ False) → p5) ∨ p2)))) → p4) ∨ False) ∧ ((True ∧ p2) → (((False ∧ p1) ∧ False) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656174388756907363581306961963 : ((((((p1 → (p1 ∧ p1)) → ((p1 ∨ (False ∨ ((True → False) → False))) ∧ p4)) ∨ (p2 → (p1 ∨ ((True ∧ True) ∧ True)))) ∨ (p3 → p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56403035278373936511992685213 : ((((p1 ∨ (p3 ∧ p1)) → False) → ((p1 ∨ p4) ∨ ((p5 ∧ (((((p3 ∨ (p5 ∧ p5)) ∨ False) ∨ (p2 ∧ p5)) ∧ False) ∨ False)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760433228853503101469928611578 : (((p2 ∧ (True ∧ (p1 ∨ ((p1 ∨ p3) ∧ ((p3 ∧ (((p4 ∧ p4) ∨ p4) → p2)) ∧ ((p3 ∨ True) ∨ (True ∧ ((p2 → True) ∧ p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314069607342016383171992554180 : (p3 ∨ (((p5 → (((p3 ∧ True) ∧ ((((p2 ∧ p4) ∨ p3) ∨ (((p2 → p4) → p3) → p5)) → p3)) ∨ (p2 → p5))) → False) → (p5 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((p3 ∧ True) ∧ ((((p2 ∧ p4) ∨ p3) ∨ (((p2 → p4) → p3) → p5)) → p3)) ∨ (p2 → p5))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p5 → (((p3 ∧ True) ∧ ((((p2 ∧ p4) ∨ p3) ∨ (((p2 → p4) → p3) → p5)) → p3)) ∨ (p2 → p5))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343409199187621885620641065181 : (p2 → ((p5 ∧ True) ∨ ((p4 ∧ ((p4 → True) ∧ p1)) → (p3 ∨ (p1 ∧ ((p3 ∧ ((p5 → p4) ∧ (p4 ∧ (p4 ∧ (p5 ∧ False))))) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165089620520629209249112384873 : (((p2 ∨ (p3 ∧ (((p3 → (False → True)) ∨ p5) ∨ ((p3 → True) → (p4 ∧ True))))) → p2) ∨ (True ∨ (((p1 ∧ p5) → (p4 ∨ p1)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113819875427161988201383894015 : (((p3 ∧ (True → ((((p4 ∨ p3) ∧ p5) ∧ True) ∧ (p4 ∧ (((p2 ∨ p4) ∧ p5) → (p4 ∨ (p3 → p2))))))) → (p1 ∨ p4)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213089564462200739417572174196 : ((((p4 ∧ p5) ∧ p4) ∧ p2) ∨ ((p5 ∧ (((p2 → p4) ∧ ((p2 ∧ p3) ∧ p2)) ∧ (p5 ∨ (p3 ∨ (((p5 ∧ False) ∧ p5) ∧ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226625594636821585519902259812 : (((True ∧ True) → p1) ∨ ((p5 ∧ (((((True ∧ p1) ∧ ((p5 → True) ∨ False)) ∧ p3) ∧ (p2 ∨ (p2 ∧ (p3 ∧ (False → False))))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688365836517607940495579569794 : ((((False ∧ ((((False ∧ p5) ∧ p3) ∧ (True ∧ (False → (p3 → (p3 ∧ True))))) ∨ p4)) ∧ (((True → (p2 ∨ (p1 → p1))) → p4) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41263283986924826173439597314 : (((((False ∨ p1) → ((p5 ∨ ((((True → (p4 ∨ True)) ∧ p2) → p4) → (False ∨ p5))) ∧ True)) ∨ ((True ∧ p2) ∨ (p3 ∨ True))) ∨ p1) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309611831593053579837150339248 : (p2 ∨ (((((True ∨ p4) ∧ (p2 ∨ ((p3 ∨ (((p3 → p2) ∨ p3) ∧ ((False ∨ p3) → p1))) ∨ False))) → False) → p3) ∨ ((p3 → True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184965305119676249163561281041 : (((p1 ∧ (True ∨ p4)) → (p4 ∧ ((p4 ∨ p3) ∨ (True ∨ True)))) ∨ (((p5 ∧ p1) ∨ p5) ∨ ((p5 → (((p5 ∨ p3) ∨ True) ∨ p2)) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112824878636137475859165409842 : ((((((p2 ∨ p2) ∨ False) ∨ p3) ∨ ((p3 ∧ (p4 ∨ True)) ∨ (False ∨ ((((p1 → p1) → (p5 ∧ p5)) ∨ p3) ∨ p4)))) → False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753729477962835868536504586971 : (((False ∧ (((((False ∧ p4) ∨ True) ∨ (p5 ∧ (p3 → (p5 → p4)))) → True) ∧ (False ∨ ((((True ∨ p2) → p4) ∨ p5) ∨ (True → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354105387069832001122419243485 : (p4 → (p5 → ((((p5 ∧ (p2 ∨ p2)) ∨ False) ∧ False) ∨ (((False ∧ p1) → False) → (p5 → ((p4 → p3) ∨ (((False → p5) ∧ p1) → p1))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40264409166843887799984446166 : ((((p4 ∨ ((p2 ∧ ((((p3 ∨ p5) ∨ p2) → p5) → ((((p5 → False) ∧ (p3 → True)) ∧ (p3 → p5)) ∨ False))) ∧ p3)) ∧ p1) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52141555803518117012806008268 : ((((p5 ∨ (((p5 ∧ ((p5 → p4) → p4)) ∧ (p5 ∧ p4)) ∨ p1)) ∨ (p5 ∨ p4)) → (((p3 ∨ p5) ∨ (True ∨ (p2 → p1))) ∨ p4)) ∨ p2) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h7.left
        let h11 := h7.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191913418064954370095067096304 : ((p5 ∨ (p5 ∧ (p3 ∨ ((p2 ∧ p1) → (p4 ∨ p4))))) ∨ (((p4 ∧ False) ∧ ((((p1 → p2) ∨ ((True ∨ p1) ∨ False)) → True) ∧ p4)) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181586857971190347047178491447 : ((p1 → ((p2 ∨ (((True → False) ∧ p2) ∨ p1)) ∨ ((p3 ∧ p1) ∨ p3))) → (p3 ∨ (p1 ∨ ((p1 ∧ p1) ∨ (p3 ∨ ((p5 ∧ False) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_211451405248605815713236473657 : (((True ∧ p1) → (p2 ∨ True)) ∧ ((False ∧ ((((p5 ∧ False) ∨ p4) ∨ (p2 → (True ∧ ((p2 ∨ True) → (p1 ∨ p2))))) ∧ (True ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22460281834103420257716514756 : (((True → ((p4 ∧ (True ∨ p4)) ∧ (p3 ∨ p3))) → (((p3 → (((p4 ∨ p2) → True) ∨ p2)) → p5) ∨ (p1 → ((True ∧ p3) ∧ p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172369525087303096013341689732 : (((p3 ∧ (((p4 → True) → p3) ∧ p1)) ∨ (p2 → ((False → (p5 ∨ p2)) ∧ p5))) ∨ (p4 ∨ ((True ∨ True) ∨ (((False ∧ p1) ∧ p1) ∧ True)))) := by
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
theorem thm_5_vars_149564965038867549321019618030 : ((p2 ∧ ((p5 → p5) → (((False ∨ ((p2 ∨ (p5 → p4)) ∧ ((False → (p3 → p1)) ∧ True))) → p1) → p1))) ∨ (p1 → ((p3 ∧ True) → p1))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134315421839666696889179993595 : (((False ∧ ((p3 → False) ∨ (p4 ∧ (p1 ∨ (((p3 ∨ (((p1 ∧ (p2 → False)) ∧ True) → p1)) ∨ p1) ∨ p5))))) ∨ True) ∨ (False ∨ (p3 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138346619831507327188391574259 : ((p4 → ((((p4 → (p3 → (True ∧ (p2 ∧ p3)))) ∧ True) ∨ (p3 ∨ ((p4 → (True ∨ p3)) → (False ∨ p1)))) ∨ False)) ∨ ((False ∧ True) → p1)) := by
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
theorem thm_5_vars_89156114487580200998936883301 : ((((True ∨ p5) → False) ∧ (((False → p1) ∨ (p3 ∨ ((p1 ∧ p3) ∧ (p5 → p2)))) → (False → ((p3 ∨ p2) ∨ (p1 ∨ (True ∧ p1)))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655348010030278640551739393130 : ((((((True → (p3 ∧ ((((p4 ∧ ((p5 ∨ p1) → p3)) → (True ∨ p3)) → (False ∧ p1)) ∧ p1))) ∧ p1) ∨ (p3 → p1)) ∨ (False ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63985390444653694195781308812 : ((False ∨ (((p3 ∨ p5) ∧ (((True → ((p3 ∧ p1) ∧ True)) ∧ p1) ∧ ((((p1 ∨ p1) ∨ ((False → p3) ∨ False)) ∧ False) ∨ p4))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47161174093047887504271533229 : (((((((p4 ∨ (((p1 ∧ True) → p2) ∧ p2)) → (p2 ∨ p3)) ∨ p5) ∧ p1) ∧ ((p5 → p3) ∧ (p3 → (p2 → p5)))) ∨ (p5 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192502985621102589266416727742 : ((((True ∨ p5) ∧ (p5 ∨ ((p4 ∨ p4) ∨ p5))) ∨ p2) → (False ∨ (True ∨ ((((p5 ∨ p5) → (p5 ∧ p3)) → p5) ∧ ((False ∨ p2) ∧ p2))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



