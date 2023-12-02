variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124511441730032886421320598144 : (((((p3 ∨ p3) ∨ p1) → (True → p1)) ∧ (p3 ∧ (((p5 ∨ (p1 ∧ p2)) → (p2 → True)) ∧ (False → (p1 ∧ (p2 ∧ True)))))) → (p5 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 ∨ p3) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717723628720739696835250785363 : ((((((p2 ∧ True) ∨ False) ∧ p4) ∨ (((p3 → p5) ∧ (p1 ∧ ((p3 → p2) ∧ ((False ∧ (p1 → (p3 ∨ p4))) → (False → p4))))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_207185519404877173302511295274 : (((((True ∨ True) ∨ p4) ∧ p5) ∨ False) → (((False ∧ (p2 ∨ ((((p4 ∨ p2) ∨ True) ∧ False) ∧ p4))) ∧ p5) ∨ ((p4 ∨ p5) ∨ (False → p4)))) := by
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
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622090957395200496540495280955 : ((((p2 ∧ ((((((p1 ∧ p1) → True) ∨ (p2 → p1)) → p3) ∧ ((True → p3) ∨ (True → (p5 → False)))) ∨ (p4 ∧ (p1 ∨ True)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_305671544255468602517183955812 : (p1 ∨ ((((((p3 → (False ∧ p1)) ∨ True) ∧ p2) → p3) → p4) ∨ (((True ∨ p4) ∧ ((((False ∧ p2) ∨ (False ∨ False)) ∨ p2) → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668811186924881573139023523794 : (((((((False ∨ ((p3 → (p2 ∨ p1)) ∨ (p3 → (p4 ∨ p2)))) ∧ p3) ∨ ((p1 ∨ (p4 → p1)) ∧ p1)) ∨ p5) ∨ (p1 → (p1 → True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165763042791462967174490181658 : (((((p1 ∨ p2) ∨ p3) ∧ p5) → (p3 ∧ (((False → (True ∨ p4)) → (p4 ∧ True)) ∧ p3))) ∨ ((False ∧ ((p4 ∨ p2) → p3)) → (p4 ∨ p5))) := by
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
theorem thm_5_vars_171659875172048532305301821819 : (((p2 ∧ (((p2 ∧ (p4 ∧ p1)) ∨ p5) → (((False → p2) → False) ∧ p2))) ∨ True) ∨ ((p5 ∧ p4) ∨ (True ∧ ((p1 ∨ False) → (p5 ∧ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47075079938428233416537693713 : ((((((((((p1 ∨ p3) ∨ (p5 ∧ (p3 ∧ p5))) ∧ (p3 → (p1 → p2))) ∨ p4) → True) ∨ p4) ∧ p2) → (p1 ∨ p3)) ∨ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83973928143054361507359245767 : ((((((p5 ∨ (((False ∧ p5) ∧ (p1 ∨ p3)) ∧ (p5 ∨ p4))) ∨ p2) → False) ∧ p2) ∧ (p3 ∨ ((True → p3) → (p3 → (True → p1))))) → p1) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((p5 ∨ (((False ∧ p5) ∧ (p1 ∨ p3)) ∧ (p5 ∨ p4))) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : ((p5 ∨ (((False ∧ p5) ∧ (p1 ∨ p3)) ∧ (p5 ∨ p4))) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784910756390367771820281261783 : (((p3 ∨ (p2 → (True → ((((((False ∨ p4) → p2) ∧ (p1 ∨ False)) ∧ ((p3 ∨ p5) → (p3 ∨ ((p1 ∧ p2) ∧ p2)))) ∨ p2) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164848709237147689491822402922 : (((p5 ∧ ((((p5 → p5) → p1) → (p2 ∧ False)) ∧ (False ∨ ((p4 ∧ True) → p3)))) ∨ True) ∨ (((False ∧ False) ∧ p5) ∧ (p5 ∨ (False ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610152154272052050508463135354 : ((((((p5 → (p3 ∧ ((p4 ∨ p1) → (True ∨ ((((p3 ∧ (True ∨ p1)) ∨ p3) ∧ (p2 ∨ (p2 ∨ p2))) → p2))))) ∧ True) → p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_766920046263812434685582636879 : (((p4 ∧ (True → (((((True ∨ p1) → p4) ∧ ((((p2 ∨ False) → True) ∨ p1) ∨ True)) → p2) ∨ ((p5 ∧ ((p1 → False) ∨ False)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261054658725089634465741294481 : ((p4 → p2) → (False ∨ (p2 → (p3 ∨ ((p1 → ((True → p3) ∧ (((p2 ∧ p3) → (True ∧ p4)) ∧ (p1 → True)))) ∨ (p3 ∨ (p2 ∧ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194262472853813821330319075245 : ((p5 → (((False ∧ (p4 ∧ (p4 ∧ p1))) → p4) ∨ False)) → (True → ((True ∧ ((((p2 ∧ ((p1 ∨ p3) → False)) ∨ p4) ∨ p2) → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739500554433008705550592962891 : ((((p5 ∧ p1) ∨ ((((((p2 → (p5 ∨ p1)) ∧ p5) ∧ False) ∨ ((p2 ∨ p1) ∧ p4)) ∨ True) ∨ (True ∧ (((p1 ∨ False) ∧ p3) ∨ p5)))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299426904084358249391942931314 : (False ∨ ((p5 ∧ (p5 ∨ ((p2 ∧ ((p5 → (p2 → ((((p5 ∨ p4) ∨ p4) → p4) ∧ (p3 ∧ ((p2 ∨ p5) ∨ p5))))) ∧ p5)) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117889984666693505094724395836 : ((p5 ∧ (((p1 ∧ p3) ∧ (False ∧ (p3 ∨ ((p2 ∧ (True ∨ (p5 ∧ ((p1 ∧ True) ∨ (p5 ∨ True))))) ∨ False)))) ∨ (p5 → False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54049729605621540313271894537 : ((((((p3 → p4) ∧ p1) → p5) ∨ (p2 ∨ (p4 ∧ p4))) → ((((p4 → False) ∨ (((p2 → p4) → False) ∨ False)) ∨ (p3 → p1)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613535235546443389988834869242 : (((((((((p2 → p3) ∨ p2) → (False ∧ (True ∨ p3))) ∧ (p3 ∧ (False ∧ ((True → True) ∨ p4)))) ∧ p3) ∧ ((p2 ∧ p4) ∧ p5)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135046875303281479222063913985 : ((((((((p5 ∧ p5) → p1) ∧ ((p3 → p5) ∧ p2)) ∧ (p1 ∨ p2)) ∨ ((p3 ∨ p1) ∧ p5)) ∨ p3) ∨ (True ∨ p1)) ∨ (p4 → (False ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150336579404652934118281516480 : ((p5 → (((((((((p5 ∨ False) ∧ p3) ∧ p1) → p4) ∧ p2) ∨ True) ∨ p3) → (p3 ∧ (p1 ∨ p4))) → False)) ∨ (((p4 ∨ p4) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4569066663158511588361081247 : (p4 → (((((p5 ∨ p2) ∨ p1) ∧ ((p2 ∧ p4) ∨ (False ∨ ((p3 → (p5 ∨ (True ∧ ((p1 ∧ p4) → p2)))) → False)))) ∧ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351280071293231745828829436272 : (p4 → ((((p1 ∨ (((p4 → (((p1 → False) → p2) ∨ True)) ∨ (p2 → p2)) ∨ p4)) ∨ (p1 → (p1 ∨ False))) ∨ p1) → ((p3 → False) ∨ p4))) := by
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
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340917803170290047425360844406 : (p2 → (((((p5 ∨ (p4 → p3)) ∨ p1) → (p5 ∨ False)) → (p1 ∧ (((p4 → p2) ∧ p3) ∧ (False ∨ ((p3 ∨ p2) → (p2 ∨ False)))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337372952659293235297584689361 : (p1 → (((((False ∨ p2) ∨ p1) ∨ False) ∧ ((((p5 ∧ (p5 ∧ ((True ∧ (p2 → p1)) ∨ True))) ∧ p5) ∧ True) ∨ p4)) ∨ ((False ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168920540848834608365986692741 : ((p5 ∨ (p1 → (((p1 ∧ ((p4 ∨ ((False ∨ p5) → p2)) ∧ (p5 → p4))) ∨ p5) ∧ p4))) → ((p3 ∧ p2) ∨ ((True ∨ (p5 ∨ False)) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40939865569840608327558352814 : (((((p5 → (((((p2 → False) → False) ∨ p3) ∨ (p4 → (p4 ∧ ((True ∧ (False ∧ False)) ∧ True)))) ∧ p4)) ∨ p2) ∨ (p4 → p2)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208127786377778344913559680272 : ((((p5 ∨ p5) ∨ p2) → (p2 → p3)) → (((p4 → p2) ∧ (True ∨ ((True → ((p4 → (False → p4)) ∨ p4)) ∧ p5))) ∨ ((p2 → p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112477255502657491984834040631 : (((((p4 → p3) ∧ (p2 ∧ ((p2 ∧ ((p2 ∧ (False ∨ (p2 → p4))) ∧ (p3 → (True ∨ p5)))) ∨ (p1 → p2)))) ∨ False) → p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593890753618609978652736866027 : ((((((((p3 → p5) ∨ (((p2 → False) ∨ True) ∧ p4)) ∨ ((p3 → True) → p3)) ∧ (False ∨ True)) ∨ (((True ∨ p5) ∧ p2) ∨ p1)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205178208531569015637908365394 : (((p1 ∨ (p5 ∨ p5)) ∧ (False → True)) ∨ ((p5 ∧ (p1 ∨ ((p1 ∧ (True ∧ p3)) ∨ (p4 ∧ (p4 ∧ p1))))) ∨ (p3 → (True → (p2 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136883316783043181756541390647 : (((p2 ∨ p1) ∨ ((((((False ∨ p4) ∨ False) ∧ ((((False ∧ False) ∧ (False ∨ p3)) ∧ p2) ∧ p3)) ∧ False) ∨ p3) ∧ p5)) ∨ (p1 → (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252298341900674744258160278904 : ((p4 → p5) ∨ ((p1 ∨ True) ∧ ((((p5 ∨ False) ∧ True) ∧ (p2 → (((((p3 ∧ p3) ∧ True) → False) → (p2 → p3)) ∨ (p5 → p5)))) → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909038882127410764545925867198 : ((((((True ∧ (False → (((p3 ∧ False) ∧ p4) ∧ p1))) → p3) ∧ (((p2 ∨ True) ∨ p4) ∧ p5)) ∧ ((True → (p2 ∨ p1)) ∨ (p3 ∨ True))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h10 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : (True ∧ (False → (((p3 ∧ False) ∧ p4) ∧ p1))) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h12
          -- False on the left can always be used.
          apply False.elim h12
          -- False on the left can always be used.
          apply False.elim h12
          -- False on the left can always be used.
          apply False.elim h12
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h11
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h17 : (True ∧ (False → (((p3 ∧ False) ∧ p4) ∧ p1))) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h18
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h18
            -- False on the left can always be used.
            apply False.elim h18
            -- False on the left can always be used.
            apply False.elim h18
            -- False on the left can always be used.
            apply False.elim h18
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h19 := h4 h17
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : (True ∧ (False → (((p3 ∧ False) ∧ p4) ∧ p1))) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h23
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h23
          -- False on the left can always be used.
          apply False.elim h23
          -- False on the left can always be used.
          apply False.elim h23
          -- False on the left can always be used.
          apply False.elim h23
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h24 := h4 h22
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h28 : (True ∧ (False → (((p3 ∧ False) ∧ p4) ∧ p1))) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h29
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h29
            -- False on the left can always be used.
            apply False.elim h29
            -- False on the left can always be used.
            apply False.elim h29
            -- False on the left can always be used.
            apply False.elim h29
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h30 := h4 h28
          -- One of the premise coincides with the conclusion.
          exact h30
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h32 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h33 : (True ∧ (False → (((p3 ∧ False) ∧ p4) ∧ p1))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h34
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h34
        -- False on the left can always be used.
        apply False.elim h34
        -- False on the left can always be used.
        apply False.elim h34
        -- False on the left can always be used.
        apply False.elim h34
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h35 := h4 h33
      -- One of the premise coincides with the conclusion.
      exact h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h39 : (True ∧ (False → (((p3 ∧ False) ∧ p4) ∧ p1))) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h40
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h40
          -- False on the left can always be used.
          apply False.elim h40
          -- False on the left can always be used.
          apply False.elim h40
          -- False on the left can always be used.
          apply False.elim h40
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h41 := h4 h39
        -- One of the premise coincides with the conclusion.
        exact h41
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338408110418894663496502220659 : (p1 → (((p3 ∧ p2) ∧ (p2 → p3)) → (((p2 ∧ ((p4 ∧ (p3 → p5)) ∧ (p2 ∧ p2))) ∧ ((p1 → p4) ∨ p3)) ∨ ((p4 ∨ p4) ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38683732511327459856089064919 : ((((p1 ∨ (((p3 ∨ p5) ∧ p4) ∧ p5)) ∧ (False ∨ ((((((False ∧ p4) ∧ True) → p1) ∨ p3) ∧ (p1 → p1)) ∧ (p4 ∨ True)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149892975155891633371949735100 : ((p2 ∨ (False ∧ (((p1 → p3) ∨ (p1 ∧ (p3 → False))) ∧ ((p4 ∧ (((False ∧ p3) ∨ True) ∨ p1)) ∨ p4)))) ∨ ((p1 ∧ p2) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115240074021922640117185398456 : (((((p1 ∧ p2) → (False → ((p4 ∧ False) → True))) → p4) ∨ (p2 ∨ (((p5 ∨ ((p5 ∨ (p4 ∧ p1)) ∨ True)) → p4) → False))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180967247808598343262537667397 : (((p1 → p4) ∧ (False ∨ ((((p1 → (p4 → p4)) ∧ p1) ∨ False) ∧ p3))) → ((((p2 ∨ p1) → False) ∧ p4) → ((True → (p1 ∨ False)) → p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117626726894469290480590830470 : ((p3 ∧ ((((((p2 ∧ (False → (True → p4))) ∧ (p4 ∨ p5)) → ((p2 ∧ False) ∧ (p3 → (p1 ∧ p2)))) ∧ p1) ∧ p2) ∨ p5)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165629853178293912866903076981 : ((((p3 ∧ (p3 → False)) ∨ (p5 ∧ True)) ∧ (p2 ∨ (False ∧ (p3 ∨ ((p5 → p5) ∨ p2))))) ∨ (((p1 → (True ∨ (p5 ∧ p4))) ∨ p5) ∨ p5)) := by
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
theorem thm_5_vars_231546426002276188157174965906 : (((p5 → True) ∨ p1) → (True → (p1 ∨ ((((True → p2) → (True ∨ (False ∧ p1))) → ((True → (False ∨ (p4 ∨ (p1 → p3)))) ∧ False)) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((True → p2) → (True ∨ (False ∧ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2280341864122773261896455295 : ((((True ∧ ((False → p5) ∨ (p5 ∨ p2))) ∧ (True ∨ p1)) → (p5 → p3)) ∨ (False → (((p2 ∧ p2) ∧ False) ∨ (p5 ∨ (True → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174890957027697598587053529171 : (((p1 ∧ p1) → (p1 ∨ (True ∧ ((((False → True) → p1) ∨ p2) ∨ (p3 ∧ p1))))) → (((p4 → (p1 → p2)) ∨ (False → p5)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62988579334504149557175888356 : ((p4 ∧ (p5 ∨ (((((p1 ∨ (p2 ∨ p4)) ∨ p4) ∨ p1) ∨ p3) ∨ (p5 ∧ (((((p5 ∧ (p2 ∨ False)) ∧ p1) ∨ p1) → p3) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300959978263359810799124155162 : (False ∨ (((((((p5 ∨ p4) → True) ∧ p2) ∨ p5) ∨ (p3 → p4)) → p3) ∨ ((((p2 ∨ True) → (p2 ∧ False)) ∧ p2) ∨ ((p1 → p1) → True)))) := by
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
theorem thm_5_vars_389940003587321768677674361070 : ((((((p1 ∧ (p2 ∨ False)) → ((p4 ∨ (p4 ∨ p1)) → (True ∨ True))) → ((p1 ∨ ((p3 ∧ p4) ∨ (p2 ∧ (True ∧ p5)))) → p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_622482022394080040360502534613 : ((((p3 ∧ (p5 ∧ ((((p1 ∧ (p4 → p3)) → ((False ∨ False) → (p4 ∧ (True → p1)))) → ((p3 ∨ p3) ∧ (p2 ∧ True))) ∧ False))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785487467071283391779164067176 : (((p4 ∨ (((False ∨ p1) ∧ ((p2 → ((False → p3) ∧ (p1 ∧ p3))) → (p3 ∧ ((p2 ∨ ((True ∧ p4) → True)) → (p1 → False))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358055361233201702666690854434 : (p5 → (p1 ∨ ((False ∧ (((p4 → (p2 ∧ (p5 → (p1 ∧ False)))) ∨ p1) ∨ (False ∨ True))) ∨ (((False ∨ (p3 → p2)) ∨ p3) ∨ (p2 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689538058842876894202256359809 : ((((((p3 ∧ p2) ∧ (False → ((p3 ∧ p5) → p4))) ∨ ((p5 → (p3 → p5)) → p1)) ∨ ((p5 ∨ (True → (p5 ∧ p4))) ∧ (p5 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339601826551112461045099314659 : (p1 → (p2 ∨ ((((((True → p4) ∧ (p1 ∨ False)) ∧ (p1 → p3)) → (((p4 → ((p5 → True) ∨ (False ∧ p1))) ∨ p1) → p5)) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338981008118087155189950642488 : (p1 → ((p4 → p4) → ((True ∧ ((True ∧ p1) → (p3 ∨ (p1 → ((((p3 ∧ (False ∧ (p1 ∨ p3))) ∧ p1) ∧ p4) ∨ (p2 ∨ p2)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247289075781929506250022537370 : ((False ∨ False) ∨ ((p1 ∨ (((p1 ∨ (((p1 ∧ p1) → p5) → p3)) → (p1 ∨ p2)) ∧ ((p1 → (p3 → (p3 ∨ (True → p3)))) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216125705808755157674201131736 : ((True → (p2 ∨ (p4 ∧ p5))) ∨ (((p3 ∧ True) ∨ (p1 → (((p4 → (((p5 → p2) ∧ p5) ∧ p3)) ∨ ((False ∧ False) → True)) ∨ p3))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788977538861222227285289712093 : (((p5 ∨ ((p1 ∨ (p2 ∨ (((p4 → (p1 ∧ p3)) → (p4 ∨ (((p3 ∨ p1) ∧ p3) → (p4 ∨ p4)))) ∧ (p4 ∨ p1)))) ∨ (p4 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190462819496141980393480513359 : (((((p1 → ((True → p1) → False)) ∧ p3) ∧ p3) → p2) ∨ (((p5 ∧ p2) ∧ (((p2 ∨ (p5 ∨ p3)) ∧ (False ∨ p5)) ∧ p1)) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41321579553687978383069140827 : (((((True → p3) → (p2 ∨ (p1 → ((((p2 → p2) ∧ p2) → (p5 → p2)) → False)))) ∧ (True ∨ (((False ∨ False) ∨ p2) → False))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51489285669308701471247407928 : ((((p3 → ((p1 ∧ p2) ∧ p4)) ∧ ((True ∧ (False → (p2 → ((p2 ∨ False) ∨ p3)))) → p4)) → ((((p4 → p2) → p5) ∨ p4) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782994562507523178417799544343 : (((p3 ∨ (((p5 ∧ (True ∧ ((p4 ∨ ((p2 → p4) ∧ (False → p4))) → (p5 ∧ True)))) → (p1 ∨ ((p2 → p4) → p3))) ∨ (p4 ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_175384173123364188409187795946 : ((True → ((False ∧ (True ∨ False)) ∨ ((((p5 → (p2 → p1)) ∨ p1) → False) ∨ p2))) → ((p1 ∧ ((p5 ∧ p3) ∨ p3)) → (p2 ∨ (False ∨ p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : ((p5 → (p2 → p1)) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h20 := h1 h19
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : ((p5 → (p2 → p1)) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- False on the left can always be used.
        apply False.elim h27
      case inr h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345361521554920563649840957210 : (p3 → ((((p3 ∨ (False → (True → (((p1 ∧ (p3 ∨ (((p3 → p2) → p4) ∧ p3))) → p3) ∧ ((p3 ∨ p1) ∨ p1))))) → p1) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47337182274183148329447189508 : ((((True ∨ p1) ∧ (((p2 ∨ p5) → p4) → (p2 ∨ ((((((True ∨ p3) ∧ p4) ∧ p4) → True) ∨ p5) ∧ (True ∧ False))))) ∨ (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789392875527144031334127583822 : (((p5 ∨ (((p2 → ((p4 ∧ False) ∧ ((False ∧ (p1 ∧ (p5 ∧ False))) ∧ p4))) ∨ p1) ∨ ((((p3 ∨ p5) → (p2 → True)) → True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336117277609577510845452488079 : (p1 → ((((((True → ((p3 ∨ (((False ∨ True) ∨ p1) ∨ p5)) ∧ (True → p3))) ∨ (p4 ∧ p3)) → (False ∧ p5)) ∨ (True ∨ p2)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64355178191502981652680295835 : ((p1 ∨ ((((False → p1) ∨ (((p3 ∨ (False ∨ ((p4 ∨ p2) ∨ p2))) ∨ ((p3 ∧ (p4 ∨ (p4 ∨ True))) ∨ p3)) → True)) → p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259140022959098933107379030866 : ((False → True) → ((((((((p3 ∧ (p5 → (True ∨ (p1 ∨ p1)))) → p5) → p4) → True) → p4) ∧ p4) ∨ (p2 ∨ (False → p5))) ∨ (p1 ∨ p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616679065342412197418929709486 : (((((((p4 → ((p5 ∨ p5) ∨ (p5 ∨ True))) ∧ True) ∧ p2) ∨ ((p5 → p1) ∧ (p5 ∧ (((p2 → p3) ∧ p5) ∧ (p5 → p4))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42398291375072990211520250557 : (((p4 ∧ (p3 ∧ (((((p4 ∧ (p1 ∨ (p5 ∧ False))) → p3) ∨ (p1 → (True → p5))) → (p5 ∧ False)) → ((p4 → p1) → p4)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135132944160109555245520539192 : (((p4 ∧ ((p1 ∨ True) ∧ ((((p3 ∨ False) ∧ p5) → (p5 ∧ ((p2 ∧ p2) ∧ p2))) → (p1 → p1)))) ∨ (p4 ∧ p4)) ∨ (False ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773980672845553135451404282192 : (((False ∨ ((((((p2 ∨ False) ∨ p2) → (p3 ∧ ((False → p1) ∧ (False ∧ (p5 ∨ p1))))) → (True ∧ p2)) ∨ (p5 → p2)) ∧ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148180329819297180471550800694 : ((((((p5 ∨ (((p2 → p2) ∨ p4) ∨ p2)) → True) ∧ (p2 ∧ False)) ∨ (p3 ∨ p4)) ∧ (p1 ∨ (p3 ∧ False))) ∨ (((p3 ∨ p2) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123874974120534900992886132059 : ((((True → p2) ∨ ((((p3 → p5) → (True ∧ p4)) ∧ (True ∨ p3)) → False)) → ((p5 → True) ∧ (p2 ∨ ((p4 → p3) ∧ p4)))) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53247953274770711603649558683 : ((((p5 ∧ p1) ∧ (p4 ∧ (((p1 ∨ False) ∧ (p2 ∨ p1)) ∧ p1))) ∨ (True ∨ (True ∨ (True ∧ (False → ((False ∧ (p2 ∨ p3)) ∧ p2)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354883717583388374161380060089 : (p5 → ((p2 ∧ ((((p2 ∧ ((True ∨ (p4 → True)) ∧ p4)) ∧ p3) ∨ (p4 ∧ (((p1 → p5) ∨ p4) ∧ p4))) ∨ ((p3 → p4) ∨ p4))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669509265104615078547501511204 : ((((((p5 ∨ (False ∨ ((False ∧ True) → False))) ∧ (((False ∨ True) → ((p5 → p4) ∧ True)) ∨ p5)) → (p1 ∨ p3)) ∨ (p4 ∧ (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_446230193346541918795064895122 : ((((((p4 → (p1 ∧ p4)) → ((True ∨ (p2 ∧ (p1 → (p2 ∧ p3)))) ∨ (p3 → (False → p5)))) → (p4 ∧ p2)) → (p3 ∨ (True → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → (p1 ∧ p4)) → ((True ∨ (p2 ∧ (p1 → (p2 ∧ p3)))) ∨ (p3 → (False → p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354091827233275922499228661294 : (p4 → (p5 → ((p4 → ((((p1 ∧ (p4 ∨ p1)) → (True ∧ p5)) ∨ (((True ∨ p2) ∨ (False → p2)) ∧ p1)) → (p4 → False))) ∨ (p5 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62046158288622466918451254679 : ((p2 ∧ ((p3 ∨ False) ∨ (((False ∧ (p4 → p5)) ∨ ((((p5 ∧ True) → (False ∨ False)) → p5) ∨ (((p5 ∧ p1) ∨ True) ∧ False))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72530277226990585703524860229 : (((((p1 ∨ ((p5 → (p5 → p4)) ∧ (p3 ∨ False))) → ((p2 ∨ (p5 ∨ (((False ∨ p1) ∨ (p2 → p2)) → p1))) ∧ p3)) ∧ p1) ∨ p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ ((p5 → (p5 → p4)) ∧ (p3 ∨ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182213517478215038258252297413 : ((((p5 ∨ (p2 → ((p3 ∨ p3) ∧ False))) ∧ (p4 ∨ p3)) → True) ∧ ((p1 → p5) → (((p2 → True) → (p1 ∨ (False ∧ p1))) → (p2 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180703971112686380576799493065 : ((((p2 ∨ (True ∧ False)) ∨ p4) ∧ (((False ∨ p4) → p4) ∨ (True → p5))) → (p1 ∨ ((((False ∧ False) ∨ p1) ∨ (p3 ∧ p5)) → (False ∨ True)))) := by
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
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- False on the left can always be used.
            apply False.elim h10
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Conjunctions on the left can always be decomposed.
            let h20 := h19.left
            let h21 := h19.right
            -- False on the left can always be used.
            apply False.elim h20
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- False on the left can always be used.
          apply False.elim h34
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h40 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h41
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Conjunctions on the left can always be decomposed.
          let h44 := h43.left
          let h45 := h43.right
          -- False on the left can always be used.
          apply False.elim h44
        case inr h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h47 =>
        -- Conjunctions on the left can always be decomposed.
        let h48 := h47.left
        let h49 := h47.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303748805227613582004244325081 : (p1 ∨ ((((((True ∨ (p5 → (p4 ∨ (True → (False ∧ p3))))) ∧ (False → (p3 ∧ True))) → (p4 ∧ (p5 ∧ (p3 ∧ p1)))) ∨ False) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309781592578068918823804239759 : (p2 ∨ ((((p1 ∨ (((True ∨ p3) → (((p1 ∧ p4) ∧ (p3 ∨ p1)) ∨ (p1 ∧ p2))) ∧ True)) ∧ p1) ∨ True) ∨ (p1 ∨ ((p2 → True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303004873613669661645519261704 : (False ∨ (p1 → ((True → (p1 ∧ (True ∨ ((((p3 ∧ p5) → p4) → p1) → p2)))) ∧ (((p5 ∨ p5) ∨ (p5 ∨ (p5 ∧ True))) → (False ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
      exact h1
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185179985372866670254809990333 : (((p4 → False) → (p5 ∧ (True ∧ (p4 ∨ ((p3 → p4) → p1))))) ∨ ((p1 → True) ∨ ((((p1 → p4) ∨ ((p5 ∧ True) ∧ p4)) → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66638803863990477201455743342 : ((True → ((((True → (p1 ∨ (p5 ∨ False))) ∧ (p4 ∧ (p4 → True))) → False) ∨ (p1 ∧ ((p3 ∧ ((False ∨ p3) ∨ p5)) ∨ (True ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137478386117661172798416451880 : ((p5 ∧ ((((True ∧ ((((((True ∧ p1) ∧ p5) → p2) ∨ p1) ∧ p2) ∨ (p1 ∨ (p2 ∧ p4)))) → p1) ∨ p3) ∧ p5)) ∨ (True ∨ (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42295916562301545193570056341 : (((p2 ∧ ((p5 ∨ (p1 → (True → (p2 ∧ ((((p5 ∧ False) → (p3 ∧ ((p2 ∨ True) ∨ (p2 → p3)))) → False) ∧ p1))))) ∨ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312471560437377766852407576777 : (p2 ∨ (p5 → (((p5 ∨ (((((True ∨ (p4 ∨ (p5 → ((True ∧ p4) ∨ p2)))) → (p1 ∧ p5)) → (p5 ∧ p4)) ∧ p1) ∨ False)) → p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62564639551852404152836624450 : ((p3 ∧ (p5 ∨ (True ∧ ((p2 ∧ p5) ∧ (p5 → ((p3 ∧ (p4 → p5)) ∧ (((False ∨ p2) → (((p2 ∧ p5) ∨ p4) ∨ p2)) → p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318894936865914125339435823580 : (p4 ∨ ((p3 ∧ (((p4 ∧ ((p3 ∧ (p5 ∨ ((True ∧ (False ∨ True)) → p2))) ∧ p1)) ∨ (p3 ∧ (p3 ∨ p1))) ∧ False)) ∨ (False → (False → p2)))) := by
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
theorem thm_5_vars_186211386299383390901966440360 : (((p5 ∨ ((p4 ∨ (p2 ∨ (False ∨ False))) ∧ (p3 ∨ True))) ∨ p2) → ((((p5 ∧ (p5 ∧ p1)) → ((p2 → True) → False)) ∧ (p4 → p4)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
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
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- False on the left can always be used.
            apply False.elim h15
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156924821591013640373571011102 : ((((p1 ∨ ((p5 ∨ True) ∧ ((((p4 ∧ (True ∨ True)) ∨ p1) ∨ (p4 ∨ False)) → p5))) → p4) ∨ True) ∨ ((p5 → (True ∨ True)) ∧ (True → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654186326749526238355523708313 : (((((((p4 → p3) ∧ (((p5 → (p4 ∨ p2)) → (((p2 → ((p4 ∧ p2) → p2)) → p3) ∧ p4)) ∧ p4)) ∨ p3) ∨ p1) ∨ (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1809161599309472765052917620 : ((p4 ∧ ((((p5 → ((p1 → p3) ∧ p4)) ∨ ((False ∨ ((p5 ∧ p5) → (p1 ∨ p1))) ∧ p2)) → False) ∧ True)) ∨ ((False → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146995676427223372142802588760 : (((((((p2 → p4) ∨ p5) ∧ ((p4 → (True ∧ (False → (False ∨ p2)))) → p2)) ∨ p5) ∧ (p2 ∧ False)) ∧ p2) ∨ ((False → False) ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923385357895980453180233180192 : ((((((p5 → ((p5 ∧ p2) ∧ (False ∧ p5))) → False) ∧ (p2 ∧ p2)) ∧ (p5 → ((((p5 ∨ True) → False) ∧ ((p2 ∧ False) ∧ p5)) ∨ p5))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



