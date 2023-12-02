variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164919385563773622301926447018 : (((((p2 → (p1 → (p3 ∧ (p4 ∨ (p5 ∧ (p2 → (p5 → p2))))))) ∧ p1) ∨ p1) → p5) ∨ (True ∨ (p2 → (p3 ∨ ((p3 ∧ p4) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67555322253495025043834317487 : ((p1 → ((p3 → (p5 ∨ p2)) → ((p4 ∨ ((p3 ∧ p3) ∨ p4)) ∧ ((((p4 → p2) ∨ (((False ∨ p1) → p4) ∧ False)) ∨ p1) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158514345178920578421128058918 : (((p2 ∨ True) → ((p4 ∨ (p3 ∨ (p1 ∧ p2))) ∧ (((p1 ∨ ((p5 ∨ p4) → p4)) → p3) → True))) ∨ (p4 ∨ (True ∨ ((p1 ∧ p4) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158779161786256053959896199010 : ((p5 ∧ (((p1 → (((p3 → (p5 ∧ (p1 → (p1 → False)))) ∨ p2) → p2)) ∧ (p2 ∧ False)) ∧ p4)) ∨ (True ∨ (p4 → ((p1 ∧ p2) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233501652640344188103861336087 : ((p1 ∨ (p4 ∧ True)) → (p5 ∨ ((p5 ∨ p1) → ((p2 → (p1 ∧ ((p4 ∨ ((False ∧ ((p4 ∨ (False → p4)) ∧ p5)) → p2)) → p5))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688255230843050420320260798686 : (((((p2 ∧ p5) ∨ (((p4 ∧ (((p3 ∨ False) ∧ (p3 → p3)) ∧ p2)) → p2) ∨ p2)) ∧ ((p3 ∨ ((p2 ∨ p5) ∨ False)) ∨ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45246725532403570922103542682 : (((p1 ∧ ((False → (((p2 ∧ p5) → p5) ∧ False)) ∧ ((True ∧ ((False ∧ p3) ∨ p3)) ∨ ((p3 ∨ True) → ((True ∧ p1) → p1))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625577282345061946421616777158 : ((((p1 → (((((False → p2) ∧ ((p3 ∧ p2) ∧ (p5 ∧ (((p2 ∨ p4) ∧ p3) ∨ p4)))) → p4) ∧ (p3 ∧ (p1 → False))) ∧ False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_714219419310264708557772333754 : ((((((False ∨ p5) ∨ p1) ∧ (False ∨ p4)) → ((((True → (p4 ∧ (True ∧ p2))) → p1) ∨ (p1 ∧ ((True ∨ p2) ∧ (p2 ∧ p1)))) ∨ p4)) ∨ p4) ∧ True) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183818179659316767193188506940 : ((((((False ∨ ((p1 → p5) → True)) → p3) → False) → True) ∧ p1) ∨ ((p4 → ((False ∧ ((False ∨ (p3 → False)) ∧ p3)) ∧ (p2 → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722087057581738380348330277141 : ((((p2 → ((False ∨ p1) → p4)) → (p2 ∧ ((p4 ∨ p5) ∧ (False → (p2 ∨ (((p1 ∧ ((False → (p1 ∨ True)) ∧ p4)) → True) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47449044585643107770894572044 : (((p3 ∧ (True → ((p1 → (((p5 ∨ p4) ∧ ((p3 → p5) → ((p4 ∧ p4) → p3))) → ((p1 ∨ p1) ∧ False))) → p1))) ∨ (False → p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180233764676488119415666329711 : (((p2 ∧ (((p5 ∨ (True ∨ (p4 → p1))) → p4) ∨ (p1 → p5))) → p1) → (False ∨ (((((p4 ∧ p3) ∨ p1) ∨ (False ∨ p3)) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_166702302921159562527642418251 : ((p3 → ((((p4 ∧ p1) ∧ ((True → False) ∨ (p1 ∨ (p4 ∨ True)))) → (False ∨ p2)) ∨ True)) ∨ (((p4 ∨ (p1 → False)) ∧ p5) ∧ (p2 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263708718589240400128241328119 : (True ∧ ((p1 ∨ (p3 ∧ (((((((True ∨ p1) ∧ p4) ∨ (p1 → True)) ∨ False) → False) ∨ p1) ∨ p5))) ∨ ((p1 ∧ ((p4 ∨ False) ∧ False)) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825221699198471438063929600564 : (((((p3 → (False → p1)) → ((((p4 ∧ p3) → p2) ∧ ((p5 ∨ (p4 ∧ ((False ∨ True) → (p1 → p1)))) ∨ (False → p3))) ∧ False)) ∧ p5) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (False → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1462259361456011979404992133 : ((((p5 → p2) ∧ ((False ∨ p5) → (p2 ∨ ((p2 → ((p3 ∧ (p3 ∧ ((p3 → p3) ∧ p2))) ∨ p3)) ∧ p1)))) ∧ p4) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38614624622577009701090239396 : ((((False ∨ ((p1 ∨ (p2 → False)) ∧ (False ∧ p2))) ∧ ((False ∨ (p5 ∨ p1)) ∨ (False ∧ (False ∧ ((p1 ∧ True) ∧ (p5 ∨ p5)))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42433092621059514868405871421 : (((p5 ∧ ((p2 → p2) ∧ (((False ∧ p4) → ((p5 ∨ p2) ∧ ((p5 ∧ ((p3 ∧ ((p5 ∨ p2) → p4)) → p3)) → p5))) → p1))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184221103397150707577353488881 : ((((((False ∧ p1) ∨ p4) ∨ (True ∧ (p1 ∧ p3))) ∨ p1) → p4) ∨ ((((p5 → ((True ∧ p5) → (False ∧ p5))) ∧ (p5 ∨ True)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344615004674840319151288581150 : (p2 → (p1 → (((((p3 ∨ p3) ∧ p3) ∧ (p5 ∨ p5)) ∨ p1) ∨ ((False ∧ False) ∨ (p2 → (p4 ∨ ((True ∨ (True → (p3 ∨ True))) → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198353587778427664520138742315 : ((p2 ∧ (p3 ∧ ((p1 ∨ (p1 ∨ p1)) ∨ p4))) ∨ (((p3 → (p4 ∧ p4)) → p2) → ((p4 ∨ (p2 → (((p5 ∧ p5) ∨ p2) ∨ True))) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778977853668808417647050310605 : (((p1 ∨ (p3 → (((p1 → ((p5 ∨ p2) ∧ (p2 ∨ (p2 → (p5 ∧ p3))))) ∧ (True ∧ (p1 ∨ (True → p2)))) ∨ ((True ∨ p5) ∨ True)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_138223296470979892592994762216 : ((p2 → ((False → (p2 ∨ ((True → ((p5 ∧ ((True ∨ False) ∧ (p1 ∨ p5))) → False)) → ((p3 ∧ False) → p2)))) → p1)) ∨ (p1 ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353427303465323977109884933458 : (p4 → (p1 ∨ ((((p5 ∧ ((p3 ∨ (((True → True) ∨ (False ∨ (p3 → p5))) → False)) ∧ p4)) ∨ (p2 ∨ p1)) ∨ p3) → ((p5 ∨ p3) ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
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
theorem thm_5_vars_135298753161654848484999577353 : ((((((p4 ∧ False) ∧ (p4 → ((p1 → False) ∨ (((True ∨ p5) → True) ∧ p2)))) ∧ p5) ∨ p3) ∧ (p4 ∨ (p1 → False))) ∨ (True → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709772387789709285888230596436 : ((((p1 → (False ∧ ((p5 ∧ p5) → (p2 ∧ p1)))) → (((((p5 ∧ True) ∨ False) ∧ (p1 ∨ p2)) ∨ p1) ∨ ((p4 ∨ (p1 → p5)) ∨ False))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172729915658291566181417195334 : (((p2 → False) ∨ ((((p1 → p1) ∨ (p2 ∨ (p2 → True))) → (p3 ∨ p4)) ∧ p3)) ∨ (p3 ∨ ((p4 ∨ (False → (p1 ∨ (True ∨ p1)))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731037987358478362510748463201 : ((((False ∨ (p5 → p3)) → (p4 → ((p1 → False) → ((p2 ∨ (p2 ∨ ((p2 → ((p4 ∧ p2) → (True → p3))) → p1))) ∨ (p5 → True))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164995998322077735701746965727 : (((((p1 ∧ True) ∧ (((p2 ∧ False) ∧ p5) → p5)) ∧ ((p4 ∨ (p2 ∧ p1)) ∨ p1)) → p2) ∨ (p5 → ((p5 → p4) ∨ ((p2 → True) ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251370239834990958266120246314 : ((p2 → p4) ∨ (((((p5 → p3) ∧ ((False ∨ False) → ((p5 ∧ (p2 → (True ∨ (False ∨ False)))) ∧ p1))) ∧ True) → p4) ∨ (p1 → (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260816190034558969274430490137 : ((p3 → p5) → (True → ((((((p2 → p2) ∧ True) ∧ (True ∧ False)) → False) → False) ∨ ((True ∧ (p4 → True)) → ((p2 → (p1 → p1)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53487727189900388592733271032 : (((p4 ∧ ((False ∨ p2) → (((p5 → p5) ∧ (p3 ∨ p2)) ∨ p4))) → (((((False → False) → p5) → (False → p2)) ∨ (False ∨ False)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191619373788525168135316415621 : ((p3 ∧ (p2 ∧ ((((p2 ∧ p4) ∧ p4) ∧ p4) ∨ p5))) ∨ (True ∨ (((False ∧ p2) ∧ ((p3 ∧ p4) ∧ (True ∧ ((p5 → False) ∨ p1)))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223416473898704860750659458479 : ((True ∨ (p2 → p3)) ∧ ((p3 ∧ (p1 ∨ (((p2 ∨ p2) ∧ p1) ∧ (False → ((True ∧ ((p5 ∧ True) → ((p2 ∧ p4) → True))) ∨ p5))))) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336180300457324425653291035899 : (p1 → (((True → (p1 ∧ (True ∨ ((p2 → False) ∨ ((p2 ∧ (((p2 → p3) ∨ (False → p2)) ∨ (p4 ∨ (p3 ∨ p1)))) → p2))))) → p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147053157980050083723553939144 : ((((((True ∨ (p5 ∨ p5)) ∧ (p3 ∧ (p4 ∨ p3))) ∨ False) ∨ (((p1 ∨ p1) ∧ False) ∧ (False ∨ p4))) ∧ False) ∨ (True ∧ ((p4 ∨ p5) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172350850992750720446794041304 : (((((p5 → p2) ∨ (p1 ∧ False)) ∧ False) ∨ (((True → p1) → (True → True)) ∧ p3)) ∨ (((((True ∨ False) ∧ False) → p4) → (p5 ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357255952081869400247753029216 : (p5 → ((p1 ∧ True) ∨ (True ∧ ((((p1 ∨ (p3 → ((p1 ∨ (p5 ∨ p3)) ∧ ((True ∧ ((True ∧ False) ∨ p4)) ∨ False)))) ∨ p4) ∨ True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618234166580185365236034290177 : ((((((p3 ∧ (p4 ∨ False)) ∨ p3) ∨ (((p4 → False) → p1) ∨ (p1 ∨ ((True → (True ∧ ((p4 → p5) ∨ (p1 → p3)))) ∧ p5)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209576030665325591602103088275 : ((p5 → ((p4 ∨ p5) → (p1 ∧ p2))) → (((p2 ∧ p3) ∨ (p5 → (p3 → p5))) ∨ (((p1 ∨ p5) → (False ∨ p3)) ∨ ((p1 → p1) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197841226752059008300797058987 : (((p2 ∨ (p5 ∨ p2)) ∨ ((p1 → False) ∨ False)) ∨ (False → (p4 ∨ ((p3 → False) ∧ (False ∨ (False → (False ∨ (p2 ∨ ((p1 → p3) → p3))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67606286276779501006968679068 : ((p1 → (p2 ∧ (((((p3 ∧ True) → (p2 ∧ p4)) → ((((p1 ∨ p4) → (False ∧ (p1 → False))) ∧ p2) ∨ p1)) ∧ (p4 ∨ p3)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165901216213378035153157235254 : (((False ∨ (p1 ∨ p5)) → (((((p2 → ((p5 ∨ p3) → p1)) → p3) ∨ False) ∨ False) → False)) ∨ (((False ∧ p5) ∧ False) → ((p1 → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179206790010409551218568280947 : ((p4 ∧ ((p2 ∨ ((((p4 → p5) → p1) ∧ (p2 ∨ p4)) ∧ False)) ∧ p3)) ∨ (((((p4 ∧ True) → p1) ∨ p1) → True) ∨ ((p4 ∧ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42505392271389091709613060903 : (((False ∨ (((p5 → ((True ∨ p2) ∨ p1)) ∧ (True ∧ (False ∨ p4))) ∨ (((p2 ∧ p3) → ((p2 → p2) ∨ False)) → (p3 ∧ p2)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174361837543567805080971014213 : (((True ∨ (((p2 ∧ ((True → p3) ∨ p3)) ∨ p1) ∨ p2)) → (False ∨ (p2 ∧ False))) → (((p5 ∧ ((True ∧ p2) ∧ (p3 → False))) ∨ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p2 ∧ ((True → p3) ∨ p3)) ∨ p1) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684150583452660968490736386161 : (((((((False ∨ p2) → (((p3 ∨ (p4 ∨ p5)) ∨ (True ∨ p3)) ∧ p3)) → p2) ∨ (p5 ∧ p1)) ∨ ((p3 ∧ p5) → (p5 ∧ (p1 → p1)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66451479462363551513855871386 : ((True → (((((False ∨ (False ∧ False)) ∧ p5) → (True → (p1 ∧ p1))) → ((p5 ∧ (True ∨ (True ∨ (p3 → (p1 ∨ p3))))) ∧ True)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_579722235921674554385708504690 : (((p4 → ((((p1 ∧ False) ∧ ((p1 → p5) ∨ ((((p3 ∨ p3) ∨ p3) → (p1 ∨ p2)) ∨ p3))) ∧ (((False ∧ True) ∧ p2) ∨ True)) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_46859616650039947155757030459 : ((((p3 ∧ (((p5 → ((p5 ∧ p1) → ((p2 → p3) ∧ (((p4 ∨ p1) ∧ p4) ∧ False)))) → p5) ∨ (p3 ∨ False))) ∧ p2) ∨ (p4 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186907791568418795282359011204 : ((((p2 ∧ p1) ∨ p3) ∧ (p2 ∨ ((p1 ∧ (p2 ∨ p1)) ∧ p3))) → ((p1 ∧ (p4 ∨ p1)) ∨ ((p3 ∧ (p2 → False)) → (p5 ∧ (p4 → p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h21 := h19 h20
      -- False on the left can always be used.
      apply False.elim h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h17.left
      let h24 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h28
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h31
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111072721579832561394467253555 : (((((p5 → (p4 → (p4 ∨ (p3 ∨ (((p2 → p1) ∧ p5) ∨ False))))) ∧ p1) → (((p1 → p5) ∨ p2) ∧ (p5 → p2))) ∧ p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244822934774425491960199119529 : ((p1 ∧ p1) ∨ (((p5 ∨ ((False ∨ p3) ∧ p2)) ∨ p5) → (((False ∨ p3) ∧ (p2 ∨ p5)) ∨ (((p4 ∨ ((p4 → p3) ∨ False)) → p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319411610485721709685745749766 : (p4 ∨ ((p3 ∨ ((((p2 ∨ (p1 ∧ (False → p1))) ∧ p5) ∧ (p3 ∧ p4)) ∨ p1)) → (((p2 ∧ True) ∨ (p5 → (False ∧ True))) → (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h10.left
          let h15 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h10.left
          let h20 := h10.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h27.left
          let h32 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- Conjunctions on the left can always be decomposed.
          let h36 := h27.left
          let h37 := h27.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h34
      case inr h38 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550711547586024018310153304120 : (((p1 ∨ ((p3 ∧ (False ∨ (p5 ∨ ((p2 → p3) → ((p4 ∨ p5) → (p2 ∨ (p3 ∧ (True → (p3 ∧ p3))))))))) ∨ (True ∨ (p4 ∧ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690428895442048844559870795354 : ((((((p2 → (False → (((False → p1) ∨ False) ∧ (p3 → (p4 ∧ False))))) ∨ False) ∧ p1) → ((((p1 ∨ (True → p2)) → True) → p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197744526423669358231892707500 : ((((False → p5) → p2) ∧ (p5 ∧ (p3 ∧ p5))) ∨ ((p2 ∨ (((p2 → p4) ∨ p5) → p3)) ∨ (p1 → (False → (p1 ∨ (p1 ∧ (p1 ∧ p5))))))) := by
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
theorem thm_5_vars_123653294362163380272837783040 : ((((((p5 ∧ p4) → (p5 → (p2 ∨ (p3 → p5)))) ∧ p5) → (p2 ∧ (False → p1))) → (p2 ∨ (False ∨ (p1 ∨ (p5 ∧ p2))))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208793305962397218565952641048 : ((p2 ∧ (p3 ∨ (p3 ∧ (p3 ∧ p2)))) → (True ∧ (((((p5 → True) ∧ ((p4 ∧ (p4 ∨ p1)) ∧ (p3 ∨ p3))) → (False ∨ p2)) ∧ False) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141114168690563018280705658451 : ((((p2 → p2) → ((p3 → (p4 ∧ p1)) → p5)) → (((True ∧ (False ∧ p3)) ∨ ((p5 → (False ∨ p5)) ∧ p1)) ∨ True)) → ((p1 ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45445133220779383787884093563 : (((True ∨ ((p5 → (p3 ∧ (p5 → p5))) ∨ (((False ∨ (p5 → p4)) ∨ (p5 → (p2 ∧ p4))) → (((p3 → p1) ∧ p5) ∧ p4)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58375298244737188856295258342 : (((p1 ∨ p2) ∧ ((p3 ∨ False) → (((p1 → ((p5 → ((True → ((p1 → p5) ∨ p5)) ∨ p1)) ∧ p2)) → ((p2 ∨ p4) ∧ False)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47745397154244743899667087828 : (((((False ∧ (((p5 ∧ p4) → False) ∨ p4)) ∨ ((True ∧ ((True ∨ p2) ∧ (False → ((p4 → p4) → p5)))) ∧ True)) ∨ False) → (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260341825704700232670154889968 : ((p2 → p5) → ((((((False ∧ p3) → (False → (((False → (p2 ∨ (True ∧ (False ∨ (False ∧ p2))))) ∧ p5) ∨ p2))) ∧ p4) → p3) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65252301229983288882813651131 : ((p3 ∨ ((((p1 ∨ (True → p3)) ∧ (p3 → (((p1 ∨ (p4 → p3)) ∧ False) ∧ p4))) ∧ ((p1 ∧ p4) ∨ (p5 ∨ (p1 ∨ p4)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8487937460421092163301528941 : (((((((p1 ∧ ((p4 ∨ p4) ∨ (p2 ∨ (False ∧ (True ∧ p5))))) ∧ ((True ∧ False) ∨ (p5 ∨ p2))) ∨ True) ∧ p1) ∧ (p5 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314567645482268524913152244497 : (p3 ∨ ((p5 → (((p5 → p3) ∧ (p5 → ((False → ((p3 → (p2 → True)) ∧ p5)) ∧ False))) → p3)) ∨ ((False ∧ p5) ∧ (False → (p1 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153394113142478483141050577745 : ((p3 ∨ ((p3 ∨ ((((p5 ∧ (p1 ∧ True)) → p1) ∧ (((True ∧ True) → p1) ∨ True)) ∧ p4)) → (False ∨ p3))) → (((True ∨ False) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726982284402515560331305358567 : (((((p1 → False) → p4) ∨ (((p1 → True) ∧ ((p3 → ((False → True) → p1)) → ((p5 ∧ True) ∧ ((p4 ∧ (True → p2)) ∨ p1)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349013529322109003509979971096 : (p3 → (p4 ∨ (False ∨ ((p2 ∧ ((p3 ∨ p1) ∨ (((p2 ∨ p4) ∨ (False → (((p1 → False) → True) ∨ p3))) → (p3 ∧ p5)))) → (p4 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135736220387767122259319149888 : (((((p5 ∨ (p4 ∨ (p3 → p3))) ∨ ((p2 → True) ∧ p3)) ∧ (p2 ∧ p5)) ∨ ((True → p2) ∨ (p1 ∨ (p3 → p3)))) ∨ (p5 → (p3 ∧ p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803433152274271769902002973972 : (((p3 → ((p4 → ((p1 ∧ True) ∨ (p2 ∨ (((p1 ∨ (p4 ∧ p2)) → ((p4 ∨ True) → (p5 ∨ ((p5 → True) ∨ p1)))) ∨ True)))) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165437689189799617248516341745 : (((p4 ∨ (((((p1 → (p4 → p1)) ∨ p5) → p1) → False) ∧ False)) → ((p2 → False) ∨ False)) ∨ ((True ∧ ((p3 ∧ False) ∧ p5)) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238074835970537057183813283561 : ((True ∨ p2) ∧ ((True ∧ (p2 ∨ ((p1 ∧ p2) ∧ (((False ∨ (p4 → (False → p3))) ∧ p5) ∧ True)))) ∨ (p5 → (((p4 → p1) → p4) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_209364896543166685237362925604 : ((p1 → (((p2 ∨ True) → p4) ∧ p1)) → ((((p3 ∧ (p2 ∨ (True → ((p5 ∧ p5) ∧ (p5 → p2))))) ∧ p5) ∧ (p3 → True)) → (p2 ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312341659428680194968279224885 : (p2 ∨ (p2 → (p4 → (((p2 ∧ (True ∧ (p3 ∧ (p3 ∨ p1)))) ∧ ((((p3 ∧ p5) ∨ (p3 ∨ p1)) ∧ p1) ∧ False)) ∨ ((p4 ∧ p5) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354877013817517822141450892553 : (p5 → ((p1 ∧ (((((True ∨ ((p3 ∨ (((p3 → False) ∧ False) → p5)) ∨ (p1 → (False ∨ p4)))) ∨ False) ∧ (True ∨ p1)) ∧ True) → p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733877829099794270689722511839 : ((((p5 ∧ p5) ∧ (((p1 → p5) ∨ p4) ∧ ((((p1 → p2) → False) ∨ (True → ((p4 → (p3 ∧ ((p2 ∨ p1) → False))) ∨ p1))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137481271709601399854111886685 : ((p5 ∧ ((((p2 ∧ p2) ∧ p1) ∧ ((False ∧ (p4 → p2)) ∧ (((p1 ∨ p1) ∨ (p5 → (p5 → p1))) ∧ p5))) ∧ True)) ∨ ((True ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148394197201169605075622682237 : (((p2 ∧ ((((False ∧ (p5 → p5)) ∨ p5) ∧ p3) → ((p2 ∧ p1) ∨ False))) ∨ (p1 → (p5 ∨ (p5 ∧ p3)))) ∨ (False → (p4 → (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113504757403264700659425529991 : ((((((p5 → ((False → p3) → ((p1 → True) ∧ p3))) ∨ (p4 ∧ p1)) ∧ p1) ∨ (p3 ∨ (p2 ∨ (p1 ∧ False)))) ∨ (p5 ∧ True)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248164483276155254026985504656 : ((p2 ∨ False) ∨ (((p4 → p2) → (p3 ∨ p2)) ∨ ((p3 → True) ∨ ((True ∧ p2) → (((True ∧ (False ∨ (p3 → False))) ∨ p1) ∧ (True ∨ p1)))))) := by
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
theorem thm_5_vars_4060531577495880865582674652 : (p2 ∨ (True ∧ ((((((p2 ∨ False) ∧ ((p2 → (p2 ∨ p4)) → p3)) ∨ (p4 ∧ True)) ∨ p2) ∨ (((p2 ∧ False) → p4) ∨ p5)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46986855170007852273681391129 : ((((((p1 ∨ ((((p2 ∨ p1) ∨ p3) ∨ (p4 → (p5 ∧ p4))) → p1)) → p3) ∨ ((p3 → False) ∨ (p5 → True))) → p3) ∨ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52365256739695614246481434485 : ((((p5 → (False ∨ ((p4 → (p2 ∨ p2)) ∨ (p3 ∧ p5)))) ∨ (True ∨ False)) ∧ (p2 ∨ ((p1 → (True → (p1 ∧ p2))) → (p3 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732550479523646739330520963993 : ((((p1 ∧ True) ∧ (p3 ∨ (p4 ∨ ((True → (p2 ∧ (True → ((p1 ∧ (True ∨ p5)) ∨ ((p4 → (p2 ∨ False)) ∨ True))))) → (p3 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37956021332571318978421352898 : (((((p3 ∨ (p1 ∧ (((p3 → ((p3 → (True ∨ False)) ∧ (p3 ∨ (p1 ∧ p2)))) ∨ (p1 → p2)) ∧ p2))) ∧ p1) ∨ (p1 → p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806499819391611290324262595852 : (((p4 → (((((((p1 ∧ p5) ∨ p5) ∨ (True ∧ (p2 → (p3 → (p1 ∨ (p4 ∨ p2)))))) ∧ (p5 → p4)) → p5) ∨ (False ∨ p3)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207292403662458469079523015627 : ((((True ∨ (p5 ∧ p4)) → False) ∨ False) → (p1 ∨ (((((p3 ∧ ((p1 → p5) → p1)) → p2) → (True ∧ p2)) ∧ (False ∨ True)) → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ (p5 ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41714959983904695158494713869 : ((((p5 → (True ∧ (p5 ∨ (p1 ∨ p3)))) → (True → ((p2 → (p4 ∧ (((False ∧ False) ∧ (p5 → p4)) → (p1 ∨ False)))) ∧ False))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227940216250544566181432686776 : ((p3 ∧ (p2 ∧ True)) ∨ ((p2 → False) ∨ (p4 → (((False → (p5 ∨ (p3 ∧ True))) → False) → ((p5 ∧ (True → (p3 ∨ p3))) ∧ (False ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p5 ∨ (p3 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (False → (p5 ∨ (p3 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : (False → (p5 ∨ (p3 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h10
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : (False → (p5 ∨ (p3 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h13
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172439453838883489344255800693 : (((((p4 → p2) → p3) ∧ False) ∨ (False ∨ (False ∨ (p3 ∧ ((p4 → False) → p3))))) ∨ (((p3 → True) ∨ ((p1 → (p5 ∧ p3)) → p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167178090460368478226342641079 : ((((p4 ∧ p5) → ((True → (p4 → p5)) ∨ ((p5 → p2) ∧ (False ∧ (p1 ∨ p4))))) ∨ p1) → ((p2 ∨ ((p2 ∨ p5) → (p5 ∨ True))) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44083420422813635935419936776 : (((((True ∨ True) ∧ (((p5 ∨ True) ∨ ((p1 → ((False ∨ p1) → ((True → p2) ∨ True))) ∧ p5)) → False)) ∧ (p5 → (p5 ∧ False))) → p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p5 ∨ True) ∨ ((p1 → ((False ∨ p1) → ((True → p2) ∨ True))) ∧ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : ((p5 ∨ True) ∨ ((p1 → ((False ∨ p1) → ((True → p2) ∨ True))) ∧ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167777886396457262824792350700 : ((((p3 ∨ ((p5 → p5) ∨ False)) ∨ (p3 ∧ ((p4 → p1) → p1))) → ((False ∧ p3) ∧ False)) → (p3 ∧ ((p1 ∨ ((p3 ∨ p2) → p1)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ ((p5 → p5) ∨ False)) ∨ (p3 ∧ ((p4 → p1) → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 ∨ ((p5 → p5) ∨ False)) ∨ (p3 ∧ ((p4 → p1) → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((p3 ∨ ((p5 → p5) ∨ False)) ∨ (p3 ∧ ((p4 → p1) → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340855719034734275304846023311 : (p2 → (((((False ∧ (p4 → p4)) ∨ False) → ((p3 → True) ∧ (p4 → (p5 ∨ ((p3 ∨ (True → p1)) → p2))))) → (p1 ∨ (p2 ∨ p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136663577971614405491369089197 : (((True ∨ (True ∧ p5)) → ((p5 ∨ (p5 ∧ p5)) ∨ (((True → (True ∧ False)) ∧ p3) ∨ (p2 ∧ ((p4 → p1) ∨ p1))))) ∨ (p3 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659010841817602782795608513514 : ((((p1 → (((p3 ∨ p4) → p4) → (p2 → ((p2 ∧ (p2 → (False ∨ p5))) → (p3 ∨ ((p5 ∨ p1) ∧ (p3 ∧ True))))))) ∨ (p1 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328314949007940416190804145512 : (True → ((p4 → (False ∨ (((p2 ∨ p2) ∨ ((False ∧ False) ∨ (p1 ∨ (p3 → p4)))) ∧ (False → (p4 ∧ False))))) ∨ ((False → (p5 → p3)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



