variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257368534409744904619166948143 : ((p2 ∨ p5) → ((((p3 ∧ p3) ∧ ((p5 → p1) ∧ p1)) ∨ ((True → (p4 → (p5 ∨ ((((p3 ∧ False) → p2) ∧ p5) ∨ p5)))) ∨ p2)) ∨ False)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3142151573602169668062900188 : ((False → p2) ∧ (((True → True) → ((p2 ∧ p4) ∨ (p2 ∨ ((p3 ∨ p3) ∧ p4)))) ∨ (((False ∧ (p5 ∨ (p3 ∨ False))) ∧ p3) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117397771975847170876962974229 : ((p1 ∧ (((p2 → p2) ∧ (p2 → ((((p4 ∧ ((True → False) ∨ ((p3 → True) ∧ p1))) → p2) ∨ (p2 ∧ False)) → p3))) ∨ False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347643263339251355948374446030 : (p3 → ((((p1 ∧ p1) → p1) ∨ p2) → ((((p1 → p5) → ((((p4 ∧ False) ∧ (p2 ∧ p3)) ∨ False) ∨ ((p4 ∨ p4) ∨ False))) ∨ False) ∨ p3))) := by
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
theorem thm_5_vars_311226756321448144432507292247 : (p2 ∨ ((p1 → p5) → (((((((p2 ∧ ((p1 ∨ (False → (p1 ∧ (True ∧ p1)))) ∨ True)) ∨ p1) ∨ True) ∧ p5) ∨ p5) ∨ True) ∧ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_134764527112722725471963291272 : ((((False → p2) → (((((((True → p3) → p1) ∧ p4) ∨ True) → (False ∨ ((False → p5) ∧ p2))) ∧ True) ∧ p3)) → p3) ∨ ((True ∨ p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322371697328260198501680906728 : (p5 ∨ (((((((False → (p4 → (p5 ∧ p5))) ∨ p1) ∨ p4) → ((p4 → (p4 ∨ p2)) → p3)) → p2) ∨ (True ∨ (p4 ∨ (p2 ∧ p5)))) ∨ p3)) := by
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
theorem thm_5_vars_111141613251408353087911555901 : ((((((p4 ∧ p1) ∨ p1) ∧ (p2 → p3)) ∧ (p5 ∨ ((((p5 → ((p5 ∧ (p5 → False)) ∨ p2)) ∧ True) → p5) → p3))) ∧ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139068790094657484029527090539 : ((((((((p2 → p5) ∨ p3) ∧ (False ∨ p2)) ∧ (p1 → p2)) ∨ (p1 ∧ (p3 → (p4 → p5)))) ∧ (p5 ∧ p4)) ∨ False) → ((p1 → p3) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h4.left
          let h14 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h4.left
          let h19 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h4.left
      let h24 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65265012693444832154288968601 : ((p3 ∨ ((p2 ∧ (((p1 ∨ (((p4 ∧ False) → (p3 → (p5 ∧ (p1 ∧ (p5 → p2))))) → p4)) ∧ p4) ∨ (False ∨ (p4 → p3)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318861814498758490820406539958 : (p4 ∨ (((p3 ∨ (False ∨ (True ∧ (p4 ∨ (p1 ∧ (((p4 → p2) → (False → p3)) → ((p1 → p3) ∨ p3))))))) → p3) ∨ (p5 → (p3 ∨ p5)))) := by
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
theorem thm_5_vars_322240312849553509529985806308 : (p5 ∨ ((((((True → True) ∨ (((True → (p5 ∨ p3)) ∧ (True → ((p1 → ((p1 ∧ p5) ∨ p1)) → True))) ∧ p3)) → p1) ∨ p2) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606718893538019749616074070692 : ((((((((p4 ∧ p4) ∧ ((p1 ∨ (p1 ∧ p2)) ∨ ((False ∨ p3) → ((p3 ∨ (p5 ∨ True)) ∧ p3)))) → p1) ∨ (False → p4)) ∧ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41840472712224354095478566377 : ((((p1 ∨ (False → p1)) ∧ (((p4 ∧ ((((p2 → True) ∧ p2) ∨ True) → p1)) ∨ p4) ∧ (False ∨ (p4 ∨ (True ∨ (p1 → p2)))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342480646450399179690344031511 : (p2 → ((((False ∨ p5) ∨ ((p1 ∨ p5) ∨ ((p3 ∨ p1) → False))) ∧ (p5 → p4)) ∨ (((p2 → p1) ∧ (((p5 ∨ p5) → p1) ∧ p5)) → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258918984610763386561942673024 : ((True → p2) → ((p1 ∧ p4) ∨ (((p1 ∨ False) ∧ p3) ∨ (p2 ∨ ((((True → (True → p3)) ∨ p2) ∨ False) → (p2 → ((p3 ∧ False) → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727186137354182642940767256965 : ((((False ∧ (False ∧ False)) ∨ ((p4 ∧ p5) ∨ ((False → ((((p2 ∧ (p2 ∧ ((p3 ∨ p4) ∧ False))) ∨ p5) ∨ True) → (p4 ∨ False))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172276003597126812002892217766 : ((((p1 ∨ p2) ∧ (False → (p3 ∨ (p1 ∧ p4)))) ∨ (False ∨ ((p4 → p2) ∧ True))) ∨ (p3 ∨ ((((False ∧ p4) ∧ (p4 ∧ True)) → p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776191996136917459709370085255 : (((p1 ∨ (((((p2 → (True ∨ (p5 → p2))) ∧ (p4 ∨ ((((False ∧ p1) ∧ p5) ∨ p4) ∨ p2))) ∨ (p5 ∧ p3)) ∨ (p5 → True)) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_472272540216224603788927758463 : (((((p2 ∨ p2) → ((True ∨ (p3 ∧ p4)) ∧ ((p5 ∧ False) ∨ False))) ∨ ((((p2 ∨ p3) ∨ ((p1 ∧ False) ∧ p1)) ∧ True) → (True ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260907303590534052858466713383 : ((p4 → False) → ((((((True ∨ True) ∧ p2) ∨ ((p1 → p2) → (p2 → p5))) → p5) → (p3 ∨ (True ∧ p5))) ∨ (False → (p3 ∨ (p4 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314663136062888908871338458302 : (p3 ∨ ((p4 ∧ ((p2 → ((((True ∧ (p4 → (p5 ∧ p3))) ∧ p3) ∨ p1) ∨ p1)) ∨ p3)) ∨ (((p5 ∧ p3) ∨ True) ∨ ((p1 ∧ True) ∨ p4)))) := by
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
theorem thm_5_vars_184797314966610317080162887457 : (((p1 ∧ ((p4 ∨ p5) ∧ False)) ∨ (p4 ∨ ((p1 ∧ False) → p3))) ∨ ((((p3 → True) → ((p2 ∧ (p4 → p1)) ∨ (p4 → True))) → p3) ∨ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183866425893570855723067146898 : ((((p1 ∨ (p4 ∧ (p2 ∨ p3))) ∨ ((p2 → p2) ∧ True)) ∧ p4) ∨ (((p3 → ((p5 → (p1 ∨ (p2 ∨ (False → p2)))) ∨ p2)) ∧ p5) → p5)) := by
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
theorem thm_5_vars_199654678220385661446179036872 : ((((False ∧ p3) ∧ ((p5 ∧ p4) ∧ False)) → p2) → (p5 → (((p3 ∨ (p1 ∨ False)) → p1) ∨ ((p3 ∨ (p1 ∧ p1)) → ((p5 ∨ p5) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617628027176125196754977358723 : (((((((p5 ∨ False) → (p5 → p5)) ∧ p4) ∨ ((p2 ∧ p1) ∨ (p4 ∧ ((((p1 → p1) → (p4 ∧ (True ∨ True))) ∨ p2) → p3)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303920670728977995617345874159 : (p1 ∨ (((((((p2 ∨ True) ∧ p4) ∧ False) ∧ True) ∧ (p1 ∧ p3)) ∨ ((p1 ∨ (((p1 ∧ p5) → (p2 ∧ (False → p5))) ∨ True)) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178664494427133573772485198154 : ((((p3 ∧ True) ∨ (p5 ∨ p2)) ∧ (p2 ∧ ((p5 → (p2 → p5)) ∨ p3))) ∨ (((p5 ∨ (p3 ∧ p2)) ∨ (p1 → ((p4 ∨ p5) → True))) ∨ p2)) := by
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
theorem thm_5_vars_675730156832739154807094075208 : (((((p2 ∨ (((p1 ∧ p5) → p1) ∧ (p3 → ((p3 ∧ p2) ∨ (False ∨ False))))) ∧ ((True ∧ p1) ∧ p1)) ∧ (p4 ∧ (True → (True ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241296052863376682330841751099 : ((False → True) ∧ (((((p2 ∨ p2) ∧ ((False ∧ (p2 → p3)) → p3)) ∧ p5) → False) ∨ (p2 → (p1 → (p2 → (p3 ∨ ((False ∨ p1) ∧ p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314770384701476191950419052172 : (p3 ∨ (((((p1 → p4) ∧ p4) ∧ (((p2 ∨ False) ∨ True) → (p4 ∧ True))) → p4) → (((p4 → (p1 ∧ p1)) ∧ (True ∨ p5)) ∨ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37323724497059169213123969834 : ((((((p1 → ((True ∨ ((((False → p3) ∧ p2) ∨ ((True ∨ True) ∨ (p4 → p1))) ∨ p2)) → (p2 → p5))) ∧ p4) ∧ False) ∨ p5) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637127627279430261906391661586 : (((((((p5 ∧ (p4 ∨ True)) ∨ (True → False)) ∧ ((p5 ∧ False) ∨ p3)) ∨ (((p5 → p1) ∧ (False ∧ p3)) → (p2 ∧ (p1 ∨ False)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190733345545960754534400461891 : ((((p4 ∧ p3) → (p1 → (p5 ∨ p4))) ∧ (p5 → p1)) ∨ ((p3 ∨ (True → ((p3 ∧ (((True → True) ∧ (p2 ∨ p5)) ∧ p5)) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317077960567442976673590314244 : (p3 ∨ (p4 → (p1 ∨ ((p4 ∧ (((False ∧ (p5 ∧ p3)) ∧ (False ∨ (p1 ∨ p2))) ∨ (True ∨ (((p5 ∧ p5) ∨ p3) ∨ (p5 ∨ p3))))) ∨ True)))) := by
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
theorem thm_5_vars_113320202023958706183192330882 : (((((True ∨ p2) ∨ p3) → ((True ∨ (((p3 ∨ p5) ∨ p1) ∨ (True → ((p2 ∧ (False → p5)) ∨ p3)))) → p2)) ∧ (p3 ∧ p3)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64372437626058131472707445963 : ((p1 ∨ (((p2 → False) ∨ (p1 ∧ ((True → p1) ∨ (p2 ∧ (p1 ∨ ((p5 ∧ ((False ∨ True) ∧ False)) → (True ∨ (p4 → p3)))))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303000308216170065310309981117 : (False ∨ (p1 → ((((p3 ∧ (((((False ∨ p5) → p3) ∨ False) ∧ (p4 ∨ p3)) → (p4 ∨ p1))) ∧ False) ∧ p2) ∨ (((True ∨ p2) ∧ p1) ∨ True)))) := by
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
theorem thm_5_vars_57038416207316828576476291163 : (((p2 → (False → p2)) ∧ ((((p5 ∨ True) → ((((p4 → True) → (True ∨ False)) ∧ p1) ∨ ((p1 ∧ (p3 ∨ p5)) ∧ p3))) ∨ p1) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_495033656826740191113054945606 : ((((p4 ∧ ((p5 ∧ True) → p1)) → ((p5 ∧ (p3 ∧ False)) ∨ (p4 → ((p5 ∨ (p5 ∨ ((p1 ∧ (p4 ∧ (p4 ∨ p1))) ∨ p4))) ∨ False)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159040152396277178319633187303 : ((p5 ∨ (((((p3 ∨ (True → (p5 ∧ p5))) ∧ True) ∧ (p5 → (False ∨ (p4 ∧ p4)))) ∨ p2) ∧ p3)) ∨ (True ∧ (True ∧ (True ∨ (False ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254482249164947442699364872418 : ((p3 ∧ True) → (((p5 ∨ p2) ∧ p5) ∨ (True → (p4 → (p2 ∨ ((True → ((p1 ∨ p4) ∨ ((False ∧ p4) → ((False ∧ p1) ∧ p4)))) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321505118849704610331278314294 : (p4 ∨ (p1 → (((p1 ∧ p3) ∨ p5) ∨ ((((((p1 → p4) ∨ (p5 → p2)) ∧ (((p5 ∨ p5) ∧ p1) → False)) → p3) ∨ p2) ∨ (p1 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41311698101597212449382240555 : (((((((p5 ∨ False) ∧ (True ∨ (p5 ∧ (p1 → True)))) → (False ∧ False)) ∧ (p1 → p2)) ∧ (((p4 ∧ p3) → p4) ∧ (p3 ∨ p1))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351210886856534764068417684164 : (p4 → (((True → (((((False ∨ p1) ∧ (p4 ∨ (p4 ∧ (p1 ∧ False)))) → (False ∧ (p4 → p3))) ∧ p2) → False)) ∧ p3) ∨ ((p4 → True) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42655544433931207061407120623 : (((p4 ∨ ((((((p4 → p2) → p3) ∨ (p1 → True)) ∧ (p4 ∨ ((p5 ∧ (p5 ∧ p5)) ∧ p3))) ∧ (p5 ∧ p1)) ∨ (p1 → p1))) ∨ p3) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62389469508543634665264223104 : ((p3 ∧ ((p1 ∨ (((p5 ∨ p4) → p1) ∨ ((p1 ∨ (p5 ∧ p4)) ∧ p1))) ∨ (p2 ∨ (p4 ∧ (p1 → ((False → p2) ∧ (p1 ∨ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46630553651026355825450243433 : (((p4 ∧ ((p5 ∧ p3) ∧ ((p4 ∨ p4) ∧ ((((p1 → (p4 ∨ False)) → p1) ∧ (False ∧ ((p1 ∨ p4) → p2))) ∨ p2)))) ∧ (p5 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179909921734197224946320831873 : ((((((p5 ∨ p3) → p1) → (p3 ∨ ((p4 ∨ p5) ∨ p1))) ∨ True) ∨ p4) → ((True ∧ p5) ∨ (((p5 ∧ p5) ∧ (True ∧ (p3 ∨ p1))) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200384422787677696885597115280 : (((True ∧ p1) ∨ (False → ((False ∨ p3) ∨ p2))) → (True ∧ (True ∧ (((p5 ∧ False) ∧ (False ∨ p4)) ∨ ((True → (True ∧ p3)) ∨ (True ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47879432736770592395843400191 : ((((p5 → (((((False ∧ True) ∨ p4) ∧ ((False → p4) → ((p5 ∨ p2) ∨ p5))) → p3) ∨ (p1 ∨ p2))) ∧ (p5 ∨ p4)) → (p2 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705238779946898763027096907636 : (((((p3 ∧ (p3 → ((p5 ∧ p1) → False))) ∧ p2) ∧ (((p5 → (p5 → (p3 ∧ p3))) ∧ ((True → ((True ∨ p5) → p1)) ∨ True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338902421043629449893148908292 : (p1 → ((p4 ∧ p4) → ((p1 → ((p3 ∨ p5) ∧ ((p3 ∧ p3) ∧ (p3 ∧ ((p4 ∧ ((p2 → False) → (False → p4))) ∧ True))))) ∨ (p1 ∨ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315718255843672989922529397397 : (p3 ∨ ((True → p2) ∨ (((p1 ∨ (p3 → True)) → (p4 ∧ (p2 ∧ p4))) ∨ (p3 ∨ ((((True → p3) ∧ p5) → ((p2 ∧ p4) → p4)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713053512184088073710450516001 : ((((p4 ∧ ((p2 ∨ (p3 ∧ p1)) ∨ p4)) ∨ (((((p1 ∧ p3) ∨ p3) ∨ (True → (p5 → ((p5 ∧ False) ∨ (p5 → True))))) ∧ p3) → p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636187081224896770567105380161 : ((((((True ∧ ((p5 ∨ p2) → (p2 ∧ p3))) ∨ ((p2 ∨ ((True → p4) → False)) ∧ False)) ∨ ((False ∨ True) ∨ (p4 → (p1 ∨ False)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690774439702241278978271389950 : ((((((p4 → (p2 ∨ (((p3 ∨ p4) ∨ p2) ∨ p1))) ∧ ((p4 ∧ p1) ∨ p4)) → True) → (((p2 → (True → p5)) ∧ (False ∨ p3)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326905404374112558340833145806 : (True → ((((p4 → ((p2 ∧ p5) → ((p3 ∨ (False → (((False ∧ ((True ∧ p1) → p2)) ∨ False) ∧ p5))) ∨ (p1 ∨ p2)))) ∨ p5) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68925036844350461890210091500 : ((p4 → (p2 ∨ (p1 ∨ ((p2 → (((True ∧ p5) ∧ p1) → (False ∨ ((p3 → (True ∧ (p3 ∧ (p4 ∨ False)))) ∨ True)))) ∧ (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9075787797401879319377735053 : ((((((p3 ∨ False) → False) ∨ ((p5 → (p4 ∧ (p5 ∨ p3))) → (p3 ∨ p2))) → ((((p5 ∨ (True ∧ False)) ∨ True) ∨ p2) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65635523014587061645930987297 : ((p4 ∨ (((((p2 ∨ (p4 ∧ True)) → (p1 ∧ ((p2 ∧ (p1 → p3)) ∧ ((p4 ∨ p4) ∧ p4)))) → False) ∨ ((True ∨ p3) → p1)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200866386757449377055108904191 : ((True ∨ (p2 → (p4 ∧ ((p2 → False) → True)))) → (p4 → (((p3 ∧ (True ∧ p5)) ∨ (p4 ∧ ((True → p3) → p1))) → ((p4 ∨ False) ∨ p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65961471325807279407822540099 : ((p4 ∨ (p5 ∨ ((((p1 → (((True ∨ (((True ∧ (p4 ∨ p5)) ∧ (p1 ∧ False)) → True)) ∨ p5) → p5)) ∨ (p2 ∨ True)) ∨ True) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753802531687925377986821209108 : (((False ∧ ((p2 ∧ (False ∧ (False ∧ (p4 ∨ (p2 → (p3 ∨ p1)))))) ∧ (((True ∨ p4) → p1) → ((False ∨ p2) ∧ (p5 → (False → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207364153803475124677227550593 : ((((p5 ∨ p1) → (p5 → p5)) ∨ p5) → ((((False ∧ ((p1 → (p1 ∨ p3)) ∨ ((True ∧ p2) → (p5 ∨ p3)))) → p2) → (p2 ∧ p1)) ∨ True)) := by
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
theorem thm_5_vars_729495103752322750318616169659 : (((((False ∨ p5) ∨ p4) → ((p1 ∨ (((p3 → (p4 ∧ ((p1 ∧ (True ∧ True)) → False))) → False) ∨ (True ∨ (p5 → (p1 ∧ p2))))) ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
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
  case inr h5 =>
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
theorem thm_5_vars_184429508979505961902313330461 : ((((p4 ∧ (False ∨ p1)) ∧ ((p2 ∨ p4) → p4)) ∧ (p5 ∨ True)) ∨ (((((False ∨ (False ∧ p5)) ∨ (p1 ∨ p4)) ∨ (True ∨ p4)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348198767014109254241380617347 : (p3 → ((True → p3) → (p4 ∨ ((((p2 ∧ True) → (False → p4)) ∨ p4) → ((p2 → ((((p2 ∨ p1) ∧ p2) ∨ p4) → p5)) ∨ (p5 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257629797771877912795544647272 : ((p3 ∨ p2) → ((False ∧ (((p4 ∨ p5) ∧ ((p3 ∨ (p1 ∧ (p2 → True))) ∨ p2)) ∧ (p5 → False))) ∨ ((p3 → ((False → p4) ∨ True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49641871065264794800040582018 : (((((p2 → (True ∨ p4)) ∧ p5) ∨ (((p2 → ((p4 ∧ True) → p4)) ∧ True) → (p2 ∧ (True → (False ∨ p2))))) → ((p3 ∨ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116343320455995971285387374851 : ((((p2 ∧ False) ∨ p3) → (False ∧ (p1 ∨ (((((p3 ∨ (p2 ∨ (p1 ∨ ((p5 ∨ p4) ∨ True)))) → p3) ∨ False) ∧ p4) ∧ False)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356020898498295423357669590625 : (p5 → ((((((True → ((True ∨ (False ∧ p5)) ∨ p2)) ∨ (False ∧ False)) ∧ (p1 → p3)) → False) ∧ (p2 ∧ False)) ∨ (p2 ∨ ((p1 ∨ p5) ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112192299195696081028103411856 : (((p5 ∧ (p3 ∧ (((True ∧ (p2 ∨ ((False ∧ p3) ∨ p2))) → p1) → (((p2 → (p4 ∧ p3)) ∨ (True → p3)) → p2)))) ∨ True) ∨ (False ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61751673375876849880898349176 : ((p1 ∧ (p5 → ((p2 ∧ (((False ∧ True) ∧ p1) → ((p1 ∨ (((False → p4) → False) ∧ p2)) ∨ ((p2 → p3) ∧ p3)))) → (p4 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206062282441063332879637849969 : ((p3 ∧ (((p2 ∨ p3) ∨ p2) ∨ p1)) ∨ ((((True ∧ ((False → p3) ∨ (((p3 ∨ (p4 → p3)) ∨ p4) ∧ False))) ∨ (p4 ∧ True)) → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55670763192390065233366236937 : ((((p2 → (p3 → p5)) ∧ p5) ∧ ((((False → p5) ∨ (p1 ∧ (True ∨ (((p1 ∨ (False ∨ p4)) ∨ p2) → p4)))) → p3) ∨ (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654497464106525843434168093773 : (((((False ∧ (((p5 → (False ∨ (False ∧ ((False ∧ p3) → (p1 ∧ (((p5 ∧ p3) ∧ p5) ∨ p5)))))) ∧ p2) ∨ p2)) ∨ p1) ∨ (True ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307860447187831150987925710961 : (p1 ∨ (p5 → (((((p2 ∨ (p4 ∧ ((p2 ∨ p1) ∨ p4))) ∨ p4) ∧ (p5 → ((p2 ∧ p2) ∧ False))) → ((p5 ∧ p1) ∨ p4)) ∨ (p2 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351212783997957622643255489844 : (p4 → (((((((p4 → (p1 ∨ p1)) → (((p3 ∨ p4) → (p2 ∧ p3)) → p3)) ∨ (p3 → p5)) → True) → p5) ∨ True) ∨ (p1 ∨ (p1 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52609383488034382759841022464 : (((((p3 → p3) ∧ (p2 ∧ True)) ∨ (p2 ∨ ((p2 ∧ (p5 ∨ False)) ∨ True))) ∨ (p5 ∨ ((p5 ∨ ((p1 ∨ p1) → p3)) ∧ (False ∧ p1)))) ∨ False) := by
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
theorem thm_5_vars_42653933729515286196322854373 : (((p4 ∨ ((False → ((p3 ∨ p4) → ((p3 → (p1 → (p5 ∨ ((True → (p3 ∨ (p5 → p5))) ∨ (p5 ∧ p2))))) → p1))) → p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50654678528433000263964420352 : (((((p3 ∨ (True ∧ ((p2 ∨ p1) ∧ p5))) ∧ p3) ∧ ((p3 → True) → (True → ((p3 ∧ p4) ∧ p4)))) → ((p5 → (True → p1)) ∨ p4)) ∨ p2) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h19
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h26
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321206553478322198203154680053 : (p4 ∨ (p3 ∨ ((p3 ∧ p1) → (((False ∧ (p2 ∨ ((((p4 ∨ p3) ∧ p3) ∨ ((False → (p2 ∧ False)) ∧ p5)) ∨ p4))) ∨ (p5 → p1)) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611936999699668701359014744975 : (((((((p1 ∨ p4) → (p5 ∨ ((p1 ∨ (False ∧ (((p4 → p3) ∧ ((p4 ∨ p2) → p5)) ∧ True))) ∧ p2))) ∧ p5) ∧ (p3 ∧ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342140195118543134489179492522 : (p2 → (((((p4 ∧ (p5 ∧ ((False → p1) ∧ p2))) ∨ True) ∧ (p1 ∧ (False ∧ ((True → p3) ∧ p3)))) ∧ False) ∨ ((p2 ∧ p5) ∨ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149787644781007003327247480810 : ((False ∨ ((((p1 → p5) ∧ False) → (((p5 → p5) ∧ True) ∧ p1)) → (((False → p2) → (p5 ∧ True)) → False))) ∨ (((p2 → p4) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148174031981633652869943981654 : ((((((p5 ∧ ((((True ∨ True) ∧ p3) ∨ p2) ∨ (True → p5))) ∧ True) → p2) → p3) ∧ ((p1 → True) ∧ True)) ∨ (False ∨ (p2 ∨ (p5 → True)))) := by
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
theorem thm_5_vars_669042914584417337741126784210 : ((((((p5 → ((p4 ∨ (p3 ∧ (p3 ∨ (p2 ∨ ((False → (p5 ∨ (p2 → p4))) ∧ p3))))) ∨ p4)) ∨ p3) → p5) ∨ (p4 ∨ (False → p2))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603980584093882368558175631340 : ((((p5 ∨ (((p5 ∨ p1) → ((p5 ∧ (((p2 ∧ p5) ∧ (p3 ∧ p4)) → p2)) ∨ (((p3 ∨ (False ∧ p2)) ∧ p5) ∧ p3))) → p5)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738856479159826833143223446043 : ((((p3 ∧ True) ∨ ((p5 ∨ (p4 ∨ ((p4 ∧ ((p4 ∨ False) ∨ p2)) → (((((True ∧ p4) → p4) ∨ (p5 ∧ False)) → p1) ∧ p3)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42862608019813979330953576960 : (((p2 → (((p5 ∧ (p5 ∧ p5)) ∧ False) ∨ ((((p2 ∧ p4) ∧ (p1 → ((True → p3) → p1))) → p2) → ((p4 ∨ p2) ∨ p2)))) ∨ p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352486318920864305054200736060 : (p4 → ((p2 ∨ (False ∨ p3)) → ((p2 ∨ (True ∧ (p5 ∨ ((((True ∧ p1) ∨ p4) → p1) ∨ (p1 ∨ (((p1 → p2) → p5) → p1)))))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319634505206685130089429514860 : (p4 ∨ ((((p4 ∨ (p4 → (p3 → p2))) → p3) → p5) ∨ (p5 ∨ (((p2 ∧ p5) → (p4 ∨ p5)) → (((p2 ∨ (p2 ∧ p4)) ∨ p5) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_708510250053708302695190030818 : ((((((((p1 ∨ p1) ∧ p5) ∧ p3) → True) ∨ p4) → (True ∧ ((True → (p3 ∧ p5)) ∨ (((p4 ∨ p3) ∨ ((True ∨ p5) ∨ False)) ∨ p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136634113847682735187898907680 : ((((p5 ∨ p2) ∨ p1) → ((((p1 → p4) → (((p2 ∧ p2) ∧ ((p2 → p2) → (p5 ∧ p1))) ∨ p2)) ∨ p4) ∨ p3)) ∨ (p4 → (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166189738387589401659800618138 : ((p1 ∧ ((True ∧ ((((p5 → p3) → ((False ∧ False) ∧ p5)) ∧ False) ∨ p2)) ∨ (p1 ∨ False))) ∨ (True ∧ ((p1 → (True → True)) ∨ (p3 ∧ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137170276512549867871409255746 : ((False ∧ ((((p4 ∨ p4) ∨ p5) ∧ (((p4 ∧ p5) → (p1 → (p4 → (False ∨ True)))) ∨ (False ∧ True))) → (p3 ∧ p5))) ∨ ((p3 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111028197204925711250975980096 : ((((p2 ∨ ((((((p5 ∨ p1) ∨ p4) ∨ False) ∨ (p2 → (p3 ∨ p3))) → (False ∨ p1)) ∧ p2)) → ((False ∨ False) ∧ p4)) ∧ False) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80098283520062749107003226661 : ((((((((p1 ∨ False) ∧ (False ∨ (((p4 ∨ p5) ∨ p5) → p1))) ∨ p1) ∧ p2) → ((True ∧ (p3 ∧ p4)) ∨ p5)) ∨ True) → (False ∧ p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p1 ∨ False) ∧ (False ∨ (((p4 ∨ p5) ∨ p5) → p1))) ∨ p1) ∧ p2) → ((True ∧ (p3 ∧ p4)) ∨ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111900046390556127497330102347 : (((((p4 → ((p1 ∨ (p1 ∨ (True → p5))) → ((True ∨ p3) ∨ p4))) ∨ p4) → ((p3 → False) → (p4 ∧ (True → p5)))) ∨ True) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



