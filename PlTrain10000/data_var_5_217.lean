variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328804275009806118604813147829 : (True → ((p1 ∨ (((p5 ∧ p4) ∨ (p2 ∧ (False ∧ True))) ∧ p2)) ∨ (((p2 ∨ (p2 ∨ (True → True))) → ((p1 → True) ∨ True)) → (p1 → True)))) := by
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
theorem thm_5_vars_177688488268877890778202702631 : ((((((p3 ∧ (p3 → (p3 → False))) ∨ p4) ∨ p4) ∧ (True → False)) ∧ p2) ∨ (p5 ∨ ((((False → ((True ∧ True) ∨ p4)) → p5) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625775128971750925074202909530 : ((((p1 → (p1 ∧ ((((((p3 ∨ (p4 ∨ False)) ∧ (p1 → p1)) → p5) → p3) ∨ (p1 → p1)) ∨ ((p4 → False) → (True ∨ False))))) ∨ False) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180711104233268300987693204617 : ((((True → False) ∧ (p2 → True)) ∧ ((False ∨ ((p1 ∨ True) ∧ True)) ∨ p5)) → (p1 ∨ ((False ∧ ((False ∧ (False ∧ False)) ∧ False)) ∨ (False → p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685796821337947446202009263462 : (((((((((p5 → (False ∧ p1)) ∨ (p2 ∨ p5)) ∨ (p4 ∨ p4)) ∧ p1) ∨ (p3 → p2)) → p1) → (False ∨ (True → ((p3 ∨ p2) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47389984401422861701359873710 : ((((p1 → False) → ((True ∧ (p4 ∨ p2)) → (((p2 ∧ p2) ∨ (p2 ∨ (p4 → p1))) → (p3 → (p1 ∨ (False ∨ p1)))))) ∨ (True ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788355540584517451713129312497 : (((p5 ∨ (((p4 ∧ (((p4 ∧ ((p4 → True) → p1)) ∧ p2) ∨ ((p2 → (p3 ∧ ((p2 → p5) ∨ (p3 ∨ p3)))) → p2))) → p5) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_206132324261060289716594376376 : ((p4 ∧ (p2 ∧ ((p1 → p1) → p4))) ∨ (((p4 ∧ p3) → (p5 ∧ p4)) → (((p5 → p3) ∨ (True ∧ (p5 → p5))) ∨ (p4 ∨ (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_165546458805056750399743736113 : ((((p2 ∧ ((True → False) ∧ True)) ∨ (p1 ∨ p2)) ∧ (p3 ∧ ((False → (p2 ∧ p3)) ∨ p3))) ∨ ((False ∧ ((p2 → p3) ∧ (False ∧ p2))) → p1)) := by
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
theorem thm_5_vars_164964529075594183631048088705 : (((((((p4 ∧ True) → (p5 ∧ p1)) ∧ p3) ∧ (p1 ∧ (True ∧ p3))) ∧ (p4 → p1)) → p5) ∨ (p2 ∨ ((True ∧ (True ∧ True)) ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203031735563128050897446336586 : (((p5 ∧ p4) → ((False ∧ True) → False)) ∧ (p1 → ((((False → p4) → (((p2 ∨ (False → (p2 ∨ p3))) ∨ p2) ∧ (p1 → p4))) → p4) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194681398090904655493021261372 : ((((p1 → (p1 → p1)) → (p5 ∨ False)) ∨ True) ∧ (True → (p1 ∨ ((True ∨ p3) ∧ (False → ((p3 → (p3 ∨ p3)) → ((False → True) ∧ p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705993201362179798575212506844 : (((((p2 ∧ p5) ∧ (p1 ∨ (p5 ∨ (False ∨ p1)))) ∧ ((False → p1) ∧ (p1 → (p5 → ((p3 → p2) ∧ ((True → (p1 → p2)) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244069965135960000469092351803 : ((True ∧ p3) ∨ ((p2 ∧ ((p4 ∧ p1) ∧ (True → ((p4 ∨ (p5 ∨ (((p1 ∨ False) → p3) → (True ∨ p2)))) ∧ ((p4 → p2) ∨ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52907577355876579163831783602 : (((p2 → ((((True ∨ p3) ∨ p4) ∧ (((False ∧ p3) ∧ p1) → p5)) ∧ False)) → ((((True ∨ True) → (p3 → (p2 ∨ True))) → p3) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48104814576119384413801141587 : (((((p2 → False) ∧ (p4 ∨ p2)) ∨ ((p3 ∨ ((True ∨ p4) → (((p2 ∨ (p5 ∧ p1)) ∨ False) ∨ (True ∨ p1)))) → False)) → (p4 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183833151294118346570284337964 : ((((p1 → (True ∧ ((False ∧ (p1 ∧ True)) ∧ p5))) → False) ∧ p5) ∨ (p3 ∨ (p2 → ((p1 ∧ p1) → ((p4 ∧ (p4 → True)) ∨ (True ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53791796976638016014895057513 : ((((((p2 → (p5 → p3)) ∧ (p1 → True)) ∨ p3) → p4) ∨ (((p5 ∧ (True ∨ (((p4 → p1) ∧ p3) → p3))) ∧ (p2 ∧ p5)) → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133624455150815547334528881394 : (((((p4 ∧ (False ∨ p2)) → (True → (p1 ∨ (p4 → (p4 → (((p2 → p3) ∨ True) ∧ (p5 → True))))))) → p2) ∧ p1) ∨ (False → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49958695401309502942672970005 : (((((p2 → (False ∨ p4)) → (((p3 → p2) → (p2 ∧ (p4 ∨ (p2 ∧ p2)))) → p3)) → (p4 ∧ p3)) ∧ ((p2 ∧ p1) → (p3 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342116881038099371576146079486 : (p2 → (((False → (p3 ∧ ((p4 ∧ p5) ∧ True))) → ((((p4 ∨ (p2 ∨ p3)) ∨ p5) ∧ p1) ∨ (p4 → p2))) ∧ (False → ((False → False) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2514205407361583380589391225 : (((((p2 ∧ (p3 ∧ True)) ∧ p5) ∧ p1) → p5) ∧ (((p3 ∧ (((p1 ∧ (p1 ∧ True)) → p2) ∨ p3)) ∨ ((p4 ∨ p1) ∨ True)) ∨ p5)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135507409219332829311984466612 : (((p5 ∨ ((p2 ∨ (((p5 → p3) → p2) ∨ ((p3 → ((p4 → False) ∨ p2)) ∧ False))) → p2)) → (p5 → (False ∨ p1))) ∨ ((False ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225156468991030955898662568979 : (((p3 ∧ p4) ∧ True) ∨ (((p2 → ((False ∨ p2) ∧ ((True ∧ p4) ∨ (p5 ∨ (p5 → (((True → False) ∨ p5) ∨ p4)))))) ∨ p3) ∨ (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120559256599051829459472518720 : (((((p3 ∨ ((((p4 ∨ (p2 ∨ True)) → True) → ((p4 ∨ p3) ∧ False)) ∨ False)) ∧ (True ∨ ((False → p2) → p4))) ∨ False) ∨ False) → (p4 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h11 =>
            -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
            have h12 : ((p4 ∨ (p2 ∨ True)) → True) := by
              -- Implications on the right can always be decomposed.
              intro h13
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h10, we can now drive its conclusion.
            let h14 := h10 h12
            -- We need to get the right conjuct of h14 based on <expert-advice>.
            let h15 := h14.right
            -- False on the left can always be used.
            apply False.elim h15
          case inr h16 =>
            -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
            have h17 : ((p4 ∨ (p2 ∨ True)) → True) := by
              -- Implications on the right can always be decomposed.
              intro h18
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h10, we can now drive its conclusion.
            let h19 := h10 h17
            -- We need to get the right conjuct of h19 based on <expert-advice>.
            let h20 := h19.right
            -- False on the left can always be used.
            apply False.elim h20
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767735372029679409108162331999 : (((p5 ∧ (((((p5 → (p5 ∧ p1)) → ((p3 ∧ (((p2 → False) ∧ ((False ∧ p4) ∨ (p2 → True))) → False)) ∨ p4)) → p5) ∧ p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149418901791513899466509611422 : ((True ∧ (((p2 → False) ∨ True) ∧ ((p1 ∧ p1) ∨ (((p1 ∨ p2) ∧ ((p4 → True) ∧ (p2 → False))) ∧ p1)))) ∨ ((p5 → p5) → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720148363793062584807176449294 : (((((p4 ∧ (p5 ∨ p2)) ∧ p4) → ((((((True ∨ (p4 ∧ p3)) ∨ True) → p3) ∧ p2) ∧ (p3 ∨ (((p4 → p2) → p4) → p3))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238239287883670807657441750736 : ((True ∨ p5) ∧ (((p4 ∨ p4) ∧ (p5 ∧ ((((p2 ∨ ((p1 → p1) → (False ∨ (p4 ∨ p3)))) ∨ (False ∧ p4)) ∧ (p4 ∨ p5)) ∨ p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181342938691139318060990980993 : ((False ∨ ((((p2 → (p1 ∧ (p1 ∨ p2))) ∨ (p5 → p5)) ∧ True) ∨ True)) → (p1 ∨ ((True ∧ ((p4 → (p3 ∨ p5)) ∨ (p3 → True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
theorem thm_5_vars_317865394177392632078129958868 : (p4 ∨ (((p5 ∨ p2) ∨ (p1 ∨ ((p3 ∨ (p4 → p5)) → (p5 ∨ ((p2 ∨ ((p5 → p2) ∧ (((p2 ∧ p5) ∧ p4) ∨ False))) → p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666178340279584440310800995645 : ((((((((p2 ∧ False) ∨ False) ∨ ((p4 ∨ p5) → p5)) ∧ ((((p3 ∨ p3) ∨ True) ∧ True) ∨ False)) ∨ (True → True)) ∧ ((p1 ∧ False) ∨ True)) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107869655939428201371105708543 : (((p2 ∨ p2) ∨ (p5 → ((p3 ∧ (((p4 ∧ ((False ∧ p3) ∨ p2)) ∨ p3) → False)) ∨ ((True ∨ p2) ∨ (p4 ∧ (p4 → p3)))))) ∧ (p2 → p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627839369042976028129377410266 : ((((((p1 → ((p3 ∧ (p2 ∧ True)) ∨ (((p3 ∧ p3) → p4) ∧ (p2 ∧ p5)))) → ((p1 ∧ True) ∨ ((p5 ∧ p5) ∨ p4))) ∧ p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238341457489488139508087346379 : ((False ∨ True) ∧ (False ∨ (((p1 ∨ (True → p2)) ∧ p3) → (((p3 ∨ p5) ∧ ((True ∧ (((True ∨ p1) → p5) → False)) → (p5 ∨ p1))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336453636525511369935165678711 : (p1 → ((True → (((((True → (True ∧ (False ∧ (True ∨ p3)))) → (p3 → p3)) ∧ (True ∨ p5)) ∧ p2) → (p5 ∨ (p5 ∧ (p2 → p3))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254600711024192937900198501872 : ((p3 ∧ p1) → ((p1 ∨ (((p3 → p3) ∨ p5) ∧ True)) → (((True → ((p1 → False) ∨ ((False ∨ p5) ∧ False))) → False) ∧ (True ∨ (p2 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h24 := h3 h23
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- False on the left can always be used.
        apply False.elim h27
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h31 =>
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h30
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h1.left
      let h35 := h1.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h36 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h37 := h3 h36
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h39 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h40 := h38 h39
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h44 =>
          -- False on the left can always be used.
          apply False.elim h44
        case inr h45 =>
          -- False on the left can always be used.
          apply False.elim h43
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h46 =>
    -- Conjunctions on the left can always be decomposed.
    let h47 := h1.left
    let h48 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h49 =>
    -- Conjunctions on the left can always be decomposed.
    let h50 := h49.left
    let h51 := h49.right
    -- Disjunctions on the left can always be decomposed.
    cases h50
    case inl h52 =>
      -- Conjunctions on the left can always be decomposed.
      let h53 := h1.left
      let h54 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h1.left
      let h57 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119617743112875216491656837176 : ((p5 → (p2 → (((p1 ∨ p3) ∧ p4) ∧ ((((p3 ∧ p1) ∨ (((False ∧ (p2 → (p1 ∨ p1))) ∧ False) ∨ p3)) → p3) → p4)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53804457777529680977681498705 : ((((p2 ∧ ((p1 ∨ p2) → (p1 ∨ (p5 ∨ p2)))) → p5) ∨ (p1 ∨ (p1 ∨ (True ∧ ((((p3 ∨ p1) ∧ False) ∧ p1) ∨ (True ∨ p2)))))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176114403828546160066158226983 : ((((p4 → p4) ∧ ((p3 ∨ p3) → (p2 ∧ ((p2 ∨ p3) ∨ p4)))) → True) ∧ ((False ∧ (False ∧ ((p3 ∧ (p5 ∧ p3)) ∨ (True ∨ p3)))) ∨ True)) := by
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
theorem thm_5_vars_799604441951973873182461818114 : (((p1 → (p5 ∨ ((((p4 → ((p5 → (((p4 → p5) → (((True ∨ p5) → p4) → False)) → (p3 ∨ p4))) ∧ p5)) ∨ p1) → p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52813873916827650377926829225 : ((((p3 ∨ (p2 ∨ (p4 ∧ (p3 → False)))) → (((True → p3) ∨ p4) → p1)) → (((((True ∨ p5) ∨ (False → False)) ∧ True) → p1) → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True ∨ p5) ∨ (False → False)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150510674479491003755061883607 : (((((p5 → ((p2 ∨ (p5 ∧ p4)) → p1)) ∧ (p4 ∧ (False → p4))) ∧ ((p3 → False) → (p1 → False))) ∧ p5) → ((False ∨ True) → (p3 ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h13
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (p2 ∨ (p5 ∧ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53089156887342662071784192310 : (((p1 ∨ (((True ∧ ((p4 ∨ p3) ∨ True)) ∧ p4) ∧ (True → False))) ∧ ((p1 ∧ (((p5 ∧ True) ∨ (p4 ∨ p1)) ∧ p3)) → (p1 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652302778391254399164722649473 : ((((p3 ∧ ((p3 ∨ p3) ∨ (((((True → True) ∧ p2) ∧ p2) ∨ True) ∧ (True → (((p3 ∧ (False → p2)) ∧ p2) → p3))))) ∧ (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112458960433994763664011416034 : ((((((p4 ∧ (((p3 ∧ ((False ∨ p1) ∧ (p1 ∧ p2))) ∨ p1) ∨ p1)) → False) ∨ (((True ∨ p2) → p5) → p3)) ∨ False) → p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147116592440579585021176764805 : ((((True ∧ p1) ∨ ((p1 ∧ p3) ∧ ((p4 ∨ (True ∨ ((p1 → p5) → (p4 ∨ (p5 ∧ True))))) ∧ p5))) ∧ p1) ∨ (False → (p1 ∨ (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301193438711662637933125816096 : (False ∨ ((p2 ∨ ((False ∧ True) → (p3 ∨ (p5 ∧ False)))) → (p4 → (p5 ∨ (((p4 → ((True ∨ True) ∧ p1)) → False) ∨ ((False → False) → p4)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3267555328653960859706060097 : ((p1 → p4) ∨ ((((True → p5) ∧ p1) → True) → (p5 → (((p5 ∧ (p4 ∨ (p2 ∨ ((False ∨ p3) → p5)))) ∨ p3) ∨ (p4 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157480960946010865270608311892 : ((((p2 → ((False ∧ (p5 ∧ p4)) ∨ (p3 ∧ ((p5 ∨ p4) ∧ p2)))) → (p3 ∧ p5)) ∨ (p5 → True)) ∨ (False ∨ (((p1 ∨ p3) ∨ p2) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57272751085936670836978713855 : ((((p3 ∨ p5) → p5) ∨ ((p4 ∨ (p3 ∨ ((p2 → p4) ∨ (p2 ∨ p5)))) → (((p2 ∧ True) ∨ (False ∨ (True → (p2 ∧ False)))) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19677508690080812198184744691 : (((p5 ∨ ((True ∨ p1) → (p2 ∧ (p1 → ((((p5 ∨ p1) ∧ p4) ∧ p2) → p5))))) ∨ (((True ∧ (p5 ∨ (True → True))) ∨ True) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_727918576440327912374091626752 : ((((p2 ∨ (p3 ∨ p3)) ∨ ((p2 ∧ ((False ∨ ((((p1 ∨ (p4 ∧ False)) ∨ p3) ∨ (p5 ∧ True)) ∨ (False ∨ (p1 → p1)))) → False)) → p4)) ∨ p2) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ ((((p1 ∨ (p4 ∧ False)) ∨ p3) ∨ (p5 ∧ True)) ∨ (False ∨ (p1 → p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114664106093119236187273389024 : (((((p3 → True) ∧ p5) → ((p2 ∧ ((p2 ∧ ((p4 ∨ p1) → p4)) → p3)) → p3)) ∨ (p1 ∧ ((p1 ∨ (p5 ∨ True)) ∧ p4))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133555982232759330041468907731 : (((((((p3 ∧ p4) → True) ∧ (p5 → (((p3 ∨ True) → (((True → p1) → p1) ∨ False)) → p3))) ∧ p3) ∨ p5) ∧ False) ∨ ((p3 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55530613595146820128888456387 : ((((p2 ∨ p1) → ((p2 → p5) → p3)) → ((True ∧ ((True → p1) → ((p1 ∧ ((False ∨ (p2 → (p1 ∧ p5))) → False)) → False))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219810988472093000306495172747 : ((p2 → (p4 → (p4 → p1))) → (p1 → (((p3 ∨ ((((p4 ∨ ((p4 → p5) ∧ (p4 → True))) ∨ p4) ∨ p5) ∧ (p3 ∧ True))) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649617838022460500000173886338 : ((((((((p3 ∧ (True → p5)) ∧ ((True → p5) ∨ False)) ∧ True) ∧ (p4 ∧ (False ∨ ((p3 ∧ p2) → p3)))) ∨ (True ∧ False)) ∧ (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261630747711870484957053959352 : ((p5 → p5) → ((p4 ∨ (p5 → (((p3 ∧ p5) ∧ p4) ∨ (((p4 ∧ (p2 ∨ p4)) ∧ True) → ((p2 ∧ (p5 → p3)) ∨ p4))))) ∨ (p5 ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324508426502206010908660476305 : (p5 ∨ ((False ∨ ((p5 ∨ False) → False)) ∨ ((False ∧ (p2 ∧ False)) ∨ (((False ∧ ((True ∨ p2) → True)) → p3) → ((p4 → True) ∨ (p4 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37743812947982706914498261287 : ((((((False → p1) ∨ ((True ∨ p4) ∧ (p1 ∨ p1))) → (p2 ∧ (((False ∨ False) ∨ (p1 → (p2 ∧ p2))) → (p1 ∧ p3)))) → False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2996650009461711868831375570 : (((True → p4) ∧ p3) → (((((p3 → (p4 → p4)) ∨ ((p3 ∧ p5) ∧ ((p4 ∧ p3) ∨ False))) ∨ False) → (p5 ∧ (p1 → p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329154033154026072762383211983 : (True → (((p5 ∨ (False → False)) ∨ p5) → (((False ∨ p1) ∨ (((((False ∨ False) ∨ p1) ∧ p3) ∨ ((False ∧ True) ∨ (p4 → True))) ∧ p5)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357974017858199880596722250917 : (p5 → (False ∨ (((p1 ∨ (((((False → p3) ∧ p4) ∨ (((p4 ∨ (p5 ∧ p1)) ∧ p4) ∧ p2)) ∨ p4) → False)) → (p2 ∧ (p3 ∧ p1))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147268570161364357118071874911 : ((((((p1 → (p3 → p5)) ∧ (p1 ∧ (p4 ∧ (p1 ∨ ((p3 ∧ p2) ∨ p3))))) ∧ (p4 → True)) ∨ True) ∨ p5) ∨ ((p3 ∨ (p1 ∧ False)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185070797432315935510818782572 : (((p4 ∧ p5) ∨ ((False ∧ True) ∨ (((p4 ∧ p5) → p1) ∨ p4))) ∨ (p3 ∨ ((((p5 ∧ (p2 → p2)) ∧ p4) ∨ (p1 ∧ (p4 → p1))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115021595122315501871629056516 : (((False ∨ (((False → (p1 ∨ (p5 → p3))) ∧ (p5 ∨ p1)) ∨ p3)) ∧ (p5 ∧ (False ∧ ((True → ((True ∨ p5) ∨ p2)) ∧ p5)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1509649908237637815896818949 : (((True → ((p4 ∨ p3) ∧ (((p2 ∨ p1) → (p3 ∨ p5)) ∧ (p3 ∧ False)))) → ((p5 → ((p4 → True) ∨ p4)) ∧ p3)) ∨ (False ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299306024677329746954798738181 : (False ∨ (((((p3 ∨ (p3 ∨ p5)) → (p3 ∧ p1)) ∧ False) ∨ (((True → p5) → ((False ∨ ((p5 ∧ (p3 ∧ p5)) ∨ p2)) → p2)) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451333979178923548386823704140 : ((((((((p3 → p3) ∧ ((p3 ∨ p3) ∧ ((p2 ∧ p5) ∧ (p4 → p4)))) → False) ∧ False) ∨ (p4 ∧ p3)) ∨ (p1 ∨ (p2 → (p2 ∨ p2)))) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51240089862394330725841785546 : (((((p4 ∧ p2) ∨ p2) ∨ ((p2 ∧ ((p1 ∧ (p4 → p4)) ∧ True)) ∨ (p5 ∨ (p5 → p5)))) ∨ ((p1 → (False → (p4 → p3))) → False)) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789091959493810743031621761856 : (((p5 ∨ ((((True ∨ p5) → p5) ∧ ((((p3 ∨ False) ∨ p2) ∧ p1) ∧ ((p5 ∧ (True ∨ (True ∧ p5))) ∨ True))) ∧ ((p3 ∨ p5) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136682065777909490299958903154 : (((p2 → (p1 ∨ True)) → ((False ∨ (p2 ∧ (p3 ∨ p1))) ∧ (p2 → ((p3 ∧ p4) → (p5 → ((p2 ∧ p5) ∨ True)))))) ∨ (p2 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187015627861151370714434186898 : (((p3 ∧ (p1 → p3)) → ((((True ∧ False) ∨ p3) → p5) ∧ p4)) → ((((p5 ∧ True) ∧ (p3 → p1)) ∧ ((False ∧ True) ∨ (p5 ∨ False))) → p5)) := by
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
  cases h4
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200577456957084487108059629176 : ((True ∧ ((p2 ∨ ((p2 ∨ p3) ∨ p4)) ∨ True)) → (False ∨ (((p4 → (((p2 → p5) ∧ (((p1 → True) ∨ True) ∧ p5)) → p5)) ∧ True) ∨ p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h11
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
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h17
          -- Implications on the right can always be decomposed.
          intro h18
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h22
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h26
          -- Implications on the right can always be decomposed.
          intro h27
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h32 =>
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h33 =>
            -- One of the premise coincides with the conclusion.
            exact h31
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h35
        -- Implications on the right can always be decomposed.
        intro h36
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h41 =>
          -- One of the premise coincides with the conclusion.
          exact h40
        case inr h42 =>
          -- One of the premise coincides with the conclusion.
          exact h40
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h43 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h44
    -- Implications on the right can always be decomposed.
    intro h45
    -- Conjunctions on the left can always be decomposed.
    let h46 := h45.left
    let h47 := h45.right
    -- Conjunctions on the left can always be decomposed.
    let h48 := h47.left
    let h49 := h47.right
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h50 =>
      -- One of the premise coincides with the conclusion.
      exact h49
    case inr h51 =>
      -- One of the premise coincides with the conclusion.
      exact h49
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148817191163649815803951004531 : ((((p1 → False) → (p2 ∧ (p2 ∧ p1))) → ((False ∨ ((p1 → False) ∨ p1)) ∨ (False ∨ ((False ∨ p5) → True)))) ∨ ((p2 → (p2 ∨ False)) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111833397062913455306115478450 : (((((((p1 ∧ (((False ∧ p3) → (p4 → (p5 ∨ p1))) → p3)) → p1) → (p3 ∨ p5)) ∨ True) ∨ ((p4 ∨ False) ∨ True)) ∨ p2) ∨ (p4 ∧ p3)) := by
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
theorem thm_5_vars_190434689742678424453011061376 : (((p5 ∨ (p3 → (p5 ∧ (p1 ∨ (False ∨ True))))) ∨ p3) ∨ ((False → (((p1 → ((False → p2) ∧ (p4 ∨ (p5 → p1)))) ∧ p4) ∨ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191761775426626944476457979883 : ((p1 ∨ ((p1 → (False → ((p3 → True) → p3))) ∧ p2)) ∨ ((((p5 → ((p4 ∨ (p1 ∨ (p2 ∨ p5))) → p4)) ∧ p2) → p4) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161831812716223244143421272312 : ((True → (((((((p4 → p3) ∧ (p5 → (False → p1))) ∧ p3) → (p5 → p1)) ∨ p1) ∨ p2) → False)) → (((p5 → (p2 ∨ p5)) → p1) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((((p4 → p3) ∧ (p5 → (False → p1))) ∧ p3) → (p5 → p1)) ∨ p1) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → (p2 ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h5
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_521928527956132655604869596414 : ((((p2 → p5) → (((((p4 ∧ (p2 ∨ True)) ∧ ((p5 ∧ (p5 ∨ ((False ∨ p2) ∧ p5))) ∨ (p1 → (False ∨ p2)))) ∨ True) ∨ p3) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778164692496994700136078299579 : (((p1 ∨ ((p2 → p3) ∨ ((False ∧ (True ∧ (p3 ∧ (((False ∧ True) ∧ (False ∧ (p4 ∧ ((p1 ∨ p1) ∨ p1)))) ∨ (p4 → p1))))) ∨ True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_962552540501226823018427868437 : ((((True → p4) ∧ (((((((p2 → (p2 ∨ (True → p3))) → ((True ∨ (False ∧ p1)) ∧ p4)) ∧ p5) → p3) ∧ (p3 → p1)) ∨ p3) ∨ p1)) → p4) ∧ True) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117526518687934451474882594973 : ((p2 ∧ ((((False ∧ p4) → p4) → (p5 ∧ (((True → p2) ∨ ((p1 ∧ p5) ∧ ((p2 ∧ True) ∨ False))) → (p4 ∧ p4)))) → False)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179341395625794853934901427673 : ((p1 ∨ ((p2 → p2) → ((p2 ∧ (p5 → (p3 ∧ p5))) → (False ∧ False)))) ∨ (((p4 → True) ∨ (True ∧ True)) → (p5 ∨ ((True ∧ False) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135367722814936242199413938487 : ((((((p4 → p5) ∧ ((p1 ∧ ((False ∨ (p2 → p2)) ∧ (p1 ∨ p1))) ∧ p3)) → False) ∧ p4) ∨ (p5 → (p4 ∨ p1))) ∨ (False → (p2 ∧ p1))) := by
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
theorem thm_5_vars_725036561224364189144389209346 : ((((False → (p3 ∧ True)) ∧ (p3 ∨ (((((False → p3) ∨ False) → p3) → ((False ∨ (p2 ∧ True)) ∨ (p2 ∧ True))) ∨ (p5 ∨ (p4 ∨ True))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_115311711430208159896746321433 : ((((True ∨ ((p4 ∨ p4) ∧ (p4 ∧ True))) → (False ∨ p5)) → (p5 ∨ ((p1 ∨ (p4 ∨ (((p2 ∨ p1) ∨ True) ∨ p2))) ∧ p2))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192055803681193242487800076514 : ((p3 → ((((p4 ∨ p2) ∧ p4) → (p1 ∨ p5)) ∨ p2)) ∨ ((p4 → (((p4 ∨ p1) → (p4 ∧ False)) → p3)) ∨ (p2 → (True → (p2 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113501107033197460222450432341 : ((((p2 ∧ ((p5 ∨ ((((p4 ∧ (True ∧ p4)) ∨ p1) ∧ True) → (p4 ∧ False))) ∨ p1)) → (True → (p4 ∧ p1))) ∨ (True → False)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703353828209929432976006551453 : ((((False ∨ (((p2 ∨ ((False → True) ∨ p2)) → p2) ∨ False)) ∨ (p2 → ((True → ((p5 → True) ∨ (((p3 → p4) ∧ p4) → p3))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_470788550672627062153249521802 : (((((False ∨ p4) ∨ ((p3 ∧ p4) ∨ ((p3 ∧ p4) ∨ (False → p2)))) ∧ ((p5 → (((p2 ∧ p4) ∧ (p1 ∨ True)) ∧ p1)) → (p3 → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185434402179607977188281998173 : ((False ∨ ((p5 ∧ (True ∨ (((p4 → p5) ∧ p5) → p3))) → False)) ∨ ((((p1 → False) ∧ p1) → (p5 ∧ ((True ∧ p1) ∧ p2))) ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164953336315165759649498476167 : (((((False ∨ False) ∧ (((True ∨ p5) ∨ (p1 → ((p2 ∧ p5) ∨ p1))) ∧ False)) → True) → p5) ∨ (True → (False → (((p5 → False) ∧ p1) ∧ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599122942028982431252026604812 : (((((p1 → True) ∧ ((p2 ∨ False) → (p1 ∧ (((p4 ∨ p3) ∨ False) → (((p3 → ((True ∧ False) ∧ (p4 ∨ True))) ∨ p1) → p3))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138020057397003569748909534152 : ((True → (((((p5 ∧ p2) → True) ∧ (((False ∨ (p5 ∧ (p3 ∨ (p1 → (p1 ∧ True))))) → p5) → True)) ∨ p1) → p4)) ∨ (True ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245203525698854772564525578665 : ((p2 ∧ False) ∨ (False ∨ ((((p1 → (True ∧ ((p2 ∧ (False ∨ (p2 ∧ (False → False)))) ∧ (p3 ∧ (p2 → p1))))) ∨ (p3 → p3)) ∨ p1) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615286120340516132869333765107 : (((((((((p5 ∨ (p2 → p5)) ∧ (True → p4)) ∧ (False ∨ (p1 → False))) ∧ p5) ∨ p4) ∨ (((True → True) → (p1 ∨ False)) → p1)) ∨ p4) ∨ p5) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48280766507836447958221028327 : (((p4 ∧ ((True ∧ (((((True ∧ (True ∧ p1)) ∨ True) ∧ True) ∧ (True → p2)) ∨ (p3 → p2))) ∧ (p3 ∨ (False → True)))) → (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766467355378894620181833272786 : (((p4 ∧ (p1 ∧ (p2 → ((True ∧ ((p4 → p5) → (p1 → (False ∨ (p3 → (((p4 ∨ p4) ∨ True) ∨ (False ∨ (True ∨ p2)))))))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



