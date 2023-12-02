variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158194408661659230260382048682 : ((((p3 ∧ p1) ∧ p1) ∧ ((((((p1 → False) ∧ (p3 ∨ p4)) → (p1 ∨ p3)) ∨ p1) ∨ p1) ∧ True)) ∨ (p3 → ((p3 ∨ (p5 ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336251180576404858816978338069 : (p1 → ((((p4 ∨ False) → (p1 → ((p1 ∨ (True ∧ p1)) → ((p1 → (p5 ∧ p5)) ∨ p2)))) ∧ (False ∧ ((p4 ∧ (False ∧ p2)) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48552254602502984844009900919 : (((((True → (((p1 ∨ p2) ∧ ((p3 ∧ ((p5 → (p3 ∧ p2)) ∨ (p2 → p5))) ∨ p5)) ∧ False)) → p4) → p1) ∧ ((p3 ∧ p4) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62732475054843069385728898975 : ((p4 ∧ ((p5 ∧ ((True → (p1 ∧ (p1 ∨ (p5 ∧ ((p5 ∧ True) ∨ (p5 ∨ p3)))))) ∨ ((p5 ∧ (p4 → p4)) → p4))) ∧ (p5 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113871242306778755822564458020 : ((((((((p4 ∧ ((p1 → p5) ∨ p3)) ∧ p3) ∨ (((p3 → p1) → p2) ∨ p2)) ∧ True) ∨ p4) ∧ p1) ∧ (p5 ∧ (p5 ∧ False))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117235016777147304383506884234 : ((True ∧ (p3 ∧ (((False ∧ (False ∨ (p1 → p3))) → ((((p5 → True) ∧ p5) ∨ (p2 ∧ (True ∨ p3))) → (p5 → False))) → p5))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173336323928412293344929896310 : ((p2 → (False ∧ (False ∨ ((p3 → ((p1 ∧ (p1 → False)) ∨ p3)) → (p1 → p3))))) ∨ (((((p3 → (p1 ∧ p1)) ∧ p4) → p5) ∧ p3) → p3)) := by
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
theorem thm_5_vars_352214016078327312624655307240 : (p4 → ((((False → p3) → False) ∧ p1) ∨ (((p1 ∧ ((((False ∨ p5) ∨ (p1 ∨ (p3 ∧ p5))) ∨ False) ∧ p2)) ∨ (p2 → p4)) ∨ (p5 ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612323920019776461483841264851 : (((((p3 ∧ (False ∨ (((p4 → (True → ((p3 ∨ (p4 ∧ (True → True))) ∧ p2))) ∨ p5) ∧ (False → (False → p3))))) ∧ (p3 ∨ p4)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_58070833798681133518162550560 : (((False ∧ p4) ∧ ((p3 → ((p3 ∨ (True → p3)) ∨ True)) → ((True → ((p3 → False) ∨ ((p3 ∧ True) ∧ (p4 ∨ p4)))) ∨ (True ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177794379518971041822904739725 : (((p1 ∨ (((p1 ∨ p4) → (True ∧ (False ∨ p5))) ∧ (True → p3))) ∧ True) ∨ (((p1 ∨ ((p3 ∧ ((p3 ∧ p1) ∨ p1)) ∨ True)) ∨ False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158568897687590186356907210913 : ((True ∧ ((False ∨ (((p2 → p1) → ((p2 ∧ p5) ∨ (False ∨ p1))) ∨ p1)) ∨ (False ∨ (p3 ∧ p4)))) ∨ ((False → (p2 → True)) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159110398986473370106374725072 : ((True → (p5 ∨ (((p2 → (p4 ∧ (False ∨ p3))) → (p2 ∧ (False ∨ ((p5 ∧ False) ∨ p4)))) → p1))) ∨ (p5 ∨ ((False ∧ (True ∧ p1)) → p1))) := by
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
theorem thm_5_vars_789928779115776822194977586793 : (((p5 ∨ ((True ∧ p4) ∧ ((False → (p3 ∨ (p3 → (False ∧ (((p3 → (p2 ∧ p2)) → p2) → p4))))) → ((False ∨ (p1 ∧ p3)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48993573021873751124377150745 : ((((p3 ∧ (p3 → (((((p4 ∨ (False ∨ False)) → (p4 ∧ p2)) ∧ p3) ∧ (False → (False → p2))) → p1))) ∨ p1) ∨ ((p1 ∨ p3) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114636804764573370106059861258 : (((((p4 ∨ (p2 ∨ ((p3 → p1) ∨ p2))) ∧ (False → ((p3 → p3) → False))) → False) ∨ (((p2 → True) → p5) → (p4 ∨ p1))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299273125719868638549184741075 : (False ∨ ((((p1 ∧ (p2 ∨ (((p2 ∨ True) ∧ True) ∧ p4))) ∧ ((p1 ∧ p3) ∨ (p5 ∨ p5))) → (p3 ∧ ((p1 ∧ (p1 ∨ p4)) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324378223637994888088674264235 : (p5 ∨ ((p3 ∧ ((False → (True ∧ p5)) → False)) ∨ (((((p5 ∧ p3) ∨ p1) ∧ p1) ∧ (True ∧ ((p1 → p3) ∧ False))) ∨ ((p3 → p3) ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150555004545492438253792393170 : ((((p2 → (p3 ∧ (False ∧ p5))) ∧ (((True → True) ∨ (False ∨ (((p2 → p3) ∧ True) ∨ p5))) ∨ p4)) ∧ True) → (p3 → (p3 ∧ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h30 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668688952865329380191838739759 : (((((((False ∨ (False ∧ (((p5 ∨ (p3 → ((p3 ∨ p1) → p4))) → p5) → False))) ∧ (False → p2)) ∧ True) ∨ True) ∨ (p3 → (p5 ∨ p3))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_157686810260750312167686120190 : (((p3 ∨ (p3 ∧ (((True → p4) ∨ p2) → ((p5 ∧ (True ∧ p1)) → p3)))) ∨ ((False ∧ p4) → p4)) ∨ (p4 → (True ∧ (True → (p5 → p3))))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116921854179160910571002756298 : (((True ∧ p5) → (((((p2 → (p1 → p1)) ∧ p3) ∧ (p5 → (False ∧ (((p5 ∨ p4) → p4) → p5)))) → p5) → (p5 → False))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225357891557460259078900284453 : (((p1 ∨ p4) ∧ p5) ∨ (((((True ∨ p3) → True) → p4) → ((p5 → (p1 ∧ (False ∧ (False ∧ (False → p5))))) ∨ (p4 ∨ (True ∧ p4)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57854709926738238065362276192 : (((True ∨ (p1 → p4)) → (((p1 ∧ p2) ∨ (p2 ∨ True)) ∨ (True → (p1 ∧ ((p3 ∧ (p2 → p3)) ∨ (((p5 ∨ p5) ∨ p2) → p1)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_673328927696500632136624920092 : ((((((((p3 ∨ p2) ∨ p4) ∧ p1) → False) ∧ (p2 ∨ (((p4 → p2) → p5) ∨ ((p4 ∧ (True ∨ p2)) ∧ True)))) → (p5 ∨ (p2 → True))) ∨ p4) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218393581147277623409502711020 : (((True ∧ False) → (True → p1)) → ((p1 ∧ ((((p2 ∨ p5) ∨ (p2 ∧ ((p5 ∨ (p3 ∨ p5)) ∧ p4))) ∧ p4) ∨ (p3 → False))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36690389611533835073997818018 : ((p5 → ((p2 ∧ (((p2 ∧ (p3 ∧ p2)) ∨ p3) ∨ ((False ∨ ((p4 ∨ p5) → (((False ∨ p3) ∧ p5) ∧ p4))) ∧ (False ∧ p5)))) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251390617560194433487303203570 : ((p2 → p4) ∨ ((p1 ∨ p5) → (p3 → (((True ∧ ((False ∨ p5) → ((p5 ∨ p2) ∧ (p3 ∧ p2)))) ∨ (False ∧ (False ∧ True))) ∨ (True → True))))) := by
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
theorem thm_5_vars_65563820695477232691068826066 : ((p3 ∨ (p2 → (p5 ∨ (((p1 ∧ (p5 ∧ ((p5 ∨ (True ∨ True)) ∧ ((False ∧ ((p5 ∨ p1) ∧ True)) ∧ (p1 ∧ p5))))) ∧ False) ∨ True)))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22973553000291343625482613187 : (((p5 ∨ ((p3 → (p3 ∨ p4)) → p5)) ∨ (((True ∧ (p5 ∧ p4)) ∨ (p4 ∧ True)) ∨ (((p4 ∨ (p2 → p4)) → (p4 → p3)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_171412075008886298558526616629 : (((((p3 ∨ p3) ∧ p4) ∨ (((p1 ∧ (p5 ∧ (p2 ∨ p5))) ∧ p5) ∧ p4)) ∧ p2) ∨ (False → (((p1 ∨ p5) → (p3 ∨ (False ∨ p4))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444702806043582472423795399033 : ((((p4 ∨ ((((False ∧ (p4 ∨ p5)) ∨ (((p3 → p3) ∨ p4) → ((True → False) ∨ p4))) ∨ (p5 → p1)) → p3)) ∨ (p1 ∨ (True ∧ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701437911062408654345744855077 : ((((((p2 ∨ p2) ∧ True) ∧ (p3 → (p4 ∧ (p1 ∧ False)))) ∧ (((p1 ∧ (p2 ∨ ((p3 ∧ p1) ∧ True))) ∧ p5) → (p2 ∧ (p1 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49324790865626467554679411823 : (((p4 ∨ ((p3 ∧ (p1 → (((((True → (p1 ∨ True)) → p4) → p5) ∨ p2) ∧ (p2 → False)))) ∨ (p5 ∨ p3))) ∨ (p4 ∨ (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3468730773994368662898165732 : (True ∧ (p4 → ((False ∧ (p2 ∨ (p2 → (p2 ∧ ((p4 → ((True ∧ p1) ∨ (False ∧ True))) ∨ p3))))) ∨ (p5 → ((p5 ∧ p1) → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299305476079099723479229131607 : (False ∨ (((p5 ∨ ((True ∨ p1) ∨ ((p2 ∧ True) → p1))) ∧ ((((False → (True ∧ (((p1 ∨ p4) → False) → p4))) ∨ p3) → p4) ∨ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172586517010823734715628889621 : ((((p2 ∨ p5) ∨ p4) → (((p3 → (True ∨ p1)) → ((True ∧ p3) ∧ False)) → p4)) ∨ (p4 ∨ (p2 ∨ ((p1 ∧ (False → p4)) ∨ (p4 → p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (p3 → (True ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h5
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p3 → (True ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219670359328943377592489667230 : ((False → (True → (p4 ∨ p4))) → (((p3 ∧ True) ∨ ((p3 ∧ (((p2 ∧ (p5 ∧ p4)) → ((p1 → p1) ∧ p1)) → p2)) ∧ (p4 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91002035623755952919337792906 : (((p1 → False) ∧ (True → ((((((((True → p5) ∧ p4) ∨ p1) ∧ p1) → (((p1 ∧ p5) ∨ p5) ∨ True)) ∨ (p3 ∧ p3)) ∨ False) ∧ p3))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123928508104467161786129799042 : ((((p1 → (p3 ∧ (p4 → p3))) ∧ ((False ∨ (p5 ∧ p4)) → True)) ∧ ((p2 ∨ ((p1 ∧ ((p2 → False) ∧ p4)) ∧ p4)) ∨ False)) → (p1 → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h19 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h20 := h5 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167829762290355273063579596304 : ((((((p3 ∧ (p1 → p4)) ∧ False) ∨ (p3 ∧ True)) ∧ p3) ∨ ((True ∨ p4) → (False ∧ p4))) → (p4 → (False ∨ ((False ∨ p5) ∨ (p3 ∨ p2))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41150118111987423205472913101 : (((((p3 → (False ∨ p1)) ∨ ((p2 ∨ ((p5 → ((p3 ∧ p4) → p2)) ∨ p3)) → (p2 ∨ (p1 ∨ True)))) ∨ (p2 ∧ (p2 → False))) ∨ p5) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
theorem thm_5_vars_64977852954579749251108965854 : ((p2 ∨ (((False ∨ (False ∨ p2)) ∧ p5) ∨ (p3 ∨ ((((((p3 ∨ p1) ∨ (p3 ∨ p3)) ∨ p3) ∨ (p1 ∨ (False ∨ True))) ∨ True) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190636656516593491679234349165 : (((p5 ∧ (p3 → (False ∨ ((p1 → p4) ∨ False)))) → p3) ∨ (p4 ∨ (((p1 ∧ p1) ∨ (p3 ∧ (p5 → p1))) → (p4 ∨ ((True → p3) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690934610537218614542815441777 : (((((((True ∨ p1) → ((p2 ∨ p5) ∧ p4)) → ((p5 ∧ p4) → False)) ∨ (p2 ∧ p5)) → ((p2 → p2) → (p2 → (False ∧ (p3 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346790158368706394543616992934 : (p3 → ((((p4 → p4) ∨ True) → (((True → (p4 ∨ (p3 ∧ True))) ∨ p1) → (p2 ∧ (True → (p5 ∨ p1))))) ∨ (p4 ∨ ((p2 ∨ p3) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115179788780789563326593860245 : (((((p5 → ((p3 ∨ False) → False)) ∧ True) ∧ (True ∧ p2)) ∧ ((p1 → p5) ∨ (((p2 ∨ ((p1 ∨ p5) → p2)) ∧ p1) ∨ p2))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127582901526876240670301919309 : ((p4 ∨ (p5 ∧ ((p3 → (((p4 ∧ p5) ∧ p2) → (False ∨ p2))) → ((p4 ∧ ((p3 ∨ p4) ∧ (p4 ∨ (p3 → p2)))) ∧ p5)))) → (p1 ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p3 → (((p4 ∧ p5) ∧ p2) → (False ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h6
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315820347749722199600296471187 : (p3 ∨ ((p3 ∨ p3) → (((p1 ∨ p2) ∨ p3) ∨ (p5 ∧ (p1 ∨ (((p5 ∧ p5) ∨ (((p5 ∨ False) → p3) ∧ p3)) ∨ ((p1 ∧ p4) ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222589309934131002292389080088 : ((True ∧ (p2 → p2)) ∧ (((p4 ∧ ((p2 ∨ True) ∨ False)) ∨ p4) → (((p1 ∨ (((False ∧ p1) ∨ p4) → (False ∧ (p5 ∨ p5)))) ∨ p1) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h11 =>
            -- One of the premise coincides with the conclusion.
            exact h5
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
            have h20 : ((False ∧ p1) ∨ p4) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h16
            -- We have shown the premise of h14, we can now drive its conclusion.
            let h21 := h14 h20
            -- We need to get the left conjuct of h21 based on <expert-advice>.
            let h22 := h21.left
            -- False on the left can always be used.
            apply False.elim h22
          case inr h23 =>
            -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
            have h24 : ((False ∧ p1) ∨ p4) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h16
            -- We have shown the premise of h14, we can now drive its conclusion.
            let h25 := h14 h24
            -- We need to get the left conjuct of h25 based on <expert-advice>.
            let h26 := h25.left
            -- False on the left can always be used.
            apply False.elim h26
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h29 : ((False ∧ p1) ∨ p4) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h30 := h14 h29
        -- We need to get the left conjuct of h30 based on <expert-advice>.
        let h31 := h30.left
        -- False on the left can always be used.
        apply False.elim h31
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h38 =>
          -- One of the premise coincides with the conclusion.
          exact h32
      case inr h39 =>
        -- False on the left can always be used.
        apply False.elim h39
    case inr h40 =>
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40616743895720145358742247933 : ((((((p1 → True) → (((((p1 ∧ (p2 ∧ (p3 ∧ p2))) ∨ (p3 → (p5 ∨ p3))) ∧ True) ∧ p5) → (p1 ∧ p2))) ∨ p3) → p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179631654910750337288736265838 : ((p4 → ((p1 ∨ p1) ∧ (p2 ∧ (((p1 ∧ True) ∨ (p2 ∧ p3)) ∨ False)))) ∨ (((p2 → p4) ∨ ((p2 ∧ p2) → (p3 → (True ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135326511205295865156721815382 : ((((p3 ∧ (p2 ∧ ((True ∨ p2) ∧ (p5 ∧ p1)))) ∧ ((True → (p4 → p1)) ∨ (p1 → p2))) ∧ ((p1 ∨ p2) ∨ p3)) ∨ (False → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146438275279526258295631917770 : ((p3 ∨ (((((((p2 ∧ p1) → p4) → (False ∨ (True ∧ p5))) ∨ p3) ∨ (p4 → (p1 ∧ False))) ∧ p4) ∨ True)) ∧ ((p2 ∨ (p4 ∨ p3)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175448542800716805714977511936 : ((p1 → (False ∧ (True ∧ (p3 ∧ ((p5 ∧ ((False ∨ p1) → (p2 ∧ p2))) ∧ p5))))) → ((p2 ∨ ((p1 ∧ p2) ∨ ((p4 → True) ∨ False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112215489905539133539104954450 : (((False ∨ (p4 ∨ ((((p1 ∨ p4) ∧ p2) → (p5 → (True → (p3 ∧ ((p2 ∧ (p5 ∧ (p4 ∨ p2))) ∧ p3))))) → p1))) ∨ p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258793668970005250157364941387 : ((True → False) → ((True ∨ (p3 ∧ p3)) ∧ (((True ∨ (p2 ∨ p2)) ∨ ((p2 → p1) ∧ (p2 ∨ p5))) → (p4 ∨ (p2 → ((p1 ∨ False) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h10 := h1 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h13 := h1 h12
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h21
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713998663703297638491613206965 : ((((((p3 ∧ (p5 → p1)) ∧ p2) → False) → ((False ∨ ((True ∧ (p1 → p4)) ∧ (p3 → (False ∧ (True → (p1 ∧ False)))))) ∨ (p1 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347284661748813052853649689975 : (p3 → (((((False → False) → p4) ∧ p1) ∧ (p2 ∧ (p5 ∧ False))) ∨ (((False ∧ ((False → p1) → p1)) → p4) ∧ ((p2 ∧ p3) → (p2 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174073463553673405327892012258 : ((((((False → ((False ∧ p3) → p2)) → True) ∨ (False ∨ p4)) ∨ True) ∧ (True → p3)) → (((p1 → True) → ((p3 → False) ∨ (p3 ∧ p2))) ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234376918568810029397456261743 : ((p1 → (p5 ∨ p4)) → ((p1 ∨ (True → (((False ∧ p2) ∧ ((p2 ∧ p2) ∨ p5)) ∧ p2))) → (((p2 → p3) ∨ (True → (False → True))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113252455016470174030915143971 : ((((False ∨ (True ∧ (((p2 → (p5 → (True ∧ p4))) → p1) ∨ (p5 → ((p2 ∨ p5) ∨ p4))))) ∨ (p4 ∧ p2)) ∧ (p3 → p3)) ∨ (p4 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117225019641155125104690024165 : ((True ∧ ((p4 → p3) ∨ ((p2 ∨ (p5 → (False ∨ ((p2 → (False → p3)) ∨ p1)))) ∧ (p2 ∧ (p5 ∨ (p3 ∧ (p5 ∨ p2))))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634306949490934514230268666078 : (((((True → (False ∨ (((((True ∧ p2) ∧ (False ∧ p3)) → ((p3 ∧ True) ∧ (p5 ∧ (p2 ∧ True)))) ∧ p5) → p1))) → (p3 ∨ p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116251521930463958501345026093 : ((((p4 → p4) → p4) ∨ ((p3 → (p4 → (p3 → (((True ∨ p1) ∧ (p3 → p3)) → (False → ((p3 ∨ p4) ∧ p2)))))) → p4)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135341183606995884353995970405 : ((((p3 ∨ p5) ∨ ((p5 → p3) ∨ (p4 ∨ ((((p4 → (p3 → p4)) ∧ p4) → p5) ∨ p2)))) ∧ (p5 ∧ (p3 ∨ p1))) ∨ (p1 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238750250377131573945033869875 : ((p1 ∨ True) ∧ ((True ∨ ((False ∨ p4) → (True → True))) → ((p1 ∨ ((True ∧ (True → True)) ∧ (p1 ∧ p4))) ∨ ((p5 ∨ p2) → (False → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195716188655082634404633006713 : (((p1 ∨ p3) ∨ (True ∨ ((p1 ∨ True) ∨ p5))) ∧ (((p1 → (p4 ∧ p4)) → p3) ∨ (((p1 ∧ False) → p3) ∨ (p1 ∧ (p2 ∨ (p3 ∨ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634719957314659241089396970099 : ((((((((p4 ∨ p3) → (((p2 ∨ ((p4 → p3) ∨ p3)) ∨ (True ∧ (p2 → p2))) ∧ False)) ∨ p1) → p4) ∨ (True ∧ (p1 → True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65230450183588885791634784708 : ((p3 ∨ ((p4 ∨ ((False ∨ ((p5 ∨ ((p1 ∨ p4) ∨ p3)) ∧ p1)) → (((p3 ∧ False) ∧ p3) ∨ (p1 ∨ ((p3 ∨ True) ∨ False))))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134040697677693668318707350603 : (((((False ∨ ((p5 ∨ p3) → False)) ∧ (p4 → (((p2 → (p1 ∧ p4)) → ((False ∧ p4) → True)) → p2))) ∨ True) ∨ p1) ∨ (p3 ∨ (p3 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149610839663255882906447900106 : ((p3 ∧ ((True ∨ True) → ((p4 ∧ False) ∨ (((p5 ∧ (False ∧ ((p5 → p2) ∨ (p3 ∧ p2)))) → p3) ∧ p3)))) ∨ ((p2 ∨ False) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67538555471060277531096432466 : ((p1 → (((p2 ∨ p4) ∨ p2) ∧ (p5 → ((False ∧ (((p3 ∨ ((((p5 ∨ p4) ∨ p5) ∨ (p1 ∧ p4)) → p1)) ∨ False) ∨ p1)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59584735779681858489950844414 : (((p4 → False) ∨ (p4 ∧ (((True ∧ p2) ∨ ((((p1 ∧ (p1 ∧ p4)) ∨ False) → ((p1 ∧ True) ∧ (True → False))) → p3)) ∧ (False ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57995211466405330319236222195 : (((p5 → (p3 ∨ p2)) → ((p4 ∧ ((True ∧ (p5 → p3)) → True)) → (((True → ((p5 ∨ (p1 ∧ False)) ∧ False)) ∧ (True ∧ False)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217744794643209370980220615790 : (((p3 ∧ (True ∨ p4)) → p5) → ((False ∧ p5) ∨ ((True ∧ ((p2 → (False ∧ (p2 ∨ (p3 ∨ ((p3 → p1) ∧ False))))) ∨ p3)) ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200411099296182249626120749710 : (((p5 ∧ p1) ∨ (p5 ∨ ((p5 → False) → p4))) → ((p4 → ((p3 → ((False ∨ p5) ∨ p1)) ∧ ((p2 ∨ p2) ∧ p5))) ∨ ((p1 ∨ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51637284963021290683084736361 : (((((True → ((p3 ∨ (p4 → (False ∧ (p2 → p2)))) ∨ False)) ∧ (False ∧ p3)) ∨ p1) ∧ (False ∧ (((False ∨ p3) → p5) → (p5 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632371258404625968915539260730 : (((((p5 ∧ (p4 → (p1 ∨ ((True ∧ ((False → ((p2 ∧ (True ∨ p1)) ∧ p4)) ∧ p2)) → (p3 ∨ (p4 → (True → True))))))) → p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147745448286431775459432730049 : ((((p4 → ((True ∨ p3) ∧ False)) → (True → (((False ∧ p3) ∧ (False ∧ (p5 ∧ p1))) ∧ (p1 ∧ p1)))) → p3) ∨ (p4 → ((p5 ∧ p1) → p1))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58961217208503336300094738329 : (((p2 ∧ p1) ∨ (p5 ∨ (p1 → ((((p4 ∧ p5) → ((p5 ∧ p5) ∨ (False ∨ p4))) ∧ (True → (p3 ∨ True))) → (p4 ∨ (False ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654448789024283902096308608405 : ((((((p3 ∧ False) ∧ (True → (((p5 ∨ p4) ∧ (((p2 → True) ∨ True) → (p3 → p5))) → (True → (p5 → p4))))) ∨ p2) ∨ (True ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_198032691444757514358702669361 : (((False ∧ True) ∨ (True ∧ ((p2 ∧ p1) ∨ p5))) ∨ ((((((p3 ∨ p4) ∨ (p3 → p2)) → p1) ∧ False) ∨ p3) ∨ ((p2 ∨ True) ∨ (p4 ∨ p2)))) := by
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
theorem thm_5_vars_177674652415017288015938138574 : (((((p4 ∨ ((p5 → (p5 ∨ p1)) → p1)) ∨ (True → p5)) → p5) ∧ True) ∨ (((p3 → (p2 ∨ True)) ∨ p3) ∨ ((p1 ∨ (p2 ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308481782465008603392106313736 : (p2 ∨ (((((p5 → (True → True)) ∨ p5) ∧ (((((p5 ∧ (p3 ∧ p5)) ∧ p3) → (p5 ∨ p5)) → p1) → p3)) ∧ (p2 ∧ (p1 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341673113439808480929232874045 : (p2 → (((((p5 → (((p5 ∧ p3) → p2) → p3)) ∧ (p3 ∧ p2)) ∧ ((p4 ∧ False) → (((p2 ∧ False) ∨ p1) ∨ p2))) ∨ False) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166241280347224818134190188412 : ((p2 ∧ (p1 → (((((p3 ∨ False) ∨ (p3 ∨ p3)) ∨ (p5 → p1)) ∨ (p2 ∧ False)) ∨ p5))) ∨ (((True ∧ p5) ∨ True) → ((p5 ∨ True) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355857273736748195053228229643 : (p5 → (((((p2 ∧ (p1 ∧ (p4 ∨ p3))) → p3) ∨ ((p4 ∧ p2) ∧ (True ∧ p1))) → ((p3 → (p1 ∨ False)) ∨ p5)) ∨ (p2 ∨ (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37646137910805481947749428352 : (((((True → (((p2 ∧ (p4 → (True → ((p3 ∨ True) ∧ (p3 → (p5 → False)))))) → p3) → ((False ∨ p3) → p1))) ∨ True) → False) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225924856027167587494433399164 : (((p2 ∧ False) ∨ p3) ∨ (p1 ∨ (((p5 ∨ True) ∨ (p2 ∧ (False ∧ ((False ∨ (p2 ∧ p4)) ∧ False)))) ∨ ((p2 ∧ True) ∧ (p4 ∨ (p4 ∧ False)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318617228485814428671532955301 : (p4 ∨ (((p4 → (False → p2)) → (p4 ∨ (p3 → (((True → ((False ∨ p2) ∧ p2)) ∨ True) ∨ (((False ∧ p3) ∧ True) ∨ p1))))) ∨ (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627494463188509038981327315392 : (((((((p1 ∨ ((p4 → (p3 ∨ (p1 → ((p4 ∨ p2) → p3)))) ∨ (p5 ∧ (True → (p1 ∧ p5))))) ∨ p5) ∧ (False → p4)) ∧ p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354849130678277473839877118171 : (p5 → (((p4 ∨ p1) ∨ ((((p2 ∨ (((True → ((True ∨ p2) → p1)) → (p5 ∧ p4)) → p4)) ∨ p1) → (p3 ∨ p5)) ∧ (p2 ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248594436079094430947628379933 : ((p3 ∨ False) ∨ ((p2 → True) ∧ (True ∧ ((((True ∧ (p1 ∧ ((True ∨ p3) → (p2 ∨ True)))) → True) ∧ False) ∨ (p5 → ((False ∨ False) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249658253122575414723093573358 : ((p5 ∨ p4) ∨ ((p4 → ((p5 ∧ ((p2 ∧ (p1 → (p5 ∨ (False ∧ ((True → p5) ∨ (p2 ∧ p2)))))) ∨ (False ∧ (p2 ∨ p3)))) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245146038946996244896637059863 : ((p2 ∧ True) ∨ (p4 ∨ ((((p5 ∨ (p1 ∧ p2)) → ((p5 ∨ p2) ∨ False)) → (((False → (((p1 → p5) ∨ False) ∨ False)) → True) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116359604941441743731850880159 : ((((p3 → p5) ∨ p2) → ((((p1 ∧ (p1 ∧ True)) ∧ ((p3 → (((p3 ∨ p1) ∨ p3) → p4)) ∧ True)) ∨ p4) ∧ (False ∧ p2))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654918454195963098902353322478 : (((((((p3 → ((False ∨ (p4 ∨ p5)) → p3)) → p4) ∨ (((p1 → p5) ∧ (p4 → p3)) ∧ (p3 → (p5 ∧ False)))) → p4) ∨ (False → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_135797179131703583302095671587 : ((((p1 ∨ False) → (p5 ∧ (((p5 ∨ (p2 ∨ p2)) ∧ p3) ∧ (p5 → p3)))) → (p1 ∧ (p3 ∨ ((p3 ∧ True) ∧ True)))) ∨ (p2 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179393178947855398177738649789 : ((p3 ∨ ((((False → False) ∧ p1) ∧ (p1 ∨ p5)) → (p5 → (p4 → p3)))) ∨ (((p5 ∧ p4) → p4) ∨ (((p5 ∧ (False → p2)) ∨ p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



