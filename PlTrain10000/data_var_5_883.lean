variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617015612955774228656821921847 : (((((((False ∧ p2) ∨ (p3 ∨ (p4 → True))) → p2) ∧ (p3 ∨ ((p1 ∨ p2) ∧ ((((p4 ∧ (True ∧ True)) → p2) ∧ p5) → p5)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_785393542151358241476315233531 : (((p4 ∨ (((((False ∨ p5) ∧ (((((p2 ∨ (p5 → p5)) ∧ p1) ∨ p1) ∨ (p1 ∧ (False ∧ p3))) ∧ p4)) ∨ p2) ∨ (p1 ∧ p5)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_344429263872133888177013886339 : (p2 → (p5 ∨ ((p5 → ((p4 → p1) → ((p5 → ((p3 ∧ p1) ∨ (p5 ∨ p4))) ∧ p3))) ∨ (((p3 ∨ False) ∧ (True ∨ (False ∨ p2))) → p2)))) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190667578461733740334326679724 : (((False → ((False → p4) ∧ ((False → p2) → p2))) → False) ∨ (((True ∧ True) ∧ ((p5 ∨ True) ∨ (p4 → ((True → p4) → p4)))) ∨ (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185120015278228368620941326916 : (((True ∧ p1) → (p3 ∨ (p4 ∨ ((True ∨ (False → p5)) → p3)))) ∨ ((True ∨ (((p3 → p1) ∨ True) ∧ (p4 ∧ (True → (p5 → p3))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66107322485361836859960699430 : ((p5 ∨ ((((p1 → (p5 ∧ True)) ∧ p1) ∧ (((True → ((True → (p3 ∧ (p4 ∨ True))) ∧ (p1 ∨ p2))) ∧ p4) ∨ (p3 ∧ p1))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126415575978665072851398106817 : ((p1 ∧ (False → (((p5 ∧ (((p5 → ((p5 ∧ (p2 ∧ p1)) ∧ p5)) ∨ (p3 ∧ (p1 → (p5 ∨ p4)))) ∨ p5)) → p1) ∨ False))) → (p2 ∨ True)) := by
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
theorem thm_5_vars_185343696546123204231104923513 : ((p4 ∧ (((p3 ∧ p1) ∧ (p5 ∧ ((p1 ∧ p2) ∧ p4))) → True)) ∨ (p2 ∨ ((p1 ∨ (False ∨ ((p4 → ((p1 → p2) ∧ p3)) ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788315102916406418421708454045 : (((p5 ∨ (((((((p2 → (False ∧ p5)) ∨ p5) ∨ ((True ∧ (False ∨ p1)) ∨ ((p3 ∨ p2) ∨ p3))) ∨ (False ∧ p2)) → p5) ∨ p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201230189822696349265225419029 : ((p2 → (p1 ∧ (((True ∨ p3) ∨ p2) ∧ p2))) → (((p2 ∨ ((p4 ∨ (False ∧ False)) → (p5 ∧ ((p4 ∧ True) → (False ∨ False))))) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173080785878029625747840870979 : ((p1 ∨ (((p5 ∨ (((p4 ∨ p1) → (False → p2)) → (p4 ∨ p2))) ∧ p2) → p1)) ∨ ((p2 ∨ (p4 ∨ (p2 → (False → p2)))) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229057821924413804573339268765 : ((p5 ∨ (p4 ∨ p4)) ∨ (p2 → (((p3 ∧ (p3 → p3)) → (True → (p5 ∧ ((False ∨ p5) ∧ (p5 ∧ p3))))) ∨ (True ∨ ((p1 ∧ p1) ∧ p3))))) := by
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
theorem thm_5_vars_345436864110195323468255187057 : (p3 → ((((p4 ∨ p1) ∧ (p4 ∧ (p3 → (True ∨ (True ∨ (((p3 ∨ p4) ∧ (((p2 ∧ False) ∨ True) → p2)) ∨ p2)))))) ∧ (False ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184376910190290962467741445980 : (((True → (((p1 ∨ False) ∧ (p1 ∨ p2)) ∨ (p5 ∨ p1))) → False) ∨ ((p2 ∧ (p4 ∧ (p4 ∨ False))) → (p4 ∧ (p1 → ((p2 ∨ p3) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798191048063508371732442510038 : (((p1 → ((((((p5 ∨ p5) → ((p1 → p2) → p2)) ∨ p2) → ((p5 → p2) → (False → p3))) ∨ p4) → ((p2 ∧ (p3 → p2)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310019966129038673980532141934 : (p2 ∨ ((((True ∨ p1) ∧ (p3 → ((p3 → (p2 ∨ (p4 ∨ True))) → (p1 ∨ p5)))) ∨ True) ∨ (((p1 ∧ p4) ∧ ((p4 ∨ p5) ∧ p4)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53365196606286694799677192999 : ((((p1 ∧ (p1 ∨ (p3 → (p5 → ((p2 ∧ p3) → p4))))) ∨ p3) → (((True → (((p5 → p3) ∧ True) ∧ (True ∨ False))) ∧ p1) ∨ True)) ∨ p1) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136169258608322375641828600269 : ((((((p3 → p5) → p2) ∨ p3) ∧ p4) ∧ (p5 ∧ (((True ∧ (p2 ∧ ((p5 ∨ True) ∧ p5))) ∧ (p1 ∧ False)) ∨ True))) ∨ (True ∧ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41276128872433228443379611783 : ((((((p4 → ((p4 ∧ (True → p2)) ∧ (p5 ∧ (False ∧ (False ∨ (p5 ∧ True)))))) ∧ p1) ∨ p4) → (((True → p5) ∧ p4) → False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172401687186785101599217324108 : (((p2 ∨ (p3 → (True → (False ∨ p2)))) → (((p4 → (p1 ∧ False)) ∧ p2) ∧ p5)) ∨ (True ∧ ((False ∧ ((p2 → p3) ∧ (p4 ∨ p2))) → True))) := by
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
theorem thm_5_vars_36669935090550805933570520147 : ((p5 → ((((False → p2) ∧ ((((((p5 ∨ p4) ∨ p3) ∨ p2) ∧ p2) ∧ ((p3 → (p1 ∧ p4)) ∨ p2)) ∨ (False ∧ False))) → p1) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113837233743634265845841238917 : (((p2 ∨ ((((((p5 ∨ False) → p1) → p2) ∧ p1) ∧ p1) ∧ ((True ∧ p4) → (p5 → ((p4 → p5) ∧ p1))))) → (p2 → p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41497263955358816078298177318 : (((((((p5 ∨ False) → p3) ∨ (p3 ∨ False)) ∧ (p4 ∨ (p1 ∧ True))) → (p4 ∨ ((p2 → (p5 → p2)) → ((p3 ∨ p2) ∧ True)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114231095732281830898289426271 : (((p2 ∧ ((p4 ∨ (True ∧ ((p4 ∧ (True → (False → (False → p2)))) → p5))) ∧ ((p3 ∧ p5) ∧ True))) → (p2 ∧ (False ∨ False))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109577602458513786075257732001 : ((p3 ∨ ((((False → True) ∨ ((p1 → p4) ∨ True)) → p2) → ((((False ∨ (p1 → False)) → (p5 → p5)) → p4) ∨ (p4 → True)))) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137947610763831207516885648421 : ((p5 ∨ (((((p2 → (True ∨ ((True ∨ p1) → p1))) ∧ (p4 ∨ p1)) ∧ (((p1 ∧ False) ∨ p2) ∧ True)) ∨ p3) ∨ p3)) ∨ (False → (p3 ∧ p4))) := by
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
theorem thm_5_vars_241536955729850668857912310736 : ((False → p3) ∧ ((p1 ∧ ((p3 → (False ∧ p4)) ∨ (((True ∨ (True → (False → False))) ∨ p2) ∨ True))) → ((p3 ∧ p5) → ((p4 ∨ p5) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112779300070717099629615017197 : (((((False ∨ ((False ∧ (p1 → p1)) ∨ p3)) ∧ p2) ∨ (((((((p5 ∨ p4) → p5) ∨ p5) → p1) ∧ p3) → False) ∨ False)) → p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1484182102784328258459909252 : ((((p4 ∨ True) ∧ ((p2 → (p5 ∨ (((((True ∨ (p5 ∧ p2)) → True) → p3) ∨ (p4 ∧ True)) ∧ True))) → False)) → p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84717357452788287506440177886 : (((((p1 ∨ (p5 ∧ True)) → (p1 ∨ ((False ∧ p2) ∧ False))) ∧ (p2 → p3)) ∧ (((p3 ∨ p4) ∨ (((p5 → p4) ∨ True) ∨ False)) ∧ p5)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : (p1 ∨ (p5 ∧ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- False on the left can always be used.
        apply False.elim h16
    case inr h18 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : (p1 ∨ (p5 ∧ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h19
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h23.left
        let h26 := h23.right
        -- False on the left can always be used.
        apply False.elim h25
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h30 : (p1 ∨ (p5 ∧ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h7
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h31 := h4 h30
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- Conjunctions on the left can always be decomposed.
          let h36 := h34.left
          let h37 := h34.right
          -- False on the left can always be used.
          apply False.elim h36
      case inr h38 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h39 : (p1 ∨ (p5 ∧ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h7
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h40 := h4 h39
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Conjunctions on the left can always be decomposed.
          let h45 := h43.left
          let h46 := h43.right
          -- False on the left can always be used.
          apply False.elim h45
    case inr h47 =>
      -- False on the left can always be used.
      apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40949021522206774147910030855 : (((((p3 ∨ ((((p4 ∧ p3) ∧ (p5 → p2)) ∨ ((p2 → (p1 ∨ (False → p5))) ∨ p1)) ∨ p4)) ∧ (p4 ∨ True)) ∨ (p5 ∧ p4)) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668527909976431856506390486783 : ((((((p2 ∧ ((p3 → (False ∨ p4)) ∧ (p2 → p1))) ∨ ((True → (p4 → ((False ∧ p2) ∨ p3))) ∨ p1)) ∧ p3) ∨ (p5 ∨ (False → p2))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_16946555055746557890514933214 : (((p1 ∨ (((False ∧ True) → True) → ((p4 ∧ ((((False ∨ p3) ∨ (p2 ∧ True)) → True) ∨ p1)) ∧ (p2 ∧ p2)))) ∨ (True → (p3 → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39385754451090068437173152633 : (((p3 ∧ (p1 ∨ (((((((p5 → p1) ∨ p2) ∧ True) ∨ ((p1 → (p3 → (p2 ∧ p1))) ∨ p2)) ∨ p3) → p5) ∨ (p1 ∧ p1)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49260842411462402424677224902 : (((p1 ∧ ((False ∧ (((p1 → (((p2 ∧ (p2 ∧ p4)) ∨ True) ∨ (p3 ∧ (p3 ∧ p3)))) ∧ p1) ∨ True)) ∧ True)) ∨ (p1 ∧ (True ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134663779812481090039287715387 : ((((((p2 → p2) ∧ (p3 ∧ (p4 ∧ (True ∧ True)))) ∨ p2) → ((p2 → ((p4 → p2) → p3)) ∧ (p2 ∧ True))) → p5) ∨ ((False → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135873936306135248075824886116 : ((((True ∧ (p3 ∧ p1)) ∨ (False ∨ (p4 ∨ ((True ∧ p2) ∨ p1)))) ∨ (True ∨ (True ∨ (False ∧ (p2 → (False ∨ False)))))) ∨ (True → (p3 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228747885717068168934003618615 : ((p2 ∨ (p5 → p4)) ∨ ((((p1 → (p5 → ((True ∧ (p1 ∧ p5)) ∨ (((p4 ∧ (p3 → True)) ∧ False) → p4)))) ∧ True) → (True → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244252640927365617643603809848 : ((False ∧ True) ∨ ((p2 ∨ (((p1 ∨ (True ∧ (((p3 → p3) → ((True ∧ False) ∨ False)) ∨ p4))) ∨ (p4 → (p4 → (p3 ∨ p1)))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40711869506456909303429377346 : ((((((((True ∧ ((p5 ∧ p2) ∨ p3)) ∨ p1) → False) ∨ p5) → (p2 → ((True → ((p1 ∨ (p5 ∨ p4)) → True)) ∨ p1))) → p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165744810593873108304982184979 : ((((p4 ∨ p5) ∧ (p1 → p4)) ∨ (((p2 ∨ p4) ∨ (False → p4)) ∨ (p1 ∨ (False ∧ p1)))) ∨ (p5 → (p1 ∨ ((p1 → False) → (p5 → p5))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117912955513037434898931564146 : ((p5 ∧ ((p3 ∧ ((p3 ∧ ((p4 → False) → p2)) ∨ p2)) ∧ (((p2 ∧ (p4 ∨ p1)) → ((p5 ∨ p1) ∨ p1)) ∧ (p4 → p1)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261279260508743390468832370367 : ((p5 → True) → ((((False ∨ True) → (True ∨ p4)) ∨ (p3 → p5)) → ((((p5 ∨ (p5 → ((p3 → False) ∧ (p2 ∧ p5)))) ∧ True) ∨ True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45703129075453028918429043374 : (((True → (((p2 → (p4 → (True ∧ (p1 → ((False → True) → p5))))) ∨ ((False → (True ∧ (True ∨ False))) ∧ (p2 ∧ True))) ∨ p3)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348210367623457365013454147333 : (p3 → ((p1 → p4) → ((False ∨ (p5 → ((p1 ∨ p4) ∧ ((((p1 → p4) → (p2 ∨ True)) → True) → ((False ∨ p3) ∧ p1))))) ∨ (p3 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55904514330115228468690694107 : (((p4 ∨ (True ∧ (p5 ∧ p4))) ∧ (((((False ∨ (p5 ∧ False)) ∨ False) ∧ ((p1 ∧ False) ∨ (p2 ∨ False))) ∨ ((p4 → p3) ∧ p1)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172142733851697056033530326153 : (((False ∨ (((p5 ∨ p4) ∧ (p5 ∨ p3)) ∧ (p3 → p3))) ∧ ((p2 → p4) ∨ True)) ∨ (False → (False → ((p3 → p2) ∧ (False ∧ (p5 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158261251783567813211670322655 : (((False ∧ (p1 ∨ p3)) ∨ ((p3 → (p3 → (((p5 → p2) → p2) ∧ ((p2 ∨ p2) → True)))) → p5)) ∨ (((True → (p5 ∧ False)) → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688706818717544700651049307661 : ((((p1 → (((p3 ∨ p3) ∨ (p1 ∨ (False → p4))) ∧ ((p5 ∧ p4) ∧ (False ∧ p2)))) ∧ ((((p3 ∧ p2) ∨ p1) ∨ p3) ∨ (p3 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140303033673709974254980932283 : ((((p5 ∨ p1) → (((p3 ∨ (((p5 ∧ p1) → p3) → ((p4 ∧ False) → False))) ∧ True) → False)) ∧ ((p5 ∨ p4) ∨ p4)) → (p5 → (p1 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((p3 ∨ (((p5 ∧ p1) → p3) → ((p4 ∧ False) → False))) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h9
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : ((p3 ∨ (((p5 ∧ p1) → p3) → ((p4 ∧ False) → False))) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- False on the left can always be used.
        apply False.elim h22
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h23 := h17 h18
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h25 : (p5 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h26 := h3 h25
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h27 : ((p3 ∨ (((p5 ∧ p1) → p3) → ((p4 ∧ False) → False))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- False on the left can always be used.
      apply False.elim h31
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h32 := h26 h27
    -- False on the left can always be used.
    apply False.elim h32
  -- Conjunctions on the left can always be decomposed.
  let h33 := h1.left
  let h34 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h37 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h38 := h33 h37
      -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
      have h39 : ((p3 ∨ (((p5 ∧ p1) → p3) → ((p4 ∧ False) → False))) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h40
        -- Implications on the right can always be decomposed.
        intro h41
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- False on the left can always be used.
        apply False.elim h43
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h38, we can now drive its conclusion.
      let h44 := h38 h39
      -- False on the left can always be used.
      apply False.elim h44
    case inr h45 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h46 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h47 := h33 h46
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h48 : ((p3 ∨ (((p5 ∧ p1) → p3) → ((p4 ∧ False) → False))) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h49
        -- Implications on the right can always be decomposed.
        intro h50
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- False on the left can always be used.
        apply False.elim h52
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h53 := h47 h48
      -- False on the left can always be used.
      apply False.elim h53
  case inr h54 =>
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h55 : (p5 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h56 := h33 h55
    -- We want to use the implication h56 based on <expert-advice>. So we show its premise.
    have h57 : ((p3 ∨ (((p5 ∧ p1) → p3) → ((p4 ∧ False) → False))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h58
      -- Implications on the right can always be decomposed.
      intro h59
      -- Conjunctions on the left can always be decomposed.
      let h60 := h59.left
      let h61 := h59.right
      -- False on the left can always be used.
      apply False.elim h61
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h56, we can now drive its conclusion.
    let h62 := h56 h57
    -- False on the left can always be used.
    apply False.elim h62



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345330802637352411497823448040 : (p3 → ((((p5 → (((p3 ∧ ((False ∨ p5) ∨ True)) ∨ (p5 → p3)) → True)) → ((p3 ∨ True) → (p5 → ((p5 → p3) → p4)))) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624084027939825158990508167153 : ((((p2 ∨ (((p4 ∨ p4) ∨ p5) ∨ ((p4 ∧ ((p2 → p5) ∧ (p4 → ((p5 ∨ p2) ∧ (False ∨ (True ∧ (False → p5))))))) ∨ p2))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57997691172556115948741768302 : (((p5 → (p1 → False)) → (((p3 ∧ False) → True) → ((False ∨ ((((p1 ∨ False) → (p3 → (p3 ∧ (True ∧ p2)))) → p1) ∧ p2)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634179471755936561966541931754 : ((((((p5 ∨ p2) ∨ ((((p4 ∨ (p2 ∨ p5)) ∧ True) ∨ (p3 ∨ p1)) ∨ (False → ((p5 → p4) ∨ (p1 ∧ False))))) → (True → p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158298346011521676259231311332 : ((((p3 ∧ False) → p5) → (True → (((p5 → p1) → (False → False)) ∧ (((p2 → p2) ∧ p3) ∨ False)))) ∨ (p4 ∨ (p1 → (p3 ∨ (False ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612221396991990882152212717183 : (((((((True ∧ False) ∨ p4) ∧ ((False ∧ ((((p1 → p1) → (False → p4)) ∧ ((p2 ∨ p4) → p5)) ∧ p2)) ∧ p3)) ∧ (p5 ∧ p1)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_48699805502663584622390473590 : ((((p1 ∧ (((p1 ∨ p2) → p4) → p3)) ∧ (False ∧ (p1 → (((p4 → ((p2 ∧ False) → p2)) ∨ p1) → p5)))) ∧ ((p2 ∧ p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69354974006974618670552744691 : ((p5 → (p3 ∨ ((True ∨ p1) → (p5 → ((p2 ∧ (True ∧ ((((False ∨ (p3 ∧ True)) ∨ (p3 ∨ True)) ∨ p3) → False))) ∨ (p2 ∨ True)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_56276611507960792785432074964 : (((p4 → (p2 ∨ (False ∧ p1))) ∨ (p5 → ((p4 → ((p2 ∨ ((p2 → p1) → (False ∨ p4))) ∨ ((False ∨ p4) → (False → p2)))) ∨ p5))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691492039435846811772744680126 : (((((True ∨ p5) → ((False ∨ p3) → ((True ∧ ((p5 ∧ True) → True)) → (p3 → False)))) → ((p1 ∧ p1) ∧ (False ∧ ((p3 ∨ p4) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612325736326339746795555612890 : (((((p4 ∧ ((False ∨ ((((True → (p3 → (p3 → (p3 ∧ (True ∧ p5))))) ∧ (False ∧ p4)) ∨ p5) ∧ p3)) ∧ False)) ∧ (p5 ∨ p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667145036162690220553960666789 : (((((p4 → (p3 ∨ p5)) ∨ (((((False → p1) ∨ ((True → (p5 → p1)) → (True → False))) ∧ p4) ∨ p2) → p4)) ∧ (p3 ∧ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172796464359950884386762925607 : (((p3 → p1) → ((p2 → (p5 ∧ ((False ∧ p5) → ((p2 → p4) → True)))) → p4)) ∨ ((p4 → True) ∨ ((True → (p5 ∧ (p5 → p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66624121300272564062549821306 : ((True → (((p3 → (p4 ∨ p5)) → (False ∨ ((True → p4) ∨ ((p5 → (False ∧ p5)) ∧ p2)))) → (((p4 ∨ p3) ∨ (p4 ∧ False)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255727190668242186851691963166 : ((True ∨ True) → (((p2 ∧ ((p2 ∨ ((True ∧ (p3 ∧ p3)) ∨ ((p5 → p2) ∧ ((p5 ∨ ((p5 → p1) ∧ p2)) ∧ p5)))) ∧ p3)) → False) ∨ True)) := by
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
theorem thm_5_vars_119054658926171729024868783581 : ((p1 → ((p5 → (((p5 → (p3 ∨ False)) → True) ∧ ((p3 ∨ ((p3 → p5) → ((p4 ∧ False) → (p4 → False)))) → False))) ∨ True)) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684886265213388985865004260255 : ((((False ∧ (((p4 ∨ ((p4 ∨ ((p4 → p4) → (p3 → (p1 → True)))) ∨ p5)) ∧ p2) → p3)) ∨ (True ∨ (((p5 ∧ False) ∨ True) → False))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_686030947078994624093924834589 : (((((((False ∨ (((p4 ∨ True) ∨ ((p2 → p1) ∧ True)) ∨ True)) ∧ p5) → p2) → (p4 ∧ p1)) → ((p4 → p1) → (p4 ∧ (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54510723400178202192656827838 : (((((False ∧ False) → True) → (p3 ∧ (True ∧ p2))) ∨ (((False ∧ p4) → (p2 → ((((p4 → p4) → p3) → (False ∨ p2)) ∨ p5))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134358771054391542447698835325 : (((False ∨ ((True ∨ p4) ∧ (p1 → (((p2 ∨ p2) ∨ ((p1 → p3) → p2)) ∧ (((p4 → True) ∧ p2) ∧ p1))))) ∨ p2) ∨ ((False ∧ False) → False)) := by
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
theorem thm_5_vars_301268732511904104661722201686 : (False ∨ ((p5 ∨ ((p5 ∧ True) ∧ (False ∧ p2))) ∨ (((p4 ∨ p4) → p4) ∨ ((((p5 → (p4 ∨ (False ∧ p4))) → (p1 ∧ p3)) ∧ p3) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119100303291197948997758585178 : ((p1 → ((False → ((p1 ∨ True) ∨ True)) ∧ ((((p2 ∧ ((True → (p2 → p5)) → (p2 ∧ p5))) ∨ False) ∨ p1) ∨ (p2 ∨ p2)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177822382801271455010977835316 : (((p3 → ((False → p5) → ((p5 → (p1 ∧ p5)) ∧ (False → True)))) ∧ p5) ∨ (False ∨ (p3 → ((((p4 ∨ p1) → p4) → False) → (False → p1))))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116607725002027593534271785280 : (((True → p1) ∧ (False ∨ ((p1 ∧ ((p4 ∨ p5) ∨ (False ∧ ((p3 ∧ ((False → False) ∧ p2)) → (p4 → p5))))) ∧ (False ∨ False)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748012552694183397681315406095 : ((((p1 → False) → ((p1 ∧ p5) → (p3 → (p2 ∨ (p1 ∧ (((False ∨ (((p5 ∨ (True ∨ p2)) ∨ (p4 ∨ p3)) ∨ p4)) ∨ False) → False)))))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157110338383746721874254379346 : (((p4 → (p4 ∧ (((p5 → ((((p1 ∧ p5) ∧ p3) → (p1 ∨ p3)) ∧ p4)) ∧ True) → p3))) ∨ p4) ∨ ((False → (p1 ∨ (p2 → p2))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761656522968041868904008984670 : (((p3 ∧ (((False ∨ ((p4 ∧ (p5 ∧ False)) ∨ p5)) → (((p4 → False) ∨ ((p4 ∧ True) ∨ ((p3 → (p2 ∨ p5)) ∧ p4))) ∨ p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121841275779644034360720313706 : ((((p4 ∨ p5) ∨ ((p2 → (p2 → (((p2 → p3) ∨ True) → False))) ∨ ((p1 ∧ (p4 ∧ False)) → (p3 ∨ (True ∨ False))))) → False) → (p2 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ p5) ∨ ((p2 → (p2 → (((p2 → p3) ∨ True) → False))) ∨ ((p1 ∧ (p4 ∧ False)) → (p3 ∨ (True ∨ False))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118225252363250005005573694307 : ((p1 ∨ ((False ∧ (((p4 ∧ True) ∨ False) → ((p1 ∨ ((p1 ∨ p5) ∧ (True → (False → p2)))) ∨ (p2 ∨ (p2 ∨ p5))))) ∨ True)) ∨ (False ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172897303700761435835422267862 : ((p2 ∧ ((p1 → (p3 ∧ (True → ((p1 ∧ (False ∨ p5)) ∨ (p5 ∧ p5))))) ∧ p1)) ∨ (False → ((p4 ∨ p3) ∧ (True → (False ∨ (True → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697896945039229278439324034772 : (((((((p2 → p5) ∧ (p3 ∨ p4)) ∧ ((p4 ∨ True) ∨ p2)) ∧ True) ∨ (True ∧ (p4 ∨ ((p4 → (False ∧ p1)) ∨ ((p5 → False) ∨ True))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26420280676677022875785394916 : (((p4 → p4) ∧ (p3 → ((p2 ∨ ((((p5 ∧ (p5 ∧ p2)) ∧ False) → (p2 ∧ p5)) → ((p3 ∧ p1) → False))) ∨ ((True ∧ p2) → p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324482761544575864710911782813 : (p5 ∨ (((p2 ∧ (p4 ∨ p1)) ∨ p3) ∨ ((p3 → p5) → (p5 → ((p1 → (False → (p5 ∧ p5))) ∧ ((p4 ∧ p2) → (p2 ∨ (p4 ∨ True)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698468207100410566927690783557 : (((((p4 ∧ ((p2 ∨ (p5 ∧ p3)) ∧ p1)) ∨ (True ∨ (p4 ∧ False))) ∨ (((p5 ∨ p5) ∧ p4) ∧ (((True → (p5 → p1)) → p5) → p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_36690363642223120403203016100 : ((p5 → ((p2 ∧ (((((True ∨ p4) ∧ (p2 → False)) ∨ p1) → p1) → (((False → ((p5 ∨ False) ∨ (True ∨ p1))) ∨ p5) ∧ p1))) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803325900018717941452251748853 : (((p3 → (((False ∨ ((True ∨ False) ∧ p1)) → ((((((p4 ∨ p1) → ((p4 ∨ False) ∨ p5)) ∨ False) ∧ p4) ∨ (False ∨ p2)) ∨ p1)) ∨ False)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38431971559550664388896737043 : (((((((p1 ∧ False) ∧ p5) → (p2 → (p5 ∧ (p2 ∨ (True → True))))) → p4) ∨ (((p1 ∨ p5) → p3) → (p1 → (p5 ∧ p1)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229877126761639379730450088701 : ((p5 → (p3 ∨ p2)) ∨ (p3 ∨ (((p3 ∨ p3) ∨ ((False ∨ (p4 ∨ ((p5 ∧ True) ∨ p1))) ∨ p4)) ∨ (((p2 ∨ p3) ∧ p3) → (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37772741633010602271170114053 : (((((p4 ∨ (p5 ∨ p2)) → ((((True ∨ p4) ∧ (p5 ∧ True)) ∨ (p5 → False)) ∧ ((p2 ∧ False) → ((p5 ∧ p2) ∨ p2)))) → p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354641366441125543355028047797 : (p5 → ((((((p5 → ((p4 → (p3 ∨ p4)) → False)) ∨ (((p1 → True) → ((p4 ∧ False) ∧ False)) ∨ p4)) → (False → True)) ∨ p4) → p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193179683258457119847650120312 : (((((p4 ∧ False) ∧ True) → p2) → (True ∧ (True ∧ False))) → (((((p4 ∨ p5) ∨ p4) ∨ (((p5 → True) ∨ p2) ∧ p4)) ∨ (False → p4)) → p1)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h7 : (((p4 ∧ False) ∧ True) → p2) := by
            -- Implications on the right can always be decomposed.
            intro h8
            -- Conjunctions on the left can always be decomposed.
            let h9 := h8.left
            let h10 := h8.right
            -- Conjunctions on the left can always be decomposed.
            let h11 := h9.left
            let h12 := h9.right
            -- False on the left can always be used.
            apply False.elim h12
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h13 := h1 h7
          -- We need to get the right conjuct of h13 based on <expert-advice>.
          let h14 := h13.right
          -- We need to get the right conjuct of h14 based on <expert-advice>.
          let h15 := h14.right
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h17 : (((p4 ∧ False) ∧ True) → p2) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Conjunctions on the left can always be decomposed.
            let h21 := h19.left
            let h22 := h19.right
            -- False on the left can always be used.
            apply False.elim h22
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h23 := h1 h17
          -- We need to get the right conjuct of h23 based on <expert-advice>.
          let h24 := h23.right
          -- We need to get the right conjuct of h24 based on <expert-advice>.
          let h25 := h24.right
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h27 : (((p4 ∧ False) ∧ True) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h29.left
          let h32 := h29.right
          -- False on the left can always be used.
          apply False.elim h32
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h33 := h1 h27
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- We need to get the right conjuct of h34 based on <expert-advice>.
        let h35 := h34.right
        -- False on the left can always be used.
        apply False.elim h35
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h39 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h40 : (((p4 ∧ False) ∧ True) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h41
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- Conjunctions on the left can always be decomposed.
          let h44 := h42.left
          let h45 := h42.right
          -- False on the left can always be used.
          apply False.elim h45
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h46 := h1 h40
        -- We need to get the right conjuct of h46 based on <expert-advice>.
        let h47 := h46.right
        -- We need to get the right conjuct of h47 based on <expert-advice>.
        let h48 := h47.right
        -- False on the left can always be used.
        apply False.elim h48
      case inr h49 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h50 : (((p4 ∧ False) ∧ True) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h51
          -- Conjunctions on the left can always be decomposed.
          let h52 := h51.left
          let h53 := h51.right
          -- Conjunctions on the left can always be decomposed.
          let h54 := h52.left
          let h55 := h52.right
          -- False on the left can always be used.
          apply False.elim h55
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h56 := h1 h50
        -- We need to get the right conjuct of h56 based on <expert-advice>.
        let h57 := h56.right
        -- We need to get the right conjuct of h57 based on <expert-advice>.
        let h58 := h57.right
        -- False on the left can always be used.
        apply False.elim h58
  case inr h59 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h60 : (((p4 ∧ False) ∧ True) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h61
      -- Conjunctions on the left can always be decomposed.
      let h62 := h61.left
      let h63 := h61.right
      -- Conjunctions on the left can always be decomposed.
      let h64 := h62.left
      let h65 := h62.right
      -- False on the left can always be used.
      apply False.elim h65
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h66 := h1 h60
    -- We need to get the right conjuct of h66 based on <expert-advice>.
    let h67 := h66.right
    -- We need to get the right conjuct of h67 based on <expert-advice>.
    let h68 := h67.right
    -- False on the left can always be used.
    apply False.elim h68



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157736780020597154984520108047 : (((p5 → (((p1 ∨ p2) → ((True → ((True ∧ p4) → p1)) ∨ False)) → p2)) → (False ∧ (False ∨ p2))) ∨ ((p3 → (p4 → False)) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148981195389091328673107173728 : (((p3 ∧ (p1 ∧ p4)) ∧ (p2 → (((p4 → True) ∧ ((p5 ∧ (p4 ∨ (False ∨ p3))) ∨ p5)) → (False ∨ False)))) ∨ ((p1 ∧ p2) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53022396776412269342586728803 : ((((p1 ∧ ((p3 → p1) → p1)) ∨ ((True ∧ (p1 ∧ p2)) ∨ p5)) ∧ ((((True ∧ (True → p3)) ∨ p2) → ((p1 ∧ p2) ∧ p1)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192221740295591393195739739396 : ((((p1 → ((p3 → p3) ∨ (True ∧ p2))) → p2) ∧ p5) → (p4 ∨ ((True ∧ ((p3 ∧ p4) ∧ True)) ∨ (p1 → ((False ∧ (p2 ∧ p2)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258132948843807731243187874446 : ((p4 ∨ p3) → (True ∧ ((False ∨ (False ∨ p5)) → ((p1 → (False ∧ (False ∧ ((p3 → (p5 ∧ ((True → p2) → (p2 ∧ p4)))) ∨ p2)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718574879991545179898130304665 : (((((p5 → (p1 ∧ p5)) → p3) ∨ (((True → p3) → (True → ((p3 ∧ (p1 → ((((True ∨ False) ∨ p3) ∧ p1) ∧ p3))) ∧ True))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322860829492116602462010440586 : (p5 ∨ (((((p4 → True) ∧ (p2 ∧ p5)) → p2) → ((False ∨ (True ∧ (p1 → (False ∨ (((False → p4) ∧ p1) → True))))) ∧ (p4 ∧ p2))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → True) ∧ (p2 ∧ p5)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137705960850876713565921058747 : ((p1 ∨ ((p3 ∨ (((True ∧ (p5 ∧ p3)) → p3) ∨ ((p2 ∨ False) ∧ p4))) ∧ (((p1 → (True ∨ False)) → p5) ∨ p3))) ∨ ((p2 ∧ p2) → p2)) := by
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
theorem thm_5_vars_143191171248348583467813669859 : ((p2 → (((p3 ∨ (False → (((p1 → (p5 ∧ p1)) → p4) → p3))) → ((True ∨ p1) ∧ False)) → ((False ∧ p3) ∨ p4))) → (p5 → (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



