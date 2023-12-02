variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167013826950617560641770246661 : (((p3 → ((p2 ∧ (p2 ∧ ((p1 ∧ (p2 ∨ False)) → ((p4 ∧ p4) ∨ True)))) → p1)) ∧ p1) → (((p3 ∨ (p1 ∨ p2)) → p3) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246437911677346443237567615202 : ((p5 ∧ False) ∨ (((False ∨ p1) ∨ ((((p3 ∧ (((True ∨ p1) ∨ p2) ∧ (p5 ∧ p2))) → p1) → (p4 ∨ (True ∨ (p3 → p4)))) ∨ False)) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136353806010229250336351932882 : (((p3 → (p2 → (p2 ∧ p5))) ∧ (((True → (((p4 → (p3 ∨ (True ∨ (True ∨ p3)))) ∨ True) → p5)) → p3) ∨ False)) ∨ (p2 ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171637850435210457815344421261 : ((((p3 ∧ p3) ∨ (False ∨ (p2 → ((p2 ∨ (p3 → False)) → (p1 ∨ p2))))) ∨ True) ∨ (p2 ∨ ((((False ∨ (p1 ∨ p2)) → p3) ∨ True) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67873233778157773075176471475 : ((p2 → (((False ∧ (True → (((p4 ∧ p5) ∧ ((False → p2) → p3)) → p2))) → (p4 → ((False → True) → True))) → ((p4 ∨ p1) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47607699048616655579319225068 : (((p4 → ((False ∨ ((True ∨ (((p5 ∧ (p2 ∨ True)) ∧ True) ∧ ((p4 ∧ (p4 ∨ p3)) ∧ p5))) → True)) ∧ (p3 ∨ p2))) ∨ (p2 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785326104568772150168440202337 : (((p4 ∨ ((((p2 ∨ p4) → (((p2 → False) → p3) → (((p1 ∨ p3) ∨ ((p2 → p5) → ((p3 ∧ p3) → p1))) ∧ p5))) ∧ p1) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_300056740114797398180773112924 : (False ∨ ((((True ∧ p4) ∨ ((p3 ∧ (p1 → p2)) ∨ (p4 ∧ (((p3 → ((p4 ∨ (p4 ∧ True)) → p3)) ∧ True) ∧ p4)))) ∧ p4) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243934834833892788138702916104 : ((True ∧ False) ∨ (p1 → (((p1 ∧ ((False ∨ ((p3 ∧ p2) → ((p1 → True) → p5))) ∧ (p3 ∨ (p2 ∨ p4)))) ∨ p1) ∧ (False → (p3 → p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347076756308640322538227748497 : (p3 → (((((p5 → False) ∧ p3) ∨ ((True → False) ∨ p4)) ∨ ((True → False) → p5)) ∧ (((p4 ∧ p1) ∧ p4) ∨ (False → ((p3 ∧ False) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185278556674561513308844751451 : ((p2 ∧ ((p2 → (((False ∨ p4) ∨ True) ∨ (p3 ∧ p2))) ∧ p4)) ∨ (p4 ∨ ((False → p4) ∨ ((p2 ∨ (p4 → (p3 ∧ (p4 ∧ p2)))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229031655833767614553528648015 : ((p5 ∨ (False ∨ False)) ∨ (((((True ∨ p1) → p5) ∨ (p1 → ((p2 → p4) → ((p4 ∧ p3) ∨ p1)))) ∨ (p3 ∧ p3)) ∨ ((p4 → True) → p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336256063627539933429851432200 : (p1 → ((((((((p2 ∨ p1) ∨ p5) ∧ p4) ∨ True) → (((False ∨ p3) ∧ p4) ∧ False)) ∧ True) → (((p1 ∧ (p1 ∧ p3)) ∧ p1) → p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : ((((p2 ∨ p1) ∨ p5) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732991912056781491412987381525 : ((((p2 ∧ p4) ∧ ((p5 → (p4 ∨ ((((p4 ∧ (p5 ∧ (p4 → p3))) ∨ False) ∨ ((False → True) → p1)) ∧ ((True ∨ True) → p1)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49225497015406415175055841959 : ((((p3 ∧ False) ∨ (((((p4 ∧ (p5 ∧ True)) ∨ p3) → p3) ∧ (True ∧ (((p3 → p5) → p1) ∧ p1))) ∧ p4)) ∨ (p5 → (p3 → p3))) ∨ p1) := by
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
theorem thm_5_vars_303848889559495403842404078951 : (p1 ∨ (((((p2 → False) ∧ ((True ∨ p5) → (p1 ∨ (p5 → ((p3 → p2) ∨ p5))))) ∧ (True ∧ (p4 ∨ (False ∧ p4)))) → (p2 → p3)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112263182825951286206953664783 : (((p5 ∨ (((((((p4 ∧ p5) ∧ (False → p2)) ∨ (p5 ∨ p2)) ∨ ((p5 → p4) ∨ p5)) → (p5 → p3)) → p3) → p2)) ∨ False) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624715343455464403458267005229 : ((((p4 ∨ (p5 ∨ (p2 → ((((((p5 ∧ p5) ∧ p3) ∨ False) ∨ ((p4 ∧ p2) ∧ True)) ∧ p1) ∨ (False → ((p1 ∧ p4) ∧ p5)))))) ∨ False) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249066548316693887917710308694 : ((p4 ∨ p1) ∨ ((((p1 ∨ (True ∧ ((((False ∨ True) → p3) ∧ (p3 ∧ p5)) → False))) ∨ p5) ∧ p1) ∨ (((p3 → p5) → (p4 ∧ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112116536137742518171980668474 : ((((p4 → p5) → (p2 ∨ ((((False ∨ (p3 ∧ ((p5 ∨ p2) ∧ (p5 ∨ p2)))) ∨ p5) → (True ∨ (p5 ∧ True))) → False))) ∨ True) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262133530947496145009723894712 : (True ∧ (((p1 → ((((p3 → ((p4 ∨ p4) ∧ False)) ∧ (p3 ∨ (((False → (False → (p5 ∨ p1))) ∨ p2) ∧ False))) ∨ p5) ∨ True)) ∧ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164628584322876388015840331866 : (((False ∨ ((p3 ∨ True) → ((True ∧ ((p1 ∨ p3) ∨ p2)) → (p4 ∧ (p3 → p2))))) ∧ p4) ∨ ((p2 ∨ (False → (p5 → (p2 ∨ p1)))) ∨ p2)) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307183999857380351244672036050 : (p1 ∨ (p1 ∨ ((p5 ∨ ((((p3 → (((True ∨ p3) ∨ ((((False ∨ p2) ∧ p1) ∨ p1) ∨ (False ∨ False))) ∨ p2)) ∨ p3) → p1) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37490555207901327848982146929 : ((((((p3 ∧ True) ∨ p1) ∨ (p5 ∨ ((((p5 ∨ True) ∨ (((p5 ∧ p3) → False) ∨ p4)) ∧ (p2 ∧ (True → p1))) → p1))) ∨ False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157700068311488560218605067033 : (((((p3 → p2) ∨ ((p1 ∨ (p1 → p2)) ∨ (p3 ∧ (p4 ∧ p4)))) ∨ False) → (p5 ∨ (p4 ∧ p1))) ∨ ((True → (p5 ∨ False)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226259645258886136288588227087 : (((p3 ∨ p4) ∨ False) ∨ (((p3 ∨ p2) ∧ p5) ∨ ((p4 → True) ∨ (p4 → (p5 ∨ (((True ∨ (p4 ∨ (p5 ∨ p1))) ∧ p4) → (p5 ∨ False))))))) := by
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
theorem thm_5_vars_773945324802594915619247919985 : (((False ∨ ((p3 → ((p4 ∨ ((p2 ∧ p4) ∧ ((((False → (p3 ∧ p2)) ∨ p2) ∧ (p2 → (p4 ∧ p1))) → (p4 ∧ False)))) ∧ p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299142967983640714941139059397 : (False ∨ ((((p1 ∨ ((p4 → False) ∨ True)) ∧ ((p4 ∧ p4) → (p5 ∨ ((p3 → ((p5 ∨ p2) ∨ True)) ∨ ((p5 → p2) ∧ p1))))) ∨ False) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246083290234715223565264519481 : ((p4 ∧ p1) ∨ ((((False → (((p2 → p4) → (p4 ∨ True)) ∨ p5)) ∧ p5) ∧ ((p4 ∨ (((p4 ∨ p5) → False) → p3)) → p4)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258776193368692007568201083630 : ((True → False) → ((True ∧ (p2 ∧ (((p5 ∧ p2) ∧ p5) ∧ ((p1 ∨ (True → ((True ∧ ((False → True) ∧ False)) → True))) ∧ p5)))) ∨ (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160780320609757663395749049542 : (((p2 → (((p4 → True) → p5) ∧ True)) ∧ ((p2 ∧ p5) ∧ ((True ∧ (p4 → p4)) → (p2 ∨ p1)))) → ((p2 → ((p3 → False) ∨ True)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660556458571489083099938760339 : ((((((((True → (p4 ∨ True)) → (p2 → p4)) ∧ ((((p5 ∧ p5) → (p4 → (True → True))) ∨ p2) → p1)) → p3) → p2) → (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172143625057098671776273541703 : (((p1 ∨ (p4 ∨ (p1 ∧ (((True ∨ p3) ∧ p2) ∨ p5)))) ∧ (p2 → (p1 → p2))) ∨ ((p3 ∨ (True → (p3 → p3))) ∧ ((True ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118702560655717847867577300698 : ((p5 ∨ ((((((p2 ∧ (False → p4)) ∨ ((p4 ∧ (p2 ∧ (False ∨ False))) → ((True ∨ False) → p3))) ∨ p1) ∧ p5) → p4) → p2)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180080278916687437432091560874 : (((p5 → (((p5 ∧ p3) ∧ (p3 ∧ True)) ∨ (p3 ∨ (True ∧ p1)))) ∨ p2) → (p1 ∨ (True ∧ ((p2 ∨ (p4 → p4)) ∧ (p1 → (False ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59237924506393283066903882467 : (((p2 ∨ p2) ∨ (((((((((p4 ∧ p4) ∧ True) → p3) ∧ True) → (p1 → True)) ∨ p2) ∨ ((True → (True ∨ p4)) ∧ p1)) → p4) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54357642316581280079869012610 : (((p3 ∨ (p4 ∧ (p2 ∧ (p2 ∨ (True → p1))))) ∧ (((((p4 ∧ True) → (False ∧ False)) ∧ (False → True)) ∨ (True → (p1 → p1))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149701850613626127115414101763 : ((p5 ∧ ((p1 ∨ p2) ∧ (((False ∧ True) ∧ (p5 ∧ ((False → p1) ∨ ((True ∨ (p1 ∨ p4)) → p3)))) → p4))) ∨ (False ∨ (True ∧ (p4 ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231496764613379442316409440478 : (((p3 → p4) ∨ p3) → (((((p3 → ((False ∧ (True ∨ ((((p4 ∨ p2) ∧ p4) → p3) ∨ True))) ∨ p3)) ∨ False) → (p3 ∧ p2)) ∧ True) ∨ True)) := by
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
theorem thm_5_vars_183829173839391689186669473970 : ((((p4 ∧ ((p4 ∨ (True ∨ p1)) ∧ (p4 → False))) → p1) ∧ p2) ∨ ((p1 ∨ ((p1 → (False ∨ True)) → (True → ((p4 ∧ p4) ∨ True)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337865023871023910539820265635 : (p1 → (((p2 → (p1 ∧ p3)) ∧ ((((False ∧ (p2 ∨ False)) ∨ p2) ∧ p2) ∧ p1)) ∨ (((False ∨ ((p3 ∧ False) ∨ p2)) → (p5 ∧ p4)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257480213606962937206534176296 : ((p3 ∨ True) → (p4 → ((p2 ∧ p3) ∨ (p2 ∨ (p3 ∨ ((False ∧ (True ∨ ((False → (p4 ∨ p3)) → p5))) → (p5 ∨ (p2 → (True ∨ p2))))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356055942168447155828753074788 : (p5 → (((((False ∨ (p2 ∧ ((False ∧ p3) ∨ (False ∧ p3)))) ∨ p2) ∨ ((False → False) ∨ (p3 → p4))) ∧ p4) → (((False ∨ p1) ∨ p3) ∨ True))) := by
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
    cases h5
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
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354859187057053287099560755307 : (p5 → (((p2 ∨ p2) → (((((p2 ∨ p1) → (False ∨ (p2 → (p3 ∧ p4)))) ∨ (True → p3)) ∧ p1) ∨ (p1 → ((p5 ∨ p4) ∨ p3)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136106288943921968193290322036 : (((((p5 ∨ False) ∧ True) ∧ ((True ∧ True) ∧ p3)) ∨ (((p2 → p3) → p3) ∧ (False ∧ (True ∨ ((p3 → p1) ∨ p2))))) ∨ ((p2 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146720587146004490814644008931 : ((p2 → (((p4 ∧ (p1 ∨ (p2 ∨ (p3 ∨ (p2 ∧ p4))))) ∨ (((True ∨ (False ∧ p2)) ∨ p2) ∨ p4)) ∨ False)) ∧ (((p1 ∨ p5) ∧ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328665908190040786356975080664 : (True → ((((((p1 → p2) → (p2 ∨ p4)) ∨ p3) ∧ (p3 → p5)) ∨ True) ∧ ((p5 ∧ ((p4 → p1) ∨ (((p1 ∨ False) → p3) → True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_167494770589053285572535366716 : (((((True ∨ p1) → (((False ∨ p3) ∨ False) ∧ ((True ∧ p2) ∨ p3))) → False) ∧ (p3 ∨ p3)) → (((p5 ∨ p2) → (p5 ∧ (True → p2))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h12 : ((True ∨ p1) → (((False ∨ p3) ∨ False) ∧ ((True ∧ p2) ∨ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h18 := h9 h12
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h20 : ((True ∨ p1) → (((False ∨ p3) ∨ False) ∧ ((True ∧ p2) ∨ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h26 := h9 h20
      -- False on the left can always be used.
      apply False.elim h26
  -- Implications on the right can always be decomposed.
  intro h27
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h32 : ((True ∨ p1) → (((False ∨ p3) ∨ False) ∧ ((True ∧ p2) ∨ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h33
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h35 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h38 := h29 h32
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h40 : ((True ∨ p1) → (((False ∨ p3) ∨ False) ∧ ((True ∧ p2) ∨ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h41
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h43 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h46 := h29 h40
      -- False on the left can always be used.
      apply False.elim h46
  case inr h47 =>
    -- Conjunctions on the left can always be decomposed.
    let h48 := h1.left
    let h49 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h49
    case inl h50 =>
      -- One of the premise coincides with the conclusion.
      exact h47
    case inr h51 =>
      -- One of the premise coincides with the conclusion.
      exact h47
  -- Conjunctions on the left can always be decomposed.
  let h52 := h1.left
  let h53 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h53
  case inl h54 =>
    -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
    have h55 : ((True ∨ p1) → (((False ∨ p3) ∨ False) ∧ ((True ∧ p2) ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h56
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h54
      case inr h58 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h54
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h59 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h54
      case inr h60 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h54
    -- We have shown the premise of h52, we can now drive its conclusion.
    let h61 := h52 h55
    -- False on the left can always be used.
    apply False.elim h61
  case inr h62 =>
    -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
    have h63 : ((True ∨ p1) → (((False ∨ p3) ∨ False) ∧ ((True ∧ p2) ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h64
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h65 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h62
      case inr h66 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h62
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h67 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h62
      case inr h68 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h62
    -- We have shown the premise of h52, we can now drive its conclusion.
    let h69 := h52 h63
    -- False on the left can always be used.
    apply False.elim h69



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197126227183224637683762408507 : (((p3 ∨ ((p2 ∨ p5) → (p2 ∨ p1))) ∨ p5) ∨ (p3 ∨ ((((False → p5) ∧ p5) ∧ p2) → (p2 → ((p5 → (False ∧ True)) → (p4 ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35394189248281622067227133376 : ((p2 → (((((p3 → False) ∧ ((p5 ∧ p1) ∨ p3)) ∨ (p1 ∨ (p1 ∨ (((p4 → False) ∧ (p2 ∧ True)) → (p3 ∧ p4))))) → p5) ∨ p2)) ∧ True) := by
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
theorem thm_5_vars_114647807287386805660206469739 : (((((((p4 → False) ∨ (p3 ∧ p1)) ∨ (True ∧ p5)) → False) ∧ (p3 ∨ (p2 ∨ p1))) ∨ (True ∨ ((p4 → p4) ∧ (True → True)))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809947869748268598088041347117 : (((p5 → (((p2 ∨ (p5 ∧ (p4 ∨ (p2 ∨ ((True ∧ (p1 ∧ (p5 ∧ (p1 ∨ (p1 ∧ False))))) → p4))))) ∨ p1) ∨ ((False → p3) ∨ p3))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347494871539663612764242244673 : (p3 → ((p5 ∧ (True ∧ ((p4 ∨ p5) ∧ p3))) ∨ ((p2 → (False ∨ ((True ∧ p1) ∨ ((p1 ∨ p4) → True)))) ∨ (p2 → (p4 ∧ (p5 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112758428141475092890582150969 : ((((True → ((((p2 → (p5 ∨ p3)) → p4) ∨ p5) ∧ p2)) ∧ (((True → True) → (p1 ∧ p4)) ∨ ((p4 ∧ p3) ∨ p5))) → p2) ∨ (False ∨ p3)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782824288250457356684761138823 : (((p3 ∨ ((p3 ∧ (p1 → (((p4 ∨ p5) → ((((p1 ∧ (((p3 → p2) ∧ (p4 → p1)) ∧ p2)) → True) ∧ p5) ∧ p1)) → p4))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134268688069230344054401890689 : ((((False ∧ p5) ∧ ((((p2 ∧ p4) ∧ p1) ∨ (((p2 → (p2 → False)) → (p2 ∨ p5)) ∨ p2)) ∧ (p5 ∧ p2))) ∨ False) ∨ ((p2 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246132156080634700790563939198 : ((p4 ∧ p2) ∨ (((p3 ∨ ((p3 ∧ ((p5 ∨ True) ∧ (True → ((p4 ∧ False) ∧ p2)))) ∧ (p3 → (p4 ∧ (p1 → p2))))) ∧ (p1 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166488895347021422401225492290 : ((p3 ∨ ((p2 ∨ (p3 ∧ (p2 ∧ p4))) → (((p3 → ((p4 ∨ p3) → p1)) ∨ p5) ∨ p3))) ∨ (((((False → True) ∧ p2) → p2) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354575121685273687244620286461 : (p5 → (((((p5 → p4) ∨ (((p3 ∧ (p5 ∨ (p1 → p4))) ∨ p1) ∧ (p3 ∧ p4))) ∧ (p3 → ((p1 → p4) → (True → p4)))) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20177490072470193032134897899 : ((((p4 ∨ (False ∧ ((False ∨ (((p1 ∨ True) ∧ p3) ∨ True)) ∧ p5))) ∨ True) ∨ ((((p5 ∨ p5) ∨ (p2 ∧ (p2 → p3))) ∧ False) ∨ False)) ∧ True) := by
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
theorem thm_5_vars_596785653812213798674267566138 : ((((((((True ∧ p4) ∧ True) ∧ False) ∧ p5) ∨ ((((p2 ∨ p2) → p1) → (p5 → (p3 ∨ ((p3 → (p1 ∧ True)) → p3)))) ∧ p1)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62754096623920483514007377886 : ((p4 ∧ ((p2 ∧ (((p2 → p4) ∧ p3) ∨ (((((p3 ∨ (p4 ∧ (p5 ∧ p5))) ∧ (p3 ∧ p4)) ∨ p1) → p5) ∧ p1))) → (p4 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226218113480361398466720380912 : (((p2 ∨ p3) ∨ p4) ∨ (True → (((p4 → ((p3 ∧ (True → (p3 → p1))) ∨ ((False ∧ (p1 → (p5 ∧ p3))) → p2))) ∧ False) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_114990854651241176046936357289 : ((((((p4 ∨ p4) ∨ p1) ∨ (False → (p1 → p3))) ∧ (p1 ∧ p1)) ∧ ((((False ∧ p3) ∧ p1) → p2) ∨ (p1 ∧ (p2 ∨ p2)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791333667611800404897758195005 : (((True → (((p4 ∨ ((False ∨ ((True ∧ (p1 → ((True → p3) ∨ ((p5 → True) → p3)))) ∨ True)) ∧ ((p4 ∨ True) ∧ True))) → p1) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191269237345569794869723233041 : (((False ∨ p1) ∧ ((p4 ∨ p4) ∧ ((False ∨ True) ∧ p5))) ∨ (p1 → ((False ∧ p1) → ((p4 → (((False ∧ (p5 ∧ p2)) ∧ True) ∨ False)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173966516151010528234708748525 : ((((((p2 ∨ p1) ∧ p2) ∧ p2) → ((((p5 ∨ False) → False) ∨ p1) ∨ False)) → True) → (((False ∨ (p4 → (p3 ∧ (p3 → p2)))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715625472365393849592470764739 : (((((p5 ∨ (p5 ∧ p3)) ∧ False) ∧ (p5 → (((p1 → (p5 ∧ False)) → ((False ∧ ((p5 ∨ p2) ∧ p2)) ∧ True)) ∧ (True ∨ (p4 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706674057825052170972193258204 : ((((p4 → (p2 → ((False → False) → (p4 ∧ p5)))) ∧ ((((False → (p2 ∧ p2)) ∧ p2) → ((p4 ∨ p5) → p1)) → ((p2 ∧ p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180959223723648984766325681552 : (((True → False) ∧ ((True ∨ ((((True → p4) → p4) → False) ∨ p3)) ∧ p5)) → ((((p4 ∧ p1) ∨ False) ∨ (False ∨ ((p1 → p5) → False))) ∧ p1)) := by
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- False on the left can always be used.
      apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h22 := h16 h21
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h26 := h16 h25
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h29 := h16 h28
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759168910203369674000689573842 : (((p2 ∧ (((p5 → ((p3 ∧ (p3 ∨ p4)) ∧ (p3 ∧ ((((p4 → p3) ∧ ((p1 ∨ p1) ∨ False)) ∨ False) → p2)))) ∨ p3) ∨ (False → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192995958698611758540909641564 : ((((p1 ∧ (p2 → (p5 → False))) ∨ True) → (p1 ∧ False)) → (((p4 → p1) ∧ (((p1 ∨ p4) ∨ p1) ∧ ((p4 ∧ False) ∨ (p3 ∨ p5)))) → p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h8
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h21 : ((p1 ∧ (p2 → (p5 → False))) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h22 := h1 h21
          -- We need to get the right conjuct of h22 based on <expert-advice>.
          let h23 := h22.right
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h25 : ((p1 ∧ (p2 → (p5 → False))) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h26 := h1 h25
          -- We need to get the right conjuct of h26 based on <expert-advice>.
          let h27 := h26.right
          -- False on the left can always be used.
          apply False.elim h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h34 =>
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60775758352611207275544240983 : ((True ∧ ((p5 → p2) ∨ (True → ((((p2 ∧ p3) → True) ∨ p2) → ((p4 ∧ p5) → ((((True ∧ (p5 ∧ p2)) ∨ p4) ∨ p5) → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165347052188839818065559952621 : ((((False ∨ p4) ∧ (((p4 ∨ (p1 ∧ p2)) ∧ p2) ∧ (p1 → False))) ∧ ((True ∧ p1) → True)) ∨ ((False → (p4 ∨ p5)) ∨ ((p3 ∧ p2) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57944266495908027857371406629 : (((False → (p4 → p2)) → (((p4 → (p5 → False)) → ((p2 ∧ (p3 ∧ p3)) ∧ (((((p4 ∧ p2) ∧ p3) → p3) ∨ p1) ∨ p5))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186962473113587722539085939084 : ((((p3 ∨ True) → False) ∨ (p3 ∧ ((p4 ∧ p4) ∧ (p4 → False)))) → (((p5 ∨ p2) ∨ ((True ∨ (True → (False → p3))) ∧ p2)) → (p3 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h6 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h7 := h5 h6
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h17 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h18 := h16 h17
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h22.left
        let h25 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h30 =>
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Conjunctions on the left can always be decomposed.
        let h38 := h36.left
        let h39 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h34
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h41 =>
        -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
        have h42 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h41, we can now drive its conclusion.
        let h43 := h41 h42
        -- False on the left can always be used.
        apply False.elim h43
      case inr h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h44.left
        let h46 := h44.right
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h47.left
        let h50 := h47.right
        -- One of the premise coincides with the conclusion.
        exact h45
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h51 =>
    -- Disjunctions on the left can always be decomposed.
    cases h51
    case inl h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h53 =>
        -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
        have h54 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h53, we can now drive its conclusion.
        let h55 := h53 h54
        -- False on the left can always be used.
        apply False.elim h55
      case inr h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- Conjunctions on the left can always be decomposed.
        let h59 := h58.left
        let h60 := h58.right
        -- Conjunctions on the left can always be decomposed.
        let h61 := h59.left
        let h62 := h59.right
        -- One of the premise coincides with the conclusion.
        exact h62
    case inr h63 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h64 =>
        -- We want to use the implication h64 based on <expert-advice>. So we show its premise.
        have h65 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h64, we can now drive its conclusion.
        let h66 := h64 h65
        -- False on the left can always be used.
        apply False.elim h66
      case inr h67 =>
        -- Conjunctions on the left can always be decomposed.
        let h68 := h67.left
        let h69 := h67.right
        -- Conjunctions on the left can always be decomposed.
        let h70 := h69.left
        let h71 := h69.right
        -- Conjunctions on the left can always be decomposed.
        let h72 := h70.left
        let h73 := h70.right
        -- One of the premise coincides with the conclusion.
        exact h73
  case inr h74 =>
    -- Conjunctions on the left can always be decomposed.
    let h75 := h74.left
    let h76 := h74.right
    -- Disjunctions on the left can always be decomposed.
    cases h75
    case inl h77 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h78 =>
        -- We want to use the implication h78 based on <expert-advice>. So we show its premise.
        have h79 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h78, we can now drive its conclusion.
        let h80 := h78 h79
        -- False on the left can always be used.
        apply False.elim h80
      case inr h81 =>
        -- Conjunctions on the left can always be decomposed.
        let h82 := h81.left
        let h83 := h81.right
        -- Conjunctions on the left can always be decomposed.
        let h84 := h83.left
        let h85 := h83.right
        -- Conjunctions on the left can always be decomposed.
        let h86 := h84.left
        let h87 := h84.right
        -- One of the premise coincides with the conclusion.
        exact h87
    case inr h88 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h89 =>
        -- We want to use the implication h89 based on <expert-advice>. So we show its premise.
        have h90 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h89, we can now drive its conclusion.
        let h91 := h89 h90
        -- False on the left can always be used.
        apply False.elim h91
      case inr h92 =>
        -- Conjunctions on the left can always be decomposed.
        let h93 := h92.left
        let h94 := h92.right
        -- Conjunctions on the left can always be decomposed.
        let h95 := h94.left
        let h96 := h94.right
        -- Conjunctions on the left can always be decomposed.
        let h97 := h95.left
        let h98 := h95.right
        -- One of the premise coincides with the conclusion.
        exact h98



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117823830175439958417696516745 : ((p4 ∧ (p2 ∧ (((False → (p5 → (p4 ∨ (((p3 → True) ∧ (True ∨ ((True ∧ p5) → p2))) → p2)))) ∧ (p3 ∧ p1)) → p2))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58746639452194024726396827777 : (((p3 → p5) ∧ (False ∧ (p1 → (p3 ∨ ((((p1 ∧ ((p2 → p4) ∧ (p3 ∨ (True ∧ p4)))) ∧ p1) → (False ∨ (p5 ∨ p2))) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804892728513190682640182269621 : (((p3 → ((p1 ∧ p5) ∨ (False ∧ (((p3 → p2) ∨ True) → ((((False ∧ (True ∧ p3)) ∨ (p5 → (p4 ∨ False))) ∧ (p4 ∧ p5)) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170923421604257331737531698104 : ((False ∨ (True ∧ ((True ∨ (((p5 ∧ False) ∧ p4) ∨ p2)) ∧ (p1 ∨ (p5 ∨ True))))) ∧ (((p4 ∨ p4) ∧ ((p2 ∧ p4) ∨ p5)) ∨ (True → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166198692499957759813111541288 : ((p1 ∧ ((False ∧ p2) ∧ (p4 ∧ (((False ∧ p5) ∧ True) ∧ (True ∧ (p4 ∧ (p1 → p3))))))) ∨ ((True → p4) → (p2 ∨ ((p5 → p5) ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703529058561178935199158392565 : ((((p1 → ((((p3 ∨ (p5 ∧ p3)) ∧ p4) ∨ True) ∧ p5)) ∨ ((((True ∧ (((p5 → p4) ∧ p4) ∧ (p4 ∧ p5))) ∨ False) ∨ True) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171542088769028854123198729424 : ((((p5 ∨ (p3 ∧ ((True ∨ False) → ((p4 ∨ p3) ∨ (p3 → p4))))) ∨ False) ∨ p3) ∨ ((True → p2) → ((p3 ∧ (p5 ∨ (False → False))) → p2))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134918223293784492672398472770 : (((((True ∨ (p3 ∨ (p1 → p2))) → (p2 → ((p3 ∨ (False ∨ ((p4 ∨ False) → False))) ∧ False))) ∨ p1) ∧ (p5 ∨ p2)) ∨ ((p2 → p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337151188799298215926134977704 : (p1 → ((p5 → (((False ∧ p3) → (p1 ∨ p3)) ∧ ((((p5 ∨ p2) → p4) ∧ p1) → ((p2 ∧ True) ∨ (p3 ∧ (p4 ∧ p1)))))) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735275118352762254272404163023 : ((((p4 ∨ True) ∧ (((((p5 ∧ p5) ∨ p2) → (p1 ∨ ((False ∨ p4) ∨ (((False ∧ (p1 ∨ p5)) ∧ (p4 ∧ p4)) ∧ p5)))) ∧ p1) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_784959160887446959122791997404 : (((p3 ∨ (p4 → ((((p5 → ((p1 ∨ (p4 ∧ True)) ∧ True)) ∨ (False ∨ p1)) ∧ ((p3 ∨ p4) ∧ (True ∧ ((p2 ∨ p2) ∧ p4)))) ∨ p4))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115705909154455032897354703976 : ((((True ∧ ((p2 ∨ p4) ∨ p3)) ∧ p3) → (((p1 ∨ ((p5 ∧ (p1 ∧ p5)) ∨ (p2 ∧ p5))) ∨ p4) → ((True ∧ p2) ∧ p5))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226881273112997827532110220295 : (((p5 ∧ p2) → p4) ∨ (((p3 ∨ p3) → ((p3 ∧ (True ∧ (False ∧ ((False ∧ p2) ∨ p4)))) ∧ p3)) ∨ (p2 → ((p2 ∧ (p2 → False)) → p4)))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213158705631685655907658703258 : ((((p2 ∧ p4) ∨ p2) ∧ p3) ∨ ((((p5 ∨ p4) ∨ p4) ∨ (False → (p3 ∨ p4))) ∧ (p2 ∨ ((False ∧ p1) ∨ (False → (p5 ∨ (False → False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50872779845127422004260982180 : ((((p4 → ((p3 ∨ ((True ∨ False) ∨ True)) → (((p5 → p3) → (p4 ∧ p2)) ∧ False))) ∨ p4) ∧ (p4 → (p3 → (False → (p4 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133753976554618226310898617604 : ((((((False ∨ p4) ∧ (p3 ∧ p3)) ∧ p5) ∧ (((p2 → p5) ∧ (((True ∨ p2) ∧ p5) ∧ (True ∧ True))) → True)) ∧ p2) ∨ (True ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218442039105618708768596358804 : (((p3 ∧ p3) → (p1 ∨ p3)) → (((p4 → True) → (p1 → p3)) → (p2 → ((p3 → (p5 → ((p5 ∧ ((p3 → p4) ∨ p4)) → False))) ∨ p2)))) := by
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
theorem thm_5_vars_41025327393330620029938190082 : (((((((p1 → (p1 ∧ (False ∧ p1))) ∨ (True → (p2 ∧ p4))) → (False → (p3 ∨ (p4 → True)))) ∧ (p1 ∨ p5)) → (p3 ∨ p4)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133469103651766216055518572160 : ((p5 → (((((True ∧ p1) ∨ ((((False → p4) ∧ p5) ∧ (p3 → p4)) ∨ p5)) ∧ p2) → False) ∨ ((p2 → p5) ∨ p2))) ∧ ((True ∨ p4) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40281098149111939684825115754 : ((((p1 → ((p2 ∧ (p3 ∨ p5)) ∨ (((p1 → p3) ∧ ((p5 ∨ True) → (False ∧ p2))) ∧ (p5 ∧ (p5 → (p5 ∨ p3)))))) ∧ p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68067770895579844164917159375 : ((p2 → (p1 ∨ (((p5 ∨ False) ∨ (p4 ∨ True)) → (p1 ∧ (p2 → ((p4 ∨ ((p5 ∨ p5) → p4)) ∨ ((p5 → False) ∨ (p4 ∨ p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57448213572436954632833907635 : (((p4 ∨ (p4 → False)) ∨ (p5 ∧ (False ∧ ((((((((p1 → p3) → p1) ∧ (p2 → True)) ∨ False) ∧ (p1 → p5)) → p5) → True) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179142456820675655643225245870 : ((p1 ∧ (p5 ∨ (((p5 ∨ (False ∨ ((p2 → True) ∨ p2))) → p4) → p5))) ∨ (True → ((p2 ∧ ((p3 → (False ∧ p3)) ∨ (p2 → p4))) → p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731821476481650172533149979360 : ((((p4 → (p1 ∧ p5)) → (p1 ∨ ((p4 ∧ ((True ∨ (((p5 ∨ p1) → ((True ∨ p5) ∨ (p2 → True))) ∨ (p2 ∨ p5))) ∨ True)) → p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h12 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h13 := h1 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h17 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h18 := h1 h17
          -- We need to get the right conjuct of h18 based on <expert-advice>.
          let h19 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h20
  case inr h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h24
  -- True on the right can always be proven directly.
  apply True.intro



