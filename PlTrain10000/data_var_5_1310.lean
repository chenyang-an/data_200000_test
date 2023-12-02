variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328180755581330944627471989048 : (True → (((((p4 → p4) ∧ p2) ∨ (p4 ∧ (False ∧ ((((p1 → p4) ∧ False) → p3) ∧ p1)))) ∧ (p3 → (p5 ∧ True))) → (p3 → (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87996686851798884994308083829 : (((((True → p1) ∧ p4) ∧ p4) ∧ ((p3 ∧ ((p5 ∨ p1) ∧ ((p1 ∨ (p5 ∧ (p1 → p4))) ∨ (p5 ∧ p1)))) → (p2 → (False ∧ p1)))) → p1) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351726827893002314801318716206 : (p4 → (((p1 ∧ ((p1 → (True ∧ False)) → ((p5 → p2) → p2))) ∧ (p1 ∧ p1)) ∨ (False ∨ (p4 ∨ ((p5 → p1) ∧ ((p3 → p2) → p4)))))) := by
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
theorem thm_5_vars_68734092148733855430408190259 : ((p4 → (((p4 ∨ (p2 → p1)) → ((((False ∨ (p1 ∨ p2)) ∨ p4) ∨ ((p3 → p3) ∨ False)) ∧ p3)) ∨ (((p2 ∧ True) ∨ p2) ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201274331270845563498996629111 : ((p3 → (p4 ∨ (p2 ∧ (p4 ∨ (p5 → p5))))) → ((((((p3 ∧ True) ∧ p5) ∨ (False ∧ (p2 ∧ False))) ∨ True) ∨ True) ∨ (p2 ∧ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328527181853553694293849949272 : (True → (((p1 ∧ p4) ∧ (p1 → ((((p4 ∧ p3) ∧ p2) ∧ ((True ∨ p2) ∨ p4)) ∨ p4))) ∨ (p4 → (False → ((p2 ∧ True) ∨ (p5 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224298547484923226877565960978 : ((False → (p5 ∧ p2)) ∧ ((((True → (p5 ∧ True)) ∧ (((p1 ∨ p4) → p4) ∨ p4)) ∧ (((p3 → p3) ∧ p5) ∧ (p1 ∨ False))) ∨ (p4 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312956033772747504805192891202 : (p3 ∨ ((((((p1 ∨ p2) ∨ (p2 ∧ p3)) ∨ (True ∨ ((p2 ∧ ((p3 ∨ p5) → (p5 ∧ (p5 ∨ True)))) → (p1 → p1)))) ∨ p3) ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_328537655849357983876357878970 : (True → ((p2 → (((((True ∨ (p1 → (p4 ∨ p5))) ∨ p3) → (True ∨ False)) → p5) ∧ False)) ∨ (((((False ∧ p1) ∨ p5) ∨ True) ∨ p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_706652032784504757268770580107 : ((((p4 → (((False → p4) → (True ∧ p3)) ∧ p1)) ∧ (((p1 → p3) ∧ ((p4 → (False → (p1 ∨ p5))) → ((p3 ∨ p1) ∧ p4))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151458694398828048558988933621 : (((((p3 ∨ (((p4 ∨ ((p4 ∧ p4) ∨ (True ∧ False))) → (True ∨ p1)) ∧ p5)) → p5) ∨ False) ∨ (p5 ∨ True)) → (False ∨ ((p2 ∨ p4) ∨ True))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624703777092566928634295482274 : ((((p4 ∨ (p2 ∨ (p5 ∧ (((p3 ∧ ((p2 ∧ ((p5 ∧ False) ∨ p3)) ∧ ((p3 ∧ p1) → p1))) → p5) → (p4 ∨ (p5 ∧ p2)))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_357260984006177954325142825506 : (p5 → ((p1 ∧ p5) ∨ (p4 → (True → ((False ∨ (p4 → ((p2 ∨ p1) ∨ (p3 ∧ ((p3 → (p3 ∨ p5)) ∧ ((p4 ∨ p1) ∨ False)))))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135974786136332719338794984163 : (((((True ∧ (p5 ∨ (p1 → (p3 ∧ p3)))) ∧ False) ∨ p1) ∨ (((p5 → p4) → False) ∧ (p3 ∨ (False → (False → True))))) ∨ (False → (p1 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811797144935850980588308523547 : (((p5 → (p5 → (((p1 ∨ (p2 ∨ p2)) ∨ p2) ∧ ((p1 ∧ (p1 → (True ∧ (p1 → ((p4 ∧ p1) → (p2 → True)))))) ∧ (p5 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226197836815039781914510692825 : (((p2 ∨ False) ∨ False) ∨ ((False ∧ p2) ∨ (p5 ∨ (p3 → (p5 ∨ ((p4 ∨ True) → (True ∨ ((p4 ∨ p1) ∧ ((p3 ∨ (p5 → p1)) → False))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337542688954221907267134858580 : (p1 → (((True ∧ (True ∨ p2)) ∧ (((p3 → p1) ∨ p1) → (((p4 → p5) ∨ (p4 → p2)) ∧ (p2 ∧ p2)))) ∨ (False → (p3 ∨ (p1 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165220483530685430574968690793 : (((((p1 ∨ (p2 ∧ (p1 ∧ p4))) ∨ p2) ∨ ((p4 ∨ (p1 ∨ True)) → p5)) ∨ (p1 → p1)) ∨ (((p2 ∨ True) ∨ (p2 ∨ (p1 → p5))) ∨ False)) := by
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
theorem thm_5_vars_774525700982954761854027539504 : (((False ∨ ((False ∧ ((p2 → ((False ∨ (p4 ∨ ((p3 ∧ True) → p4))) ∧ p4)) ∧ p2)) ∨ (((True ∧ True) → True) ∨ ((p5 ∧ p3) → True)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263573745164908808509584051781 : (True ∧ ((((p3 ∨ p4) ∨ p3) ∧ (p5 ∧ (((False ∧ p1) ∧ (((p3 → p4) ∨ p2) ∨ (p1 → p3))) → p2))) ∨ (((True ∧ p1) → False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190237055756649881703916080799 : ((((((p4 → (p5 ∧ p4)) → p1) ∨ p4) ∧ False) ∨ p3) ∨ ((p5 ∨ (p2 → (p2 → p5))) ∨ (True ∧ (False → ((p3 → (p3 ∧ p3)) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193223385546972559145079648043 : ((((p2 ∨ True) ∧ p2) ∧ (p2 ∧ ((p5 → True) → p4))) → ((p5 ∨ (p1 ∨ ((((p3 → (p2 ∨ p5)) → p3) → p4) → (p4 ∨ p2)))) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46383032309308336170903249288 : ((((p3 → (p3 ∧ (p3 ∧ ((p5 ∧ p1) ∧ (p3 ∧ p1))))) ∧ (((False ∧ (p1 → (False ∧ p2))) ∧ True) ∧ (p1 ∧ p4))) ∧ (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316688587328685903520648364976 : (p3 ∨ (p5 ∨ ((((False ∨ (p5 → ((((p2 ∨ (False ∧ p4)) → True) → True) ∧ True))) ∨ False) ∨ p2) ∧ (((p5 ∨ True) ∧ (p4 ∨ p1)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731252588109552044572405994723 : ((((p3 ∨ (p1 → True)) → (p4 ∨ ((p3 → (True ∨ ((((p2 → ((p2 ∨ True) ∧ (p1 ∨ p2))) ∨ p5) → False) → (False ∧ p2)))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60100409531920830296512373925 : (((p3 ∨ p1) → (((p1 ∧ (((p3 ∨ p5) ∧ (False ∨ p4)) ∧ False)) ∧ True) ∨ ((((((p4 ∧ p2) ∧ True) ∨ True) → p2) ∨ False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41284285852509639709237464588 : (((((p2 ∧ (True ∨ ((((p2 ∨ p1) ∧ p4) → (p5 → (p2 ∨ p4))) → p1))) → (True ∧ p4)) → (p1 ∨ (p5 ∧ (p5 ∨ True)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613668119108105109725208761236 : (((((((False ∨ (False ∨ True)) ∨ (((True → False) ∧ p5) ∨ True)) → ((((True → p3) → p5) → p5) → False)) ∧ ((p1 → p5) ∧ False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_49806182557539267429800025985 : (((False → (((False ∨ True) ∨ ((True ∧ ((((True → p1) → p2) ∧ (p1 ∧ p1)) ∨ True)) → p3)) ∧ (p4 ∧ p1))) → (p1 ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39774453174784112232950106654 : (((True → ((p5 → p1) → ((p3 ∧ p5) ∧ (((p5 → (((p3 → p1) ∨ p1) ∧ True)) ∨ (False ∧ p3)) → ((p4 ∨ p3) ∧ False))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135948068958095442179218993065 : ((((((p4 → p2) ∧ p1) ∧ p5) ∧ (False ∧ (p4 ∨ True))) ∧ ((False → ((True ∧ p5) ∨ (p3 ∧ (p3 ∨ p2)))) ∨ False)) ∨ (p5 → (False ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214483305188831284930087573108 : (((p1 ∧ p2) ∧ (p1 ∧ p5)) ∨ (((p4 ∧ (p3 ∧ p5)) → (((p3 ∧ p2) → p1) ∨ (True ∨ (p1 ∨ (False → ((False ∨ p3) ∨ p3)))))) ∨ p4)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139207378092711928656442139452 : (((((p3 ∨ p3) ∨ False) ∧ (((True ∧ (p4 ∨ (p1 → (p1 ∨ (p5 ∧ p3))))) ∨ ((True → False) ∨ p1)) ∨ True)) ∨ True) → (p5 ∨ (p3 → True))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Conjunctions on the left can always be decomposed.
            let h9 := h8.left
            let h10 := h8.right
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h12
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h14
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h17
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h19
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h28
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h29 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h30
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h31 =>
            -- Disjunctions on the left can always be decomposed.
            cases h31
            case inl h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h33
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h34 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h35
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h37
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h38 =>
      -- False on the left can always be used.
      apply False.elim h38
  case inr h39 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h40
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46909727545392693912727863596 : ((((((((p5 ∨ (((p4 ∨ p4) ∧ True) ∨ p4)) ∨ p3) → False) ∧ (p2 → p5)) ∨ ((p2 → p2) ∧ (p2 → p2))) ∨ p4) ∨ (False → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693096312678507339609452978638 : ((((p2 ∧ (p1 ∧ ((((p4 → p5) ∧ p5) ∧ False) ∧ (p4 → (p2 ∨ p1))))) ∧ ((p3 ∨ (p2 → False)) ∨ (True ∧ (False → (p4 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39093901820719424959197678838 : ((((True → p2) ∨ ((((p1 ∧ (p1 ∧ (p1 ∧ p5))) → ((p2 → (p5 → (p4 ∧ p5))) ∧ (p1 ∧ p1))) ∨ (p3 → p3)) → p3)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354838922562013399958352676348 : (p5 → (((p5 ∨ p5) ∧ (((((True ∨ True) ∨ ((p1 → p1) ∨ False)) → (p1 ∧ p1)) ∨ (p3 ∨ ((False ∨ (p4 ∧ p2)) → False))) ∨ p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751823222820419183407463402052 : (((True ∧ (False ∨ (True → ((((False → p5) → p2) ∨ ((p3 ∨ ((p3 ∧ ((p3 → p3) ∨ p3)) ∨ p1)) ∨ (True → (p4 ∧ True)))) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136168943042701009922416595056 : ((((((p3 ∧ p3) ∧ p5) ∨ p3) ∧ True) ∧ (((p2 ∧ (p4 → False)) → p2) ∨ (((p4 ∨ (p1 ∧ p4)) ∨ True) ∧ p4))) ∨ (p3 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191287685991257323580587315680 : (((p5 ∨ p2) ∧ ((p3 ∨ (True → (p1 → p4))) → p3)) ∨ (((p5 ∧ p5) ∨ True) ∨ (((((p1 ∨ (True → p1)) ∧ p1) ∨ p1) → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603834155607621144051809880525 : ((((p4 ∨ (True ∧ (((((((p4 ∨ (p4 ∧ False)) ∨ p5) → (p1 ∧ ((p4 ∧ p5) ∨ p1))) ∧ (p5 ∧ p4)) ∨ p3) ∧ p1) ∨ p4))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660673619746961853528389288997 : (((((((((p4 ∧ ((p1 → False) → p5)) → (p2 → p3)) → p5) ∧ p5) ∨ ((p2 ∧ False) ∨ ((p3 ∨ p1) ∨ p1))) → p2) → (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41404530330638219955991779339 : (((((((p5 ∨ (p2 → (p3 ∨ (p5 ∨ False)))) ∧ (p4 → p3)) ∨ p3) ∨ p4) ∨ (((p4 ∨ (p2 ∨ False)) ∧ False) → (False → False))) ∨ p4) ∨ p4) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350909014311038283158104291721 : (p4 → (((((p3 → p5) ∨ (p2 ∨ (p3 ∨ p4))) → (False ∨ (p1 → ((False ∨ (((True ∧ False) ∧ p4) ∨ True)) → p5)))) ∧ False) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351256744218032470594893554730 : (p4 → ((p3 ∧ ((((True → p1) ∧ p4) → p3) → ((((True ∧ p5) ∧ False) ∨ p2) ∧ (((p2 ∧ p2) → p2) → p5)))) ∨ ((True ∧ p5) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618005079070527054671384034226 : (((((((True ∨ p4) ∨ p4) ∨ p1) ∧ ((p2 → (((p2 → (p5 ∨ True)) ∧ p5) → (True ∧ (p5 ∧ p5)))) → ((False ∧ p3) ∧ p3))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698693399667385914685983799220 : (((((p2 ∧ p4) ∧ ((p1 → False) → ((True ∧ True) ∧ (False ∨ p3)))) ∨ (p3 → (((p1 ∨ (p1 ∨ ((p3 ∨ p1) → True))) → p1) ∨ True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_113503096655854792041141128667 : (((((p3 → ((p2 ∧ ((p1 ∨ p3) ∧ p5)) ∨ True)) ∧ (p5 ∧ (True → p4))) ∧ ((p5 → True) → (p4 → p5))) ∨ (True ∧ False)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45260038591289662543991339794 : (((p1 ∧ (p4 ∨ ((True ∨ (((p3 → ((True ∧ (p2 → ((True ∨ p4) → False))) ∨ False)) ∧ ((p3 ∧ p5) ∨ p4)) → p4)) ∨ False))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198542219790633325259784361902 : ((False ∨ (p5 ∧ (p5 → ((p1 ∧ False) ∧ False)))) ∨ (p4 → ((((p4 → True) ∨ p2) ∧ False) ∨ (((p2 ∧ (False ∨ p3)) ∨ (p1 ∧ True)) ∨ True)))) := by
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
theorem thm_5_vars_56583672724600214680264078515 : (((p1 → (False ∧ (p5 ∧ p5))) → (((p4 → p2) ∨ (p2 ∨ p3)) ∨ (((p2 ∧ p5) ∨ p5) → (((p2 ∨ p3) ∧ (p4 → p2)) → p5)))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181350193455646381158154494248 : ((False ∨ (((p3 → ((p1 ∧ p1) ∨ True)) → (p4 → p1)) ∨ (p2 ∨ p5))) → (((p3 ∧ (p5 ∧ p4)) ∨ ((p3 ∧ (p5 ∨ p3)) ∧ p1)) ∨ True)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590444711988479837454747136432 : ((((((p5 ∧ p1) ∨ ((False ∧ ((p4 ∨ ((p5 ∧ (True ∧ p2)) → (p5 ∧ False))) ∨ p3)) ∨ ((p1 ∨ p4) → (False → p3)))) → False) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184153883630796179470546935108 : (((p2 ∨ ((p4 ∧ (p2 → ((True ∧ True) ∨ p2))) → p2)) ∨ False) ∨ (((True ∨ True) ∧ (p3 → (((p1 ∨ p3) ∨ p1) → p3))) → (False ∨ True))) := by
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
theorem thm_5_vars_112383015178544070782940373437 : ((((((True ∧ False) ∨ ((((True → (p2 → p2)) ∨ True) ∧ False) ∧ (p3 → p5))) → (p1 ∧ (p3 ∧ (p4 ∨ p1)))) ∧ p2) → False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621395640654837230142394294539 : ((((True ∧ (p2 ∨ ((False ∧ (True ∧ (((p1 → (p1 ∨ True)) → (True → p5)) ∨ ((p1 ∨ p5) ∧ (p4 → False))))) ∨ (p1 ∨ p5)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_707149406662594598489795235514 : ((((((p2 → True) ∧ ((p4 ∨ p4) → p4)) → p4) ∨ (False → ((((p1 ∨ p2) → p1) ∨ (p1 → False)) ∧ (((True ∨ p3) ∨ True) ∧ p1)))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144516632895175503500190281706 : (((((p1 ∧ (p4 ∧ (p2 → (((p4 ∨ p3) → p4) → p5)))) → ((p5 → p3) ∧ p5)) ∨ True) ∨ (p3 → p4)) ∧ (p2 → (p3 → (p5 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720174058010637929143693780252 : (((((p1 ∨ (p2 ∧ p4)) ∧ p2) → ((p5 ∧ (((((p5 → p4) → p1) → p4) ∨ (False → False)) ∨ ((True ∧ p2) ∨ (p1 ∨ p1)))) ∨ True)) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358491818584681020684400914326 : (p5 → (p1 → ((p1 ∨ p2) ∧ (((((p1 ∨ (p2 ∨ (p2 ∨ (p3 ∧ False)))) ∧ p1) → False) ∧ ((((p3 ∨ p3) ∨ p2) ∧ p5) → p2)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∨ (p2 ∨ (p2 ∨ (p3 ∧ False)))) ∧ p1) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307151430383238572106636009541 : (p1 ∨ (False ∨ ((p4 ∧ (p2 → True)) → (p4 → ((p4 → ((((False ∧ p1) ∨ (((True → p2) → p2) → p2)) ∧ p2) → p5)) ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191389162649188690046639246831 : (((p5 → p3) ∨ (((p4 ∧ True) ∨ (p5 → True)) → False)) ∨ ((((p2 ∧ ((p1 ∨ p4) ∧ p1)) ∧ (p2 → (False ∨ p2))) ∨ (p4 → True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675009249471647927203114534647 : ((((((p3 → False) → ((p1 → p3) ∨ ((True → ((((p3 ∨ p3) → p4) → p3) → p4)) → p5))) ∧ p4) ∧ ((p5 → (p1 ∨ p5)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654085042056831449810160652573 : (((((p3 → ((p3 ∧ False) ∨ ((((True ∧ (True ∧ p2)) ∨ True) → ((p4 ∨ p4) ∨ p4)) ∨ (False → (True → p5))))) ∧ p5) ∨ (p5 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_805999893491803887580105730160 : (((p4 → (((((((False ∧ (p1 ∨ p2)) ∧ True) → True) ∧ True) → False) ∨ (((p4 ∨ (((p3 ∧ p2) → p4) ∧ p1)) ∨ p3) ∨ False)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178331609310623090062370353596 : ((((p5 ∨ (True ∧ (p1 ∧ True))) ∨ ((p2 → p4) → p2)) ∨ (p2 ∨ p3)) ∨ ((True → (p2 ∨ (True ∧ (True ∨ (p2 → p2))))) ∨ (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_47005476300609507452912968892 : (((((p1 ∧ True) ∨ (((p1 ∧ (False → ((p3 → p2) → ((p5 → (False ∨ p3)) ∨ (p2 ∧ False))))) → p5) → True)) → p5) ∨ (False → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598980775313986715810037138450 : (((((p2 ∨ p3) ∧ ((((p4 → p4) ∧ (p4 ∨ ((True ∨ (p1 ∨ (False ∨ p2))) ∨ (((p5 ∨ True) ∨ True) ∨ p5)))) ∧ True) ∧ p2)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316630181775210780480590971617 : (p3 ∨ (p4 ∨ ((p2 ∨ (((p5 ∧ True) → ((((p4 ∨ False) ∨ True) → p3) ∨ p3)) ∧ p5)) ∨ (True ∨ (p3 ∧ ((p5 → False) → (p2 ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165677322553356683642911079774 : (((((True ∨ (p4 ∨ p4)) → p4) ∨ p5) → ((((p4 → p2) → (p2 ∨ p4)) ∧ True) ∨ p2)) ∨ (((p3 ∨ False) ∧ (p3 → p5)) → (True ∧ p3))) := by
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
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64684515241540164510014673877 : ((p1 ∨ (p4 ∨ (True ∧ ((((p2 ∨ (((p4 ∧ (((p1 → p5) ∧ p4) → p5)) ∧ (p5 → True)) ∨ p4)) ∨ (False ∧ p2)) ∨ p1) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62060580631583093313855181304 : ((p2 ∧ ((p2 → p3) → (((p4 → p3) ∧ p4) ∨ ((p1 ∨ p3) ∨ ((p2 ∧ ((p1 ∧ (((p4 → p5) ∨ p3) ∧ False)) ∧ p1)) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891777538394719328537353654717 : (((((((p3 ∨ ((p5 ∧ p3) ∨ (p5 ∨ ((p2 ∧ p4) → (p2 ∧ p4))))) → p1) ∧ (False → (p5 ∧ p4))) ∧ p2) ∧ (p1 → (False → p3))) → p1) ∧ True) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (p3 ∨ ((p5 ∧ p3) ∨ (p5 ∨ ((p2 ∧ p4) → (p2 ∧ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h14 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658701852870301906146527122286 : ((((p4 ∨ (((p4 ∨ p4) ∧ True) → (p1 ∨ ((((p4 ∧ ((p1 ∧ p3) ∨ True)) → False) ∨ (p4 ∨ (False ∧ p5))) ∧ p4)))) ∨ (p3 ∨ False)) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688893064954604321920548398266 : ((((((p3 ∨ ((p1 ∨ p5) ∨ p1)) → ((p3 → False) ∨ ((p3 ∨ p4) → p3))) ∧ p5) ∨ (True ∨ (p5 ∧ (False ∨ (p3 ∨ (p2 → p1)))))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_157092575727803046886421910582 : (((True → (p2 ∨ (((p3 ∨ p2) ∨ False) ∧ ((p5 ∧ (p1 → (True ∧ (p1 → p1)))) ∧ p2)))) ∨ p3) ∨ (((p1 ∨ p3) ∨ p4) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754800138675968313395552483055 : (((False ∧ (False ∨ (p1 → (((((p4 ∨ p2) → ((p5 ∧ True) ∨ p5)) → (p5 ∧ (True → (True ∨ True)))) ∧ p5) ∧ ((p5 ∧ True) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704787035408514671832822147958 : ((((p5 ∧ (((False → p2) ∧ p3) ∨ ((False ∧ p4) ∨ p5))) → (((False ∧ (True ∨ p2)) ∧ ((p5 → (p3 → (p3 ∧ p4))) ∨ p5)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324368445563755405255026309670 : (p5 ∨ ((((False ∨ p5) ∧ p2) → (p4 ∨ p3)) ∨ (((((p1 → p5) ∧ True) ∨ p5) ∨ ((p1 ∧ (p1 ∧ p5)) ∧ (p4 → (True → p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67583771638078847177212618873 : ((p1 → ((p3 ∨ p2) → (p4 ∧ (((p4 ∧ (p3 ∨ ((p2 ∨ p1) → p5))) ∧ (False ∧ (p5 ∨ (p2 ∧ p2)))) ∧ (False ∨ (p5 → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214063439647222639763430033065 : ((((p4 → True) ∧ p1) → p4) ∨ (((False ∨ True) ∨ p5) ∧ (p4 ∨ ((True ∨ (((p1 → p3) ∧ ((p3 ∨ p1) → p2)) → True)) ∨ (p5 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_172990483625967178764076043436 : ((p5 ∧ ((p5 → ((p2 ∧ False) ∧ (False ∨ (False ∨ (p5 ∧ (True → p5)))))) ∨ False)) ∨ (p1 ∨ (((p4 ∨ (p4 ∧ p1)) → p4) ∨ (p5 ∧ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135205134167713436218421953665 : (((((p1 ∧ ((((True ∧ p4) ∨ ((p2 → True) ∧ False)) ∧ (p5 → p3)) ∧ p5)) ∧ p5) → (p5 ∨ p1)) → (p1 → False)) ∨ ((p2 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38168934487414247712006076657 : (((((((p5 ∧ True) ∧ p3) ∨ (p5 ∨ (p2 → p1))) ∧ ((True ∧ (p2 ∨ (p4 ∧ (p2 → p2)))) ∨ False)) ∨ ((False ∧ False) → p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212595307909631071638405451427 : ((p5 ∨ (False → (True ∧ False))) ∧ ((((p5 ∨ (p5 → ((p2 → (p5 ∨ p5)) ∧ (((p1 ∨ p2) → True) ∧ p4)))) ∧ p1) → (False ∧ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157655976222791793105661398713 : ((((p3 ∧ ((p1 ∧ (False ∨ p2)) ∨ ((p1 → p3) ∧ (p3 → p3)))) ∨ p4) ∨ ((p4 ∧ False) → p2)) ∨ ((p5 → ((p3 → p2) ∨ True)) ∨ False)) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49385394973564886491648207311 : (((((((p4 ∧ p5) ∨ p1) ∨ (p1 ∨ (((True ∧ ((p5 ∨ (p4 ∨ True)) ∧ p5)) → True) ∧ p3))) ∨ False) ∧ True) → (p1 ∧ (False → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210723881629081208059712183832 : ((((p5 ∨ True) → False) → p2) ∧ ((((p3 ∧ True) → p3) ∧ (True ∧ ((p2 → True) ∧ (((p5 ∨ (p2 ∨ p4)) ∧ p2) ∧ (p2 → True))))) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172202690979338675382240868709 : (((((((False ∧ p3) ∧ p5) → p5) ∧ p3) ∨ (True → True)) → ((True ∨ p3) ∧ p5)) ∨ ((p3 → p3) → (p1 ∨ ((p2 ∧ False) → (True → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59961105440190466029454850921 : (((True ∨ p4) → (True ∧ (((((p1 ∧ p5) → True) ∧ p4) ∨ ((True ∨ (p4 ∧ (((False ∧ False) ∧ p3) → p4))) → (p1 → True))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38266634409973681566209635042 : ((((((((p3 ∨ False) ∧ ((p2 ∨ (p4 ∨ p2)) ∧ (p2 ∨ p2))) → (p5 ∧ p2)) → p2) ∧ p3) ∨ (p1 → ((p3 ∨ False) ∨ p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49134303622174290267387805473 : ((((p2 ∨ ((p4 ∧ (p2 ∨ p2)) ∨ ((p5 ∧ p3) ∧ (p1 → p5)))) → ((((False → p4) → p4) ∧ p1) → False)) ∨ ((p3 → p3) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621739393879260880463660489909 : ((((p1 ∧ ((((True ∨ (((True ∧ p2) ∧ ((p4 ∨ (p2 ∧ False)) ∨ (p3 → (p1 ∧ p2)))) → p1)) → (False ∨ p4)) ∨ p4) ∨ p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_177712325479182844728472454535 : ((((((False ∨ p2) ∧ (p3 ∧ p5)) ∧ True) ∨ (p3 → (p5 → False))) ∧ p5) ∨ ((p4 → ((((True ∧ p5) ∧ False) ∧ p2) → (p4 ∧ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42554688912089562262840376325 : (((p1 ∨ (p1 ∧ (((p1 ∨ ((False ∧ p3) → (((False ∨ True) ∧ (p3 ∧ p5)) ∨ True))) ∨ (p4 ∨ True)) → ((p1 → p4) ∨ p4)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797237890633076162548292057813 : (((p1 → ((((((p1 → (p5 ∨ True)) → (((p3 → False) ∨ p1) ∧ False)) → ((p2 ∧ (p4 ∨ True)) ∨ (p3 ∧ False))) ∧ p1) ∨ p4) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (p5 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133921459043745311477737384662 : (((p4 ∨ (p1 ∧ (((p2 → (p2 ∨ p4)) → (False → False)) → ((p3 ∧ False) ∨ (p5 ∧ (p3 ∧ (p5 ∧ True))))))) ∧ True) ∨ ((p3 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228242503413413821313566808693 : ((p5 ∧ (True → p4)) ∨ (p5 → ((p4 → (p4 ∧ (False ∧ p2))) ∨ (((p5 → False) → ((p3 ∨ False) ∧ (True ∧ (p2 → (p1 → p1))))) ∨ False)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943264614733199269874925514204 : (((((p4 → True) → (p2 ∧ False)) ∧ (p1 ∨ ((p4 ∧ p3) → (((p1 ∨ p2) → False) ∧ (((False ∧ ((p5 ∨ p4) ∧ False)) ∧ True) → p2))))) → p1) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p4 → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776699463188535690836404266055 : (((p1 ∨ ((((p4 ∨ p4) ∨ (((p3 ∧ p4) → (((p3 → False) ∨ p5) → (p1 ∨ False))) → (((p5 ∧ p1) → p3) → p4))) ∨ p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



