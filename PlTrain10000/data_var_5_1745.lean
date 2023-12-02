variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198514101304011146152418099390 : ((False ∨ (((p2 ∧ (p3 ∨ p5)) ∧ p2) ∧ p4)) ∨ (p2 → ((((p4 ∨ (p3 ∧ (p1 ∧ p3))) ∧ p1) ∧ (((p1 ∧ p3) → p5) → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708035128857480821784646184303 : ((((p2 ∨ (p4 ∨ ((p1 ∧ p4) ∨ (p1 ∨ p5)))) ∨ ((True → False) ∨ (((False ∨ (True → ((p4 ∧ p3) → (False ∨ p2)))) → p2) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227642019474839991340161162243 : ((False ∧ (p5 ∨ True)) ∨ ((((p5 → p2) → ((False ∧ p4) ∧ p1)) ∧ ((p1 → False) ∧ True)) ∨ ((p3 → ((p5 ∨ (p1 ∨ p4)) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118544199456527879271339437076 : ((p3 ∨ (p2 ∨ (p1 ∧ ((False → (p1 ∨ (((False ∧ (p4 ∨ p3)) ∧ False) ∨ (p3 → (p5 ∧ (True → (p4 ∧ p5))))))) → p4)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114394369324914744342275420618 : (((((p2 ∨ (p5 → (((p2 → p2) → p1) → (p2 → p4)))) ∨ p2) → ((p1 → True) → p4)) ∨ ((True → p2) ∧ (False ∨ p2))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159089534377953939782214625031 : ((True → (((p1 ∨ (False ∧ True)) → (((p3 ∧ ((p5 ∨ p3) ∨ False)) ∧ p5) ∨ False)) ∨ (p5 → p5))) ∨ (p3 ∨ (True ∨ ((p1 ∧ False) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717250699978832534823101752511 : ((((p3 ∨ ((p4 → p4) → True)) ∧ (((False ∨ p1) ∨ (((False → (((p4 ∧ p2) ∨ False) ∧ p5)) → (p4 → p5)) → (False ∨ False))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_691156959464016940470166440101 : (((((False ∨ (((False → (False ∧ p1)) ∧ False) → p5)) → ((False ∧ (True ∧ p4)) ∧ p4)) → (False ∧ (False ∨ ((p2 ∧ p3) ∨ (p1 ∨ p4))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (((False → (False ∧ p1)) ∧ False) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (False ∨ (((False → (False ∧ p1)) ∧ False) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h9
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351525574378336591062556820179 : (p4 → (((False → (((p1 → True) → p1) ∨ (False ∨ (((False ∨ p3) ∧ p1) ∧ (True ∨ p1))))) → False) ∨ (p2 → ((p4 ∨ (p5 ∨ p5)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33626854002984523545407293164 : ((p4 ∨ (p2 → (p2 ∧ ((True → (((p1 ∨ ((((False ∧ p4) ∧ p4) ∨ p5) ∨ p3)) → True) → (p1 → ((p4 ∧ p2) ∨ p5)))) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300734862218395637837973553168 : (False ∨ ((p3 → ((p4 ∨ ((p5 ∨ False) ∨ ((p4 ∧ True) ∧ ((p3 → True) ∧ (True ∨ True))))) → p3)) → (((p3 → p2) ∨ (False → True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113258574251961273098349314446 : ((((True ∨ (((p4 ∧ p1) ∧ (p1 ∧ (False ∨ (p2 → (p1 ∨ p5))))) → ((p5 ∧ p4) ∨ p1))) → (False ∨ p2)) ∧ (p2 ∨ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53675902229465758534987222563 : ((((p3 → True) → ((((False → True) ∧ p3) ∧ p3) → False)) ∧ ((((p3 → p4) ∨ (p5 ∨ (p1 → p1))) ∨ (True → (False ∧ p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234270571371713189982199203946 : ((False → (False → p5)) → ((((p3 ∨ p4) → ((p1 ∧ (p4 ∨ (p1 ∧ (p1 ∨ p4)))) ∨ (p5 ∧ ((p4 ∨ p3) ∨ (p4 → p2))))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722362772739027849270253488314 : (((((p3 ∧ p3) ∧ p1) ∧ ((((False ∧ False) → ((p4 ∧ False) → (True → False))) → (((p1 → (p5 ∧ p2)) ∧ True) → (p2 ∨ p1))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227229839171830422531667751100 : (((False → p1) → p4) ∨ ((((p1 → p3) → False) → (p2 ∨ ((((False ∧ (True → (True ∧ True))) ∧ True) ∧ p5) ∨ True))) ∧ ((True ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314823618501825047632265244317 : (p3 ∨ ((((p4 → (p4 ∨ False)) ∧ ((p1 ∧ (p5 → p5)) → p3)) ∧ p3) ∨ (True → (p4 ∨ (False → (p2 ∨ (p3 ∧ ((p3 ∨ p1) ∨ p5)))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126801736759433961621937381350 : ((p5 ∧ ((((p2 ∨ ((p5 ∧ p4) ∨ p1)) → ((p5 ∨ p5) ∨ (p4 ∨ ((p1 ∧ p1) ∨ ((p5 ∨ p1) → p3))))) ∧ p5) → p1)) → (p3 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129082275745225987898227263636 : (((((p4 → ((p4 → p2) ∧ p4)) → (p5 → ((p2 ∨ (p2 ∨ True)) → ((p3 ∧ False) ∨ (p4 ∨ p1))))) ∨ p4) ∨ True) ∧ (True ∨ (p2 ∧ p4))) := by
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
theorem thm_5_vars_329008742255968456796971542595 : (True → ((p1 → (((False ∧ p2) ∧ False) ∨ p3)) ∨ ((p5 ∧ (((p5 ∧ True) ∨ (((p1 → p1) ∧ ((p4 ∨ p1) → p3)) → p5)) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752133828500502282915317692042 : (((True ∧ (p1 → (p4 ∧ (p4 → (((p1 → p4) ∧ (p2 ∨ (((True ∨ (p3 ∧ p2)) ∨ True) → p4))) → (p5 → ((p1 ∧ p3) ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300104517286912124956775106046 : (False ∨ (((((p5 → (p1 ∨ (p5 ∨ False))) → (p3 ∧ p5)) ∧ (p5 → p5)) ∧ ((p2 ∧ ((p4 ∧ p4) ∧ False)) ∨ (p3 ∨ p4))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43847705896479676546265029231 : (((((p5 ∨ (True → ((True ∨ (p1 ∧ p5)) ∨ (((p1 ∨ False) → p1) ∧ (True ∨ (True ∨ False)))))) ∧ (p3 ∧ p5)) ∧ (p1 → p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158420501627638904938891014338 : (((p4 ∧ True) ∨ ((((p2 ∧ p1) ∧ (p1 ∧ (p2 ∧ p4))) ∧ (p3 ∨ p4)) ∧ ((True ∨ p5) ∧ p3))) ∨ (((p4 ∧ False) ∧ p3) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158918188993388940284809053586 : ((p1 ∨ (p1 ∧ (True → ((p4 ∨ p3) ∧ ((p1 ∨ p4) ∧ ((p3 ∨ p5) → (False ∨ (p5 → p5)))))))) ∨ (((p1 ∧ p3) → (True ∨ p3)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309373190834649071080438388299 : (p2 ∨ (((p5 ∨ p2) ∧ ((True ∧ (p4 ∧ (p1 ∧ True))) ∧ ((p1 ∧ (p5 → (False ∧ p4))) ∧ (False ∨ (p2 ∨ (p5 ∨ False)))))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164558687550843824704375510363 : ((((p4 → (True → ((False ∧ p1) ∧ True))) → (p1 → ((False ∨ (p2 ∨ p1)) ∧ p3))) ∧ p2) ∨ ((p1 ∧ (((p4 ∧ True) ∧ p4) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58233244027065783279750420722 : (((p4 ∧ p5) ∧ ((p5 ∨ (((p1 ∧ p3) ∧ p4) ∧ (p2 → (False → ((False ∧ True) ∨ p5))))) ∧ ((((p3 → p3) ∧ False) ∧ p5) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621918857079133154554661346475 : ((((p1 ∧ (p1 ∧ (p1 ∧ (((p2 → ((p5 ∨ p4) → p4)) ∨ (p4 ∨ (p3 ∨ (p4 ∧ (p5 ∧ (p3 → p5)))))) ∨ (p1 ∨ False))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113546071683301406258497421851 : ((((True ∨ (p3 ∨ p2)) ∧ ((p3 ∨ ((((p5 ∨ (p1 ∨ p4)) → p3) ∧ p5) → p2)) → (p3 ∧ (p3 ∧ p2)))) ∨ (p3 → True)) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54818925443451486768392382889 : (((p5 ∨ ((p5 → p3) → ((p3 → False) ∨ p5))) → (((p1 ∧ False) ∨ p4) ∨ ((p2 ∧ p2) ∨ ((p4 → p3) ∧ ((p2 → p3) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318556229764726743447078835540 : (p4 ∨ (((((p2 → p4) ∧ ((((p5 ∨ p3) ∧ p5) ∨ p3) ∧ ((False → ((False ∨ True) ∨ True)) → p5))) ∨ (p2 ∧ True)) ∨ True) ∨ (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135383476953348839578723790508 : ((((((((p5 → p3) → True) ∧ p2) → (p4 ∨ p1)) ∧ ((p3 ∨ (True ∨ p3)) ∧ p4)) → p2) ∨ ((p2 → p2) ∨ True)) ∨ (p1 → (p1 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38196140026451883799589259154 : (((((((((p5 ∨ ((p1 → False) → (p2 ∨ p3))) ∨ (False ∧ (p4 ∧ p4))) ∨ p5) ∧ p1) → p5) ∨ p4) → (True → (p3 ∨ p3))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41352922695703721501829345720 : ((((p1 → ((p3 ∧ p3) ∧ (((p3 ∧ True) ∨ (False ∨ (p5 ∧ (p1 ∧ p3)))) ∨ p1))) ∨ ((True ∧ (p4 ∨ p1)) ∨ (p5 ∧ p5))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328837874929840023342279810295 : (True → ((p1 → (p4 → (((p5 → True) ∨ (p1 → True)) → p2))) → ((((p4 ∧ p5) → False) ∨ ((p5 → p1) ∨ (p4 → True))) ∨ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323994887317161390069336248606 : (p5 ∨ (((((p4 ∨ True) → True) ∧ p2) → (True ∧ (((p2 ∧ p5) ∧ p5) → p3))) ∨ (p2 → ((p4 ∨ (p1 → (False ∨ (p3 ∧ p2)))) ∨ p2)))) := by
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
theorem thm_5_vars_618922869458166245476595033404 : (((((p5 → (p3 ∧ False)) ∧ (((((p1 ∨ (p5 ∧ (p1 ∧ p1))) ∨ True) ∧ p5) → ((True → (p2 → (True ∧ p1))) ∧ False)) → p5)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184658162042997463511992970050 : ((((p5 ∨ (p5 ∨ (p1 → True))) → p4) ∨ (True ∧ (p5 ∧ p3))) ∨ ((p1 ∨ ((p5 ∧ (((p4 ∧ False) → (p1 ∧ p1)) ∨ False)) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_52784650094021531143338384957 : ((((True → (((True ∨ False) ∨ ((p1 → True) → False)) ∧ p1)) ∨ (p2 ∨ p2)) → (p5 → ((p5 → p5) → ((p4 ∨ p1) ∨ (True ∨ p4))))) ∨ p4) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679748092992302613931881583753 : ((((((((((p5 ∨ p2) → (p2 → p3)) ∧ False) ∧ p3) → p1) ∨ ((p3 ∧ p3) ∨ (False → True))) ∨ p5) → (((False ∨ p1) ∧ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225655381222127619133754856574 : (((p2 → p1) ∧ p4) ∨ ((p4 ∨ ((p2 ∨ (True ∨ p5)) → (((False → (p2 ∨ True)) → p2) ∧ (p5 → (p4 → p4))))) ∨ ((True → False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_156890178900134807437171639417 : ((((((False → ((p4 ∨ (True → True)) ∧ p1)) ∨ p2) → (((p1 ∧ False) ∨ p1) ∨ p5)) ∨ True) ∨ p3) ∨ (False ∨ (((True → True) → False) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230622149049557735437746111614 : (((p2 → p3) ∧ True) → ((((p5 ∨ p5) ∧ p1) ∧ (p4 → ((((p3 → True) ∧ (p2 → p3)) ∨ (p1 → (True ∨ p3))) → p1))) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68539802156153629452715164800 : ((p3 → (p2 → (p1 → (((((((p4 ∨ (p2 ∨ p5)) → p3) ∧ p2) → p3) ∨ (p4 ∨ ((p1 ∧ p5) ∨ False))) → (p4 ∨ p5)) ∨ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700480634180936793544835096993 : ((((p2 ∨ ((True ∨ (p5 ∨ p2)) → (p3 → (p5 ∧ (p1 → p4))))) → (((p1 ∨ (p1 ∧ p5)) ∨ p5) ∧ (((True ∧ p5) ∨ p4) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41931553322511185100603827043 : ((((p5 ∨ (p1 ∨ p3)) → ((p3 ∨ ((((p1 ∨ p4) ∨ p3) → (p4 ∨ (p5 ∧ ((True → (False → p3)) → p1)))) ∧ p3)) ∨ p3)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60091755552510375693875445801 : (((p3 ∨ True) → (p2 → (False ∨ ((((((p4 → p3) → p2) ∧ ((p3 → ((p5 → p3) → (p5 → p5))) ∧ p1)) ∨ p1) → p5) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303992313961490208228791942787 : (p1 ∨ (((p5 ∧ True) ∨ ((((p4 → ((p2 ∧ (False ∧ p2)) ∨ p2)) ∨ ((p4 → ((False ∨ p2) → p3)) → p1)) → p3) ∨ (p1 ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158185441610607971205889060904 : (((p1 ∨ ((p3 → p3) ∨ p1)) → (((False ∨ p1) ∧ (p2 ∨ p3)) ∨ (p5 → (p1 → (p1 ∧ True))))) ∨ ((p5 ∨ (p4 ∧ (False ∨ p2))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54251380442569168152697560189 : ((((((p5 → True) ∨ p5) → True) ∨ (True ∨ p4)) ∧ (p1 ∨ (p2 ∨ (((p5 ∧ p5) ∨ (p5 ∨ (((False ∨ False) → p5) ∨ p3))) ∨ p5)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354645622232599172998062572690 : (p5 → ((((((((False ∧ p1) → (p4 → False)) ∧ p2) ∧ False) ∨ (True ∨ ((True ∧ False) ∨ ((p2 ∧ p5) ∨ (p2 → True))))) → p2) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311196304726161865157697469311 : (p2 ∨ ((p3 ∨ p2) → ((((((((p5 ∧ p5) → (p3 ∧ True)) → False) ∧ p4) ∨ p2) ∧ (p4 ∧ (p3 → True))) ∧ True) ∨ (p5 → (p3 ∨ True))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153401272139576702235097295498 : ((p3 ∨ ((((False → (False ∧ p3)) ∨ True) → p3) ∧ (p1 → ((True → p2) ∧ (((True → p3) ∨ p1) → p5))))) → (p3 ∨ ((p5 ∨ False) ∧ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((False → (False ∧ p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111553474725093368718917855462 : ((((((p4 → (p2 → ((p2 → False) → False))) ∧ ((p1 → (p3 ∨ False)) ∨ (p2 → p3))) → ((p2 ∨ p3) ∧ p5)) ∧ p4) ∨ True) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56898851248017996119915716228 : (((p4 ∧ (False ∧ p2)) ∧ ((p5 → (p1 ∨ (p1 ∧ ((p5 ∧ p2) → False)))) → (((True ∨ p5) ∧ (p3 ∧ ((p2 → p4) ∨ p4))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111644368995336182396209196040 : (((((((p3 ∨ p3) ∨ False) ∨ p1) → (p4 ∨ (p1 → (((p3 ∨ p4) ∧ ((True → p5) ∧ (p4 ∨ p5))) ∨ True)))) ∨ p1) ∨ p3) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601371496550779023702760596385 : ((((p2 ∧ (p3 ∧ (p2 ∧ (((False ∨ True) ∧ ((p4 → (p3 ∧ True)) ∧ ((False → ((p4 ∨ p3) → (p3 ∨ True))) ∧ p2))) ∨ p4)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68372445415597249868669877751 : ((p3 → (((p5 ∧ p4) → ((True ∧ p1) ∧ p4)) → (((((p1 ∧ p5) ∧ p3) → (False ∨ False)) ∧ p3) ∨ (p5 ∨ (False → (p2 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50901874285515127844979476656 : (((((True → (p5 ∧ (((False → p5) → p4) ∧ p5))) → (p5 ∨ (p2 ∧ p4))) ∧ (p5 ∧ p3)) ∧ ((p5 ∨ p5) → ((p3 ∨ False) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187058412852676615011770934373 : (((False ∨ True) ∧ (((True ∨ p1) → (p2 → (p4 ∨ False))) → p1)) → (((False ∨ ((False → p3) ∨ ((p5 → (False ∧ False)) ∨ p1))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117241133165576976303674467525 : ((True ∧ (False ∨ ((((p3 ∧ (p2 → (p1 ∨ (p3 ∧ p1)))) ∨ (((p4 → (p3 ∨ p2)) ∧ p5) → p5)) → (False ∨ p5)) ∨ p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349352405479828958605851891358 : (p3 → (p3 → (((p3 ∧ (True ∨ (p2 → (True → ((p3 → p1) → ((True ∨ (p2 ∧ p2)) ∨ p4)))))) → False) ∨ (((p2 ∨ False) ∧ True) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230649092670958754707116570733 : (((p3 → False) ∧ p4) → (p2 ∨ ((p3 → p2) → ((p2 ∧ True) → (((((p4 ∧ (p5 → p1)) ∨ p1) → p4) → False) → ((p4 → p3) ∧ False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : (((p4 ∧ (p5 → p1)) ∨ p1) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h16 := h6 h10
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h5.left
  let h18 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h19 : (((p4 ∧ (p5 → p1)) ∨ p1) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h25 := h6 h19
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45310143358302130041277448548 : (((p3 ∧ (((p5 → p2) ∧ (((p3 → (p1 → p5)) ∧ (((p1 → True) ∨ p1) → (p2 → False))) → (True ∧ (p4 ∨ True)))) ∨ p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40885166716418406685733489513 : ((((((p3 ∨ (p2 → p5)) ∨ (p5 ∨ ((p2 ∧ True) ∧ p1))) ∧ ((p2 ∨ p3) → ((True ∧ (p1 ∧ p5)) ∧ p4))) ∧ (p5 → p1)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54142645231961156509188516151 : (((True → (((p2 ∨ (p1 ∨ False)) ∨ p3) ∧ (False ∧ p1))) → ((p4 → (False ∨ ((p3 ∨ (((p5 → p5) → False) → p1)) → False))) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120918559498653404691030506059 : (((((p3 → (p2 ∨ True)) → p2) ∧ ((False ∨ ((((True ∧ p1) → p3) ∨ p5) ∧ (((True ∨ p3) → True) ∧ True))) ∧ p5)) ∨ p2) → (p1 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : (p3 → (p2 ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h16 := h3 h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h10.left
        let h19 := h10.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h20 : (p3 → (p2 ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h22 := h3 h20
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320263088024480511898813139778 : (p4 ∨ ((True ∧ p3) ∨ (((p2 → False) ∨ (((p5 ∨ (((p4 ∧ (p1 → True)) → False) ∧ (p2 ∧ (p4 ∧ p5)))) ∨ (p4 ∨ True)) ∧ True)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52104218081121226128543553321 : ((((p5 ∨ (((False ∨ (True ∨ (p1 ∧ p4))) ∧ ((False → False) ∧ True)) → p3)) ∨ False) → ((p5 ∨ ((p1 ∨ p4) ∨ (p5 ∨ p5))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338237470362137557629219278640 : (p1 → ((((True ∧ p3) ∧ p3) → (True ∧ p4)) ∨ (((((p1 ∧ p4) → p3) ∨ False) ∨ False) ∨ (((False ∨ (p2 ∨ (True ∨ p5))) ∧ p1) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337898211949227964333228528971 : (p1 → (((p1 ∧ p2) → ((p5 ∨ (p2 ∧ (p3 ∨ (True → (p3 → p4))))) → p1)) → ((p4 ∨ ((p4 ∨ True) ∨ ((p5 → p4) ∧ p5))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738171985691995147596780400826 : ((((False ∧ p2) ∨ ((True ∧ p4) → ((((p2 ∧ p4) ∧ p5) ∧ True) ∨ (((False ∧ (True → ((p5 → p2) → (p4 ∧ p4)))) ∧ p2) ∨ p4)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197284040353242996475751439793 : ((((p4 ∨ (p2 ∨ p5)) ∨ (p3 → False)) → False) ∨ ((p1 → (p1 ∨ ((p5 → p3) ∧ (p5 → (True ∨ p2))))) ∨ (((p5 ∨ p1) ∧ p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42347844895477630220761815614 : (((p3 ∧ (((((p2 ∨ p1) ∧ (p2 → (p3 → p5))) ∨ p2) ∨ False) ∨ (False ∧ ((p3 → (False ∨ ((p2 ∨ p3) → p2))) ∧ p2)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50231607688093685820660219029 : (((((((((p5 ∨ (p5 → p1)) ∨ (False ∨ p4)) ∧ (p5 ∨ (p2 ∨ False))) ∧ p4) → True) ∧ True) → p1) ∨ ((p2 ∧ (p4 → p3)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341110884962039231257534260616 : (p2 → ((p5 → (((p3 ∧ p1) ∨ (p5 → (((False → p4) ∨ p5) ∧ p3))) → (((p5 → (((p5 ∨ p5) ∧ p3) ∨ p3)) ∧ p3) → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158519594186728107783702688737 : (((p3 ∨ p2) → (False ∧ ((((p5 ∨ (p3 ∧ p2)) → (((p1 ∨ p4) → True) ∨ p4)) → p2) ∧ True))) ∨ (((False → True) ∧ (p1 ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37628918388195576041306527415 : ((((((((p4 ∧ p1) → (p4 → p2)) ∨ ((p5 ∧ True) ∧ ((p2 ∨ ((p1 → p4) ∨ p4)) ∧ (p3 ∧ p5)))) → p3) ∨ False) → p5) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773555321362960369872832735892 : (((False ∨ ((((p1 ∧ (p2 ∨ (p1 → True))) ∧ p1) ∨ ((p5 ∧ (((((p4 ∧ p1) ∧ p1) → True) → p4) ∨ p2)) → (p1 ∧ False))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261139708853590700479559024524 : ((p4 → p4) → (((p3 ∧ (p4 ∨ p1)) ∧ ((((((p2 ∧ ((p1 → p2) ∧ p3)) → False) → p5) ∧ p1) ∧ p5) ∧ ((p1 ∨ False) → p1))) → p5)) := by
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249506635946120628066495362974 : ((p5 ∨ p1) ∨ ((p4 ∨ p4) ∨ (p2 ∨ ((False → (p5 → ((p2 → p4) ∨ (True ∧ (True ∧ p4))))) ∧ (False → ((True → False) → (p1 ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184326413932581055359570706108 : ((((True ∨ p3) → (p5 ∨ ((p2 ∨ p5) → (True ∧ p1)))) → p3) ∨ (p1 ∨ (p1 → (((p4 ∧ p4) ∧ (((p2 ∨ p1) → p2) ∨ p2)) ∨ True)))) := by
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
theorem thm_5_vars_605282552198353243930440921553 : ((((p2 → (p4 → (((((False ∧ False) → (p4 → ((p3 → p4) → p2))) → True) → ((p3 → (True ∨ p2)) ∨ p2)) → (p3 ∧ p1)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309543341613049579952644841508 : (p2 ∨ (((p3 ∨ (((p5 ∨ p3) → p3) ∧ (p3 ∨ ((False → p1) → (p5 ∨ ((p5 ∧ (p1 ∧ True)) ∨ p3)))))) ∨ True) ∧ (p2 → (p3 ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38683402321217302229989792125 : ((((False ∨ ((p5 ∨ (False → p3)) ∨ True)) ∧ ((((((p1 ∧ p2) ∧ (p2 → p1)) ∨ p1) → (p4 ∨ p1)) ∧ p2) ∨ (p1 ∧ p5))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137488549447237298307023207307 : ((p5 ∧ ((p1 ∧ (p1 ∧ ((p3 ∨ p1) ∧ ((((p5 ∨ True) ∨ (True → False)) ∨ ((False ∧ p1) ∧ False)) ∧ p4)))) ∨ False)) ∨ (p1 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148831635400430247405460470909 : (((((p1 ∨ True) → p1) ∧ p4) ∧ (((p4 ∧ (False → True)) ∨ (p5 ∧ p4)) ∧ (((p1 → False) → p1) ∧ p2))) ∨ ((True ∨ p5) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347789906696433037639300273832 : (p3 → ((p4 ∧ (p2 → True)) ∨ ((((p1 → p1) → (p4 → (True → p5))) → (p2 ∨ p2)) ∨ ((p5 ∧ (((p1 → False) ∨ p4) → p2)) ∨ True)))) := by
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
theorem thm_5_vars_58878270465495594451132656673 : (((False ∧ p1) ∨ (((p2 → p1) ∧ ((((p5 → (False ∧ (p5 ∧ p2))) ∧ (p3 ∨ (p3 ∧ p2))) ∨ (p5 ∧ (p4 ∨ p2))) ∧ True)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190239518334456166815262497347 : ((((((p3 ∧ (False ∨ p5)) ∨ p3) → False) ∧ p1) ∨ p5) ∨ (True → (((True ∧ (True ∧ p1)) ∧ (p3 → p2)) ∨ (((True → False) ∨ False) → p5)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77378500283516363824999852997 : ((((p5 ∧ p4) ∨ ((p5 ∨ (((True ∧ p5) → (((True → p1) → p5) ∨ (p4 ∨ p5))) → (p1 ∨ p2))) → ((p4 → p5) ∨ True))) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ p4) ∨ ((p5 ∨ (((True ∧ p5) → (((True → p1) → p5) ∨ (p4 ∨ p5))) → (p1 ∨ p2))) → ((p4 → p5) ∨ True))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46019036348862955054131704347 : ((((((True → p4) ∨ True) ∧ (((p4 ∧ p4) → (((False ∨ False) ∨ p3) → ((p4 ∨ False) → (p5 ∧ p1)))) ∧ p4)) ∧ p1) ∧ (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260935735140698533517171001487 : ((p4 → False) → (p4 ∨ ((((p4 ∧ ((True ∨ p2) ∧ ((p1 ∧ p5) → (p4 → p5)))) ∧ (p4 ∧ (p4 ∨ ((p5 → p5) ∨ True)))) → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h17 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h18 := h1 h17
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h20 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h20
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h4.left
    let h24 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h30 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h31 := h1 h30
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h33 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h34 := h1 h33
        -- False on the left can always be used.
        apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185547488037732097337694362323 : ((p4 ∨ (((p3 ∧ p5) ∨ (((True ∨ p1) → p3) → p2)) ∧ p5)) ∨ (p4 → (((p2 ∧ False) ∧ ((p3 ∨ False) ∧ ((p2 ∧ True) → p2))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344460820175973149752206025387 : (p2 → (p5 ∨ (p5 → ((((p4 ∧ (((p1 ∧ p2) ∨ (False ∧ p2)) ∧ (((p5 → p2) ∧ True) ∨ p1))) ∨ p5) ∧ (p1 ∨ True)) ∨ (p4 ∨ p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233795849885254125829339429520 : ((p3 ∨ (False → p2)) → (((p1 ∨ (p1 → (p4 ∧ (p1 ∧ (p1 ∨ ((p3 ∨ True) ∧ p1)))))) → ((True → (p5 ∨ p2)) → (p3 ∨ p4))) ∨ True)) := by
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
theorem thm_5_vars_207016151001993321455598201116 : ((((True → False) ∨ (True → p4)) ∧ True) → ((p2 ∨ (False ∨ (False ∧ (((p3 ∧ p2) ∨ p5) → p3)))) ∨ ((p4 ∨ (p2 → (p4 ∨ p2))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179089403386972782247282483147 : ((False ∧ ((False ∧ (p4 ∨ (((p2 ∨ p1) → p2) ∧ (True → p3)))) ∧ p3)) ∨ (((((p5 → p3) ∧ True) ∧ p1) ∨ p4) ∨ (True ∨ (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153309960299461231524388416282 : ((p1 ∨ (((p4 → (True ∧ p5)) → True) ∨ ((p3 → (((p5 → p1) ∨ p3) ∧ (True ∧ (p2 ∧ p5)))) ∨ p5))) → (p5 → (p4 → (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h4



