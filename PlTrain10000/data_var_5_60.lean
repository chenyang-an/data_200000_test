variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51252573282615525490185151447 : ((((p4 ∨ p4) ∧ ((p5 ∨ (p1 → (((p1 ∧ False) → True) ∨ ((p5 ∨ p4) → p4)))) → True)) ∨ (p3 → ((p2 ∧ False) ∨ (p4 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42832360698710383018059460306 : (((p1 → (p5 ∧ ((((False ∧ (p3 ∧ (p4 ∨ (p3 ∨ p3)))) → False) → p4) ∧ ((p1 ∧ p4) ∧ (((p4 ∨ True) → p3) ∧ True))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58560049246057381516503306766 : (((True → False) ∧ ((((p4 ∧ p3) ∨ False) ∧ True) ∧ ((p3 ∨ ((p5 ∨ (p4 ∧ (p2 ∧ p1))) → p1)) ∨ (p3 ∨ ((True ∨ p4) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698681671982436664965545902247 : (((((p1 → (p5 ∨ False)) → ((p4 → p5) → (p5 → (p2 ∧ p3)))) ∨ (p1 ∧ ((p2 ∨ (((True ∨ p3) → False) → p5)) ∧ (p5 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152876338160963594650183891385 : ((True ∧ ((p3 → ((((p1 ∨ p3) ∧ ((p1 → p1) → (True ∧ True))) ∧ (p3 ∧ p2)) → (p2 → p3))) → p3)) → (p1 ∨ (p3 ∨ (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → ((((p1 ∨ p3) ∧ ((p1 → p1) → (True ∧ True))) ∧ (p3 ∧ p2)) → (p2 → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h9.left
      let h14 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h9.left
      let h17 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h18 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52012641900734768404460825997 : (((p4 ∧ ((p1 ∨ (p3 → ((False → (True → p5)) → p4))) → (p2 → (p2 ∧ p3)))) ∨ ((p5 ∧ (p3 → (p4 → p2))) → (p5 ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114186964696605652587557307856 : ((((((p5 ∧ (p2 ∨ False)) ∧ False) ∨ ((p4 → p1) ∨ (p3 ∨ False))) ∧ (((p5 → p1) ∧ p2) ∨ p1)) → ((p3 ∧ p2) ∧ p5)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304105081535710192195933935964 : (p1 ∨ ((p1 → ((p2 ∧ p5) → (((((((True → (True → p5)) ∨ (p5 ∧ p3)) ∧ (p2 ∨ p2)) ∧ p5) → (p3 → p4)) → False) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197442593425410319662718827697 : (((((p2 ∧ True) ∧ p1) ∨ p5) ∧ (p4 ∧ False)) ∨ (p5 ∨ ((True → ((True ∨ ((((p5 ∨ False) → p3) → p5) ∧ False)) → (False → p2))) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44326993662008794074468632621 : ((((p3 ∨ (p2 ∨ (True ∧ (p4 ∧ (False ∨ ((((p1 ∨ True) ∧ True) ∧ p3) ∧ p3)))))) ∨ ((((p4 → p4) ∨ False) → p3) ∨ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357259476823234026526384017708 : (p5 → ((p1 ∧ p4) ∨ (((p5 ∧ (True ∧ ((False ∨ (((True ∨ p3) ∨ p3) → ((p1 ∨ False) ∨ (p4 ∨ p1)))) ∨ (False ∨ p3)))) ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190775467402055532391346344835 : (((((True → (p1 → p4)) → p1) ∨ p1) ∨ (True → p1)) ∨ ((False → (p5 ∨ (p3 ∨ (p2 ∨ (False ∨ (p2 ∧ (p4 ∧ (p1 → p4)))))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785916787587640259746780884635 : (((p4 ∨ ((p1 ∧ (((True ∧ ((p2 → ((p5 → p3) → ((False ∨ True) → True))) → p3)) → (p4 ∧ p1)) ∧ (p2 → p2))) ∧ (p4 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178034707460116702632193120885 : ((((((((p5 → p3) ∧ (p1 ∧ p2)) → True) → p5) ∧ p3) ∧ p4) → p1) ∨ ((p3 → (((p2 ∨ p3) ∨ p2) ∨ p4)) ∨ ((p3 ∧ p1) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113040670761595715094602829666 : (((False ∨ (p1 ∧ ((p1 ∧ p5) → (p4 ∨ (p3 ∧ (p2 → ((False → (p3 → ((False ∨ (False ∧ p5)) ∧ p5))) → True))))))) → p4) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38431143281724159426108342092 : ((((((p3 → ((True → (p1 → p1)) ∧ (False ∧ (p5 → True)))) ∨ p4) → p2) ∨ ((True ∧ p4) ∨ ((p2 ∨ p4) → (p3 → False)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191020732341543406890054782112 : (((p4 → ((p4 ∨ p2) ∧ False)) ∨ (p1 ∧ (p1 ∨ False))) ∨ (((p3 → ((p2 ∨ False) ∨ (p5 ∧ (p5 → (p3 → p2))))) ∧ p4) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55230738813138086597824207230 : (((((p3 ∨ p1) → p4) → (p4 → p3)) ∨ ((((True ∨ ((True ∧ (p5 ∧ (p3 ∧ p5))) ∧ (p2 ∨ (p3 ∨ p4)))) ∨ p2) → p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355547930072403863483357946431 : (p5 → (((p5 → (((p1 → p1) → (((p3 ∨ True) → ((p5 ∨ p4) ∨ True)) ∧ (p5 ∨ (p4 → p5)))) → (p1 ∧ p4))) ∨ p2) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743233876340689616273908891367 : ((((p4 → p5) ∨ (((p4 → ((True → p2) → (p3 ∧ (False ∧ p2)))) → (p5 → (False ∧ (p5 ∧ ((p2 ∧ p4) ∧ True))))) ∧ (p2 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197000756187988665706030207543 : (((((True ∨ p3) ∧ p2) ∧ (p5 ∧ p1)) ∨ p2) ∨ (p1 ∨ (True ∨ (p4 → (False ∧ (p2 → (p4 ∨ ((p1 ∨ p5) ∨ ((p5 ∧ p2) → p5))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165555472348648927130971668766 : (((p2 ∧ (p2 ∨ (((p5 → p3) ∨ False) ∧ p2))) ∧ (p2 ∨ (True → ((p4 ∨ p4) ∨ p4)))) ∨ ((p5 ∧ (((False ∧ p3) → False) ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110774112138455557346329273115 : ((((((((p3 ∨ True) ∨ True) → (True → (((p3 ∧ p5) ∨ (p2 ∨ True)) ∧ (p2 → (p1 → p3))))) ∨ p2) ∧ True) ∨ p1) ∧ False) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621830641826042322119218312701 : ((((p1 ∧ ((p2 → ((p5 ∧ (p2 → ((p3 ∧ p4) → (True → ((True ∧ True) → p1))))) ∨ p2)) → ((True → (False ∧ False)) ∧ True))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116970876519000428133360853996 : (((p4 ∧ p1) → (((False → p3) ∧ (((p1 ∧ p4) ∨ (p3 ∨ True)) ∧ p1)) ∧ ((False → ((True ∧ p2) ∧ p3)) → (p5 ∧ True)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310020886367600598537599325774 : (p2 ∨ (((True → ((p3 ∧ (p1 → False)) ∧ (p3 ∨ ((p3 ∧ p5) → (False ∨ p1))))) ∨ p1) ∨ ((((p3 → p5) ∧ (p4 ∨ p3)) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_42823477799846632015933355844 : (((p1 → ((False ∧ ((p4 ∧ p1) → p3)) ∨ ((((False ∧ (p5 ∨ p5)) ∧ (p4 ∨ ((True → (p1 ∧ p2)) ∧ p2))) ∧ False) ∧ p3))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_560142242539713692433744547 : (((p3 ∨ (((p4 ∧ ((((p5 → (((False ∧ (True → p2)) → True) → False)) ∧ p2) → False) ∨ p4)) ∧ (p3 → True)) ∧ True)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51477665642714760637696023250 : ((((((p2 → (p5 → p3)) ∧ False) → False) ∧ (((True ∧ False) ∨ (p1 ∨ p4)) ∧ (p4 ∨ p5))) → (p2 ∨ (p5 → (p2 → (False ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177646836387032224214064042425 : ((((((p5 ∧ False) ∧ (((True ∨ p2) ∧ p5) ∧ p2)) ∧ p3) ∨ p3) ∧ p2) ∨ ((True ∨ (p3 ∧ p1)) ∨ (p1 → (((p1 ∧ p3) → p2) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51944874613220480704184442892 : ((((((p4 ∧ True) → (p3 ∧ p4)) → p4) ∧ (((False ∨ False) ∨ (p5 ∧ True)) ∧ False)) ∨ (True ∨ (True ∧ ((False ∨ (p1 ∧ False)) → p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69041440620791480277712128683 : ((p5 → (((((((p1 ∧ False) ∧ p4) ∨ p4) ∨ p4) ∧ (p1 → p1)) → ((p1 ∨ (((p3 ∧ p1) ∧ p5) ∧ p4)) ∧ (p4 ∨ p1))) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601806044117679306338182488599 : ((((p4 ∧ (((p5 → (p3 ∨ ((p3 ∧ (p4 → (p5 → p4))) ∨ (((p4 ∧ p1) → p3) → p2)))) ∧ False) ∧ ((p2 ∨ p3) ∨ p3))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45842076318952458823820037762 : (((p2 → ((False ∧ p2) ∨ ((((p5 → p1) ∧ p4) ∨ (True → (p2 ∧ p4))) → (((False ∨ (p4 → True)) → False) ∨ (False ∨ p3))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319902613105321337887556783645 : (p4 ∨ (((p4 → (p2 → False)) ∧ p3) → (True → (((p3 → (p3 ∧ p2)) ∨ (((p2 ∧ True) ∧ p1) ∨ ((p4 ∨ (False → p5)) ∧ p3))) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180810680124926250074557088248 : ((((p1 ∧ p3) → p3) ∧ ((True ∨ True) → (p4 ∨ (p2 ∧ (p1 ∨ p2))))) → (True ∧ ((p4 → p5) → (p1 ∨ (p2 ∨ ((p2 ∧ True) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319492087662034697279992164170 : (p4 ∨ (((True ∨ p4) ∧ ((False ∨ (p3 → (False ∧ p5))) ∧ (p2 → p2))) → ((False ∨ ((p4 → True) ∨ p2)) ∧ ((p2 ∨ (False → p1)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h17.left
    let h26 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158326344389134494763435449435 : (((p5 → (p2 → False)) → (p5 → (((True → p1) ∨ (False → (p4 → (p2 ∨ p4)))) → (p1 ∧ p4)))) ∨ ((p2 → p1) → ((p1 ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158991432175850162296043810258 : ((p3 ∨ ((p5 → p4) → (((False ∨ False) → p1) ∧ (True → (((False ∧ p5) ∨ True) → (p4 ∨ p1)))))) ∨ (((True ∧ True) ∧ (p4 → p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112940397740986705418822573228 : ((((p2 → p1) → ((((True ∧ (p4 ∧ (((False ∧ (True ∧ p4)) ∨ False) ∧ True))) ∧ p5) ∧ p2) → ((p5 ∨ p2) → p5))) → False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184747385914254865074981475077 : ((((p1 → (p3 ∧ p4)) → False) ∧ ((True ∨ True) ∨ (p5 → False))) ∨ ((p5 ∧ ((p5 → ((p5 ∨ (False ∧ p2)) ∨ p3)) ∧ p3)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607677521565855937126330774647 : (((((p5 ∧ (p1 ∧ (((p5 ∨ (p1 ∧ p1)) ∧ (p3 ∧ False)) ∧ (True ∧ (True ∨ ((p5 ∧ ((p1 → p4) ∧ p1)) → p3)))))) ∧ p4) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_702236004071161890365732038713 : ((((((((p3 ∨ p4) ∧ False) → p5) → (True → p2)) ∧ False) ∨ (True ∨ ((False ∨ (False → ((p4 ∨ (p5 ∧ p3)) ∧ (p5 ∧ True)))) ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_342922983449214480239772976618 : (p2 → (((p2 ∨ (p3 ∧ p3)) ∧ True) ∧ ((True ∧ p3) → ((p1 ∨ ((((p4 → p4) ∨ p1) → p4) ∨ False)) → ((p1 ∨ p1) ∨ (p4 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h2.left
      let h10 := h2.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h11 : ((p4 → p4) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h13 := h8 h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310849984859116197296456831738 : (p2 ∨ (((p3 → False) ∨ True) → (((((((p1 → False) ∨ (False ∧ ((p2 ∨ p2) → False))) → False) → p3) ∨ (p4 ∨ (p5 ∨ False))) ∨ True) ∨ p1))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306020925808457230997907020600 : (p1 ∨ ((p5 ∨ (False ∨ (p5 ∨ p4))) ∨ ((((False ∧ p5) ∨ p5) ∧ (p3 ∨ (p3 ∨ (((p5 ∧ p4) ∧ (True → p4)) → p1)))) → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173486367980196523952550165884 : (((((p2 ∨ ((p2 ∧ (True ∨ False)) ∧ p3)) → ((p2 ∧ p2) → True)) → True) ∧ p1) → ((((False ∨ (p1 → p4)) → (p4 → p5)) → p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586767697110246425992369885433 : (((((p2 ∧ ((p1 → p4) ∧ (p1 ∨ ((p4 ∨ (p5 ∨ (((False ∧ p3) ∧ True) ∧ (p5 → ((p3 ∨ p5) ∧ p3))))) → p3)))) ∧ True) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47735531972149764847609903097 : ((((((p3 ∨ (((p5 ∨ p3) → p3) ∧ (False ∨ p2))) ∧ ((p3 ∧ True) ∨ p3)) ∧ (p1 → ((False ∨ p5) ∨ False))) ∨ p3) → (p5 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621363836708922120846193935564 : ((((True ∧ (False ∧ ((p5 ∧ p4) ∨ (((p1 → p1) → (p5 → ((p4 → p1) → False))) ∧ (p1 → (((False ∨ p3) → True) → p4)))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_206177671431370843826316826439 : ((p5 ∧ (False ∧ (p2 → (p5 ∨ p1)))) ∨ (p2 ∨ (((((p5 ∨ ((p1 → False) → p1)) ∨ p1) → (p5 → (p1 ∨ p1))) ∧ (False ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319783562406757107677457423863 : (p4 ∨ (((True ∧ (p3 ∨ p4)) → (p2 ∧ p1)) → ((p5 ∨ (p4 → p3)) ∨ (True ∨ ((((p2 ∨ (p4 → p2)) → p2) → p3) ∧ (p5 ∧ p3)))))) := by
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
theorem thm_5_vars_319458955960612826695364128430 : (p4 ∨ (((((False ∧ False) ∨ p4) ∨ p1) ∧ ((p3 → True) ∨ (p1 ∧ True))) ∨ (((False ∨ (p3 ∧ False)) ∧ p2) ∨ ((p1 → p4) → (True ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134758707197391869853340657361 : ((((p4 ∧ p3) → (((p4 ∨ True) ∨ (True ∨ ((True ∨ False) ∧ (False → ((p1 ∧ p3) → p4))))) ∨ (p4 ∨ False))) → False) ∨ (False → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207594389403555143015624329650 : (((((p4 ∨ p2) ∧ p5) → True) → p2) → (True ∧ ((p4 → p1) ∨ ((p5 ∧ (p4 ∨ (p3 ∧ p1))) → ((((p5 ∧ p3) → p2) → p4) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123169455023860868077827990443 : (((p1 ∨ ((p1 → (True → p4)) → (False ∧ ((p1 ∨ p1) ∧ ((((False → p2) ∨ p3) ∧ p5) ∨ False))))) → (True ∨ (p4 ∨ False))) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197714377538086595714191997143 : ((((True ∨ True) ∧ p4) ∧ (p3 ∧ (p3 ∧ False))) ∨ (False ∨ ((((False ∨ (p4 → ((p1 ∨ p4) ∨ p2))) → False) ∧ p2) → (p3 ∧ (False → p5))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ (p4 → ((p1 ∨ p4) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60529440091113708663878581407 : ((True ∧ (((p1 ∧ ((((p5 ∧ p5) → p4) ∨ (p3 ∧ (p5 ∧ (p5 ∨ (p3 ∨ (p5 ∨ (p2 ∨ (p3 ∨ False)))))))) ∨ p4)) → False) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121364521325553996922366013526 : ((((((p3 ∧ ((p2 ∨ (True ∧ p4)) ∧ True)) ∧ (((True ∧ (p5 ∨ p5)) ∧ p1) ∨ (False ∧ (p1 → p2)))) ∨ p1) ∨ True) → False) → (p4 ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∧ ((p2 ∨ (True ∧ p4)) ∧ True)) ∧ (((True ∧ (p5 ∨ p5)) ∧ p1) ∨ (False ∧ (p1 → p2)))) ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 ∧ ((p2 ∨ (True ∧ p4)) ∧ True)) ∧ (((True ∧ (p5 ∨ p5)) ∧ p1) ∨ (False ∧ (p1 → p2)))) ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185510349252757551027697988858 : ((p2 ∨ (p1 ∨ ((p1 → (p2 → False)) ∧ ((p5 → p2) ∨ p5)))) ∨ (p5 ∨ (p1 → (p4 ∨ (((((p2 ∨ p3) ∧ False) ∨ p3) ∧ p3) → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183360307792394553097150495971 : ((True ∨ ((False ∨ ((False ∨ (p1 → True)) ∧ True)) → (True ∨ False))) ∧ (((p3 → ((True ∧ (p5 ∧ p2)) ∧ True)) ∨ p3) → (p2 → (p5 → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228566639697389098373780411346 : ((p1 ∨ (p1 ∨ p2)) ∨ ((((p1 ∧ ((p2 → p2) → p3)) ∨ True) ∨ (True ∧ p3)) ∨ (p5 → (False ∨ (True ∨ ((p1 ∧ (p3 ∧ False)) ∧ p5)))))) := by
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
theorem thm_5_vars_644750069443009958402658544035 : ((((p2 ∨ ((((((p5 ∨ ((p4 → (p4 ∧ False)) ∧ ((p3 → p3) → (p2 ∧ p4)))) ∧ p1) ∨ (True ∨ p4)) ∨ p5) → p2) ∧ True)) → p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((((p5 ∨ ((p4 → (p4 ∧ False)) ∧ ((p3 → p3) → (p2 ∧ p4)))) ∧ p1) ∨ (True ∨ p4)) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67610445316290631644586431294 : ((p1 → (p2 ∧ (p2 ∨ ((((False → p4) → False) ∨ p5) ∧ (((p2 → (p1 → (p2 → (p5 ∧ ((p5 ∨ True) ∧ False))))) → p5) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45877222228736081145614711619 : (((p3 → ((False → ((p4 ∧ (p4 ∨ True)) ∧ p4)) → ((p3 → (p4 → (p2 → ((True → p1) ∨ p2)))) ∨ ((False → True) → p4)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8824238307023564121085202338 : (((((p2 ∨ ((p2 → ((p1 ∨ (p2 → p3)) ∧ p5)) ∧ (p5 ∨ p1))) ∧ (((p3 → p5) → True) ∧ p5)) → (p2 ∧ (False ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339796346618477302333821198058 : (p1 → (p5 ∨ ((((p1 ∨ (((p3 ∧ p5) ∧ (((p4 → p2) ∧ ((p5 ∧ p1) ∧ p5)) → p1)) → (p5 ∨ p2))) ∧ p1) → p5) ∨ (False → p5)))) := by
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
theorem thm_5_vars_780537601850952378302239843872 : (((p2 ∨ (((((p3 ∧ p3) → p1) ∨ p3) → (p5 ∧ (False ∨ (False ∧ p5)))) ∨ ((((True ∧ (p5 ∧ (p5 ∧ p3))) ∨ p3) → p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249670097486680055470001888197 : ((p5 ∨ p4) ∨ ((((p1 ∨ p1) ∨ ((False ∨ p3) → p1)) ∧ ((p2 → ((True ∧ False) ∧ (p1 ∨ True))) ∨ (p1 → p1))) ∨ (p4 → (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40415693569933840140441458883 : ((((((((p1 ∨ ((p5 → p5) ∨ (p3 ∧ (p2 ∧ p4)))) ∨ False) ∧ False) → (p3 ∧ p2)) → (((p4 → p4) → p2) ∨ True)) ∨ p3) ∨ p4) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51268060028512430383321622753 : ((((True → p2) → (p5 ∨ ((p3 ∨ (False ∧ (((False ∧ (p1 ∨ False)) ∨ p4) ∧ False))) ∨ p2))) ∨ ((True ∧ (p5 ∨ (False → p2))) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214397420639921654603143518893 : (((False → (p5 ∨ p4)) → p1) ∨ ((((True → p3) ∨ p1) ∨ p4) → (((p1 ∧ p5) ∨ ((p3 → p3) ∧ (p1 ∧ (p3 ∧ p5)))) ∨ (False → False)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564872688746352685994018493469 : (((True → (((True ∧ ((p3 ∧ p2) ∨ (p2 ∧ (p3 ∧ p4)))) ∧ (((p5 → (p2 ∨ p3)) ∨ p2) ∨ (((p2 ∧ p3) ∧ p5) → p4))) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_65083142236596504148125687115 : ((p2 ∨ (False ∨ ((((p5 ∧ ((((p4 ∨ p1) ∧ True) ∧ (p1 → p4)) → ((p5 → p3) ∨ False))) ∧ ((p5 → p4) ∨ p1)) ∨ True) ∧ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398370223011430292555985533103 : ((((p5 ∨ ((((p2 → p5) → False) ∧ True) ∨ (p5 ∧ ((True → p3) ∨ ((p4 ∧ p2) ∧ ((p5 ∨ p5) → ((False ∨ p5) ∧ True))))))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_60286535019367182953147885059 : (((p1 → True) → (((False ∨ p5) ∧ False) ∧ (((p2 → (True ∨ p3)) ∧ (p2 → (p4 → p1))) → (p4 ∨ (p3 → ((p5 ∧ p2) ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147672185107434654698235473033 : (((((False → True) ∧ (p2 ∧ (False ∨ (p2 ∧ (((p1 ∧ p3) ∨ (p2 ∧ p3)) ∨ p1))))) → (False ∧ True)) → p1) ∨ ((p2 ∧ p1) → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665096459684133252656262614015 : ((((p5 → ((p5 → (p5 → ((True → True) ∨ (True ∧ p3)))) ∧ (((p5 → p1) → ((p1 → p1) → p3)) → (p3 → p5)))) → (p3 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248221914372587441290871660929 : ((p2 ∨ p1) ∨ (((((p2 → p1) ∨ p1) ∧ p2) ∨ (p3 ∨ True)) ∨ ((((p4 ∨ (False ∨ p4)) ∧ (True ∨ (p1 ∧ p1))) ∧ True) → (p5 ∨ p1)))) := by
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
theorem thm_5_vars_54715081038001576425582637113 : (((((False ∧ (p3 → p5)) → p4) → (p4 ∨ p2)) → ((p5 → ((p5 → p5) → False)) → (p1 ∨ ((p3 ∧ p2) → ((p5 ∧ False) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249439716018090218438891054409 : ((p5 ∨ False) ∨ (((p1 → p3) ∧ (p2 ∧ False)) ∨ ((p5 ∨ ((False → p4) ∨ (((p5 ∨ False) ∧ p4) ∧ False))) ∨ (((p4 → False) ∧ p1) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223520615129363384734049164831 : ((False ∨ (False → True)) ∧ (p5 ∨ ((p3 → ((True → p3) ∧ False)) ∨ ((p3 ∨ (True → p3)) ∨ (p2 ∨ (p4 → (True → (False ∨ (False → p2))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324210560515202206318613672888 : (p5 ∨ ((True ∨ ((p5 → p2) ∧ (p1 ∨ (p3 ∨ (p4 ∨ p4))))) → (((p5 ∨ p2) → p5) ∨ (((p1 ∨ True) → ((p4 ∧ False) ∧ p3)) → p5)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
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
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : (p1 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h20 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h21 := h19 h20
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h27 : (p1 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h28 := h26 h27
          -- We need to get the left conjuct of h28 based on <expert-advice>.
          let h29 := h28.left
          -- We need to get the right conjuct of h29 based on <expert-advice>.
          let h30 := h29.right
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
          have h33 : (p1 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h32, we can now drive its conclusion.
          let h34 := h32 h33
          -- We need to get the left conjuct of h34 based on <expert-advice>.
          let h35 := h34.left
          -- We need to get the right conjuct of h35 based on <expert-advice>.
          let h36 := h35.right
          -- False on the left can always be used.
          apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782429322427644596640808782581 : (((p3 ∨ (((p1 ∧ ((((p4 → ((p2 ∨ (((p1 → p2) ∨ p4) → (p3 → p5))) ∧ False)) ∧ p4) → False) ∨ True)) → (p1 → p3)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_315247092514322322556268180780 : (p3 ∨ (((p2 ∨ p5) ∧ (p2 ∧ p1)) ∨ ((((p2 ∧ ((p4 ∨ (p1 ∧ p4)) ∧ p3)) → (p2 ∨ p2)) ∨ (p4 ∨ p3)) ∧ (p3 ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81810386292086270500098047926 : (((((p3 ∨ (p1 → p2)) ∨ (p5 → (((p5 ∨ False) → (True → (True → p2))) ∨ ((p4 ∨ p5) ∨ p1)))) ∨ False) → ((True ∨ p5) ∧ False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ (p1 → p2)) ∨ (p5 → (((p5 ∨ False) → (True → (True → p2))) ∨ ((p4 ∨ p5) ∨ p1)))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186641859024342373754142982426 : (((p1 → (p1 → ((True ∨ False) ∨ (p3 → True)))) → (p1 ∨ False)) → ((((p3 ∧ p5) ∧ p2) ∧ (True → False)) ∨ ((p3 → (p4 → p5)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (p1 → ((True ∨ False) ∨ (p3 → True)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807002495006789921384128163174 : (((p4 → ((p3 ∨ (True ∧ (p3 ∨ (p2 ∨ (False ∨ ((p4 → ((p3 → ((True ∧ p3) ∨ p4)) ∨ p4)) ∧ p5)))))) ∨ (p3 ∨ (False → p1)))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350021520926019564612512913419 : (p4 → ((((((((p4 ∨ p5) ∧ p3) ∨ (p4 → ((p2 → ((p5 → (p1 ∨ False)) → p5)) ∨ p1))) → (p1 ∧ False)) → p3) → True) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303953124690389571734659345131 : (p1 ∨ ((((False → p2) → (p3 ∨ p4)) ∨ ((p2 → p4) ∨ ((((True ∨ p1) → (True ∧ p2)) → (True ∨ ((False ∧ p3) ∧ True))) ∨ p5))) ∨ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244371539895366919757265962409 : ((False ∧ p1) ∨ ((((p4 ∨ False) → (p3 ∧ ((p1 ∧ (p2 → True)) ∨ ((((p1 → p3) ∧ p3) ∧ False) ∨ p3)))) → (p3 → (p2 → p3))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46662821391700935832216769212 : (((False ∨ (((p1 → p5) ∨ (p2 ∧ p4)) ∨ ((False ∨ ((True ∨ (p5 ∨ False)) → ((False ∧ p3) → (p2 → p4)))) ∨ p1))) ∧ (p3 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64442343998742326140661436383 : ((p1 ∨ (((p3 → p2) ∧ ((p1 ∨ p2) ∧ ((False ∧ ((p3 ∨ ((False ∨ p2) ∧ ((p2 ∨ p2) ∨ False))) → False)) ∧ p4))) ∨ (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178671958689223210233061466492 : (((p4 ∧ ((p1 ∨ p3) → p3)) ∧ (p1 ∨ (p2 → (p1 ∨ (p2 → p3))))) ∨ (p4 ∨ (((p5 ∧ True) ∧ p1) → (((p4 ∧ False) → p1) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260086486582599689145517095545 : ((p2 → False) → (p5 ∨ ((((p5 ∧ p5) ∨ (p5 ∨ (p5 → ((p2 ∧ p3) ∨ p3)))) ∨ (True ∨ ((p4 ∨ (True ∨ p2)) ∧ True))) ∨ (p4 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_308367024867658047583587560755 : (p2 ∨ ((((((p3 → (((((p2 ∧ p3) ∨ ((False ∧ p4) ∧ p1)) → p1) ∨ False) ∨ (p5 ∧ p1))) ∧ (p5 ∨ p2)) ∨ p2) ∧ p4) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186098457547974986427698507537 : ((((p1 ∨ ((False ∨ p2) → (p3 ∧ p4))) ∧ (True ∨ True)) ∨ p2) → ((((p2 → p1) ∨ p3) ∨ (False → p1)) ∨ (((p1 → True) ∧ True) ∧ True))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47868361724001194551687641605 : (((((False ∨ (False ∧ (p3 ∨ (((p4 ∨ True) ∨ p5) ∨ True)))) → ((((p1 ∨ p5) ∨ True) → False) ∨ True)) ∧ (p1 ∨ p5)) → (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659310222627340799024566052612 : ((((p5 → ((p1 → ((p5 ∧ p3) → (p3 ∨ (p1 → p4)))) ∧ ((p3 → (p1 ∨ (p5 ∨ (p4 ∧ p4)))) → (p1 ∨ p3)))) ∨ (True ∨ p2)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_336419910516646322260400930930 : (p1 → ((False ∨ ((((p1 ∧ ((p5 ∨ False) ∧ (p3 ∨ (True → p5)))) ∨ ((p1 ∧ p3) ∨ p5)) → p3) → ((p3 ∨ (p2 ∨ p5)) ∨ p3))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



