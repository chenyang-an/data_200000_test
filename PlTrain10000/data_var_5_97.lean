variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213176377477546877452196080649 : ((((False ∨ p3) ∨ False) ∧ p1) ∨ (((True ∧ (p4 ∧ p5)) → ((((False ∧ False) ∨ p2) ∨ p3) → (p2 ∨ True))) ∨ ((True → (p5 ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775762057649988651414921260680 : (((False ∨ (p4 ∨ (((p4 → (p3 ∨ ((((p2 ∨ (p2 → p3)) ∧ ((p5 ∧ (p4 → p1)) → p5)) ∨ p1) ∧ False))) ∧ False) ∧ (False → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748610945823997858663929522963 : ((((p3 → p1) → (p5 ∨ ((p1 → (False → ((p4 ∧ ((False → p1) ∨ p1)) ∧ p5))) ∧ ((((True → False) → (p2 ∧ False)) ∧ p5) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178316731802764660414590432484 : (((((p2 → (p1 ∧ (p3 → (p2 ∨ True)))) ∨ p4) → p3) ∨ (p3 ∨ p1)) ∨ (True ∨ (((p2 ∧ True) ∨ p5) ∨ (False ∨ ((True → p5) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253805734028052366805032166608 : ((p1 ∧ p2) → ((p2 ∧ ((((p1 ∧ (True ∧ (p5 ∨ p5))) ∧ p4) ∨ p5) ∨ (p4 → p5))) → (((p1 → False) ∧ p4) ∨ (False → (p5 ∨ p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h1.left
        let h15 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h1.left
        let h19 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h1.left
    let h27 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694192940179001948286706307714 : (((((p2 → (p5 → (p4 ∧ (p4 ∨ p5)))) → (p4 ∧ (p4 → (True → p2)))) ∨ ((((True → True) ∧ (p4 ∨ True)) ∧ (True ∨ p3)) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717805418717595781693695495151 : ((((((False → p4) → p3) ∧ True) ∨ (((p1 ∨ p4) ∨ ((p5 ∧ p5) → (p3 → (False ∨ p1)))) ∧ (False ∨ (p5 → ((p3 → True) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300074451502500419293588632724 : (False ∨ ((((p4 ∨ (((True ∨ (p2 ∨ ((p4 ∨ p5) → ((True → p3) ∧ False)))) ∧ p3) → ((True → p3) ∨ p3))) → p3) → p2) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341734426469905471996591840723 : (p2 → (((p4 ∨ p5) ∧ ((True ∧ (p1 → (p1 → ((p4 ∨ p4) → (p1 ∧ ((True ∧ p5) ∨ (p1 ∨ (p1 ∨ p3)))))))) ∧ p5)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355844825027683767236930098398 : (p5 → ((((p3 → p1) ∧ (p2 ∨ (False → ((p4 ∧ ((p1 → (True ∧ p5)) → (p1 → (False → p1)))) ∨ p4)))) → p4) ∨ ((p4 → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789458013207290288087695717213 : (((p5 ∨ (((p1 ∨ (((p4 ∧ (p1 ∨ p1)) ∧ p4) ∧ (True ∧ p5))) ∨ False) ∨ (p5 ∧ ((p3 → (p3 → p1)) ∨ ((p4 ∧ p3) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615731111717422003073829152297 : (((((True ∧ ((p2 → (p3 ∧ (p5 ∨ ((p3 → p3) → (p4 ∨ p5))))) ∨ p3)) ∧ ((((p1 ∧ p4) ∨ p5) ∨ p1) ∧ (True ∨ p4))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_556747785460490855010870529929 : (((p3 ∨ (((((((p2 ∧ (False → (True → (False ∨ p4)))) ∧ p5) ∨ True) ∧ (p5 ∧ False)) ∨ p1) ∧ p5) ∨ ((False ∧ (False ∨ True)) → p5))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258155215379727942420264415456 : ((p4 ∨ p4) → ((((p5 ∧ ((False → (p5 → p5)) → True)) ∨ ((p3 ∨ (p5 ∧ (p4 → (p2 ∧ ((True ∨ p2) ∧ True))))) ∨ p1)) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_65363004052094687209245394644 : ((p3 ∨ (((True → (((True ∨ p4) ∨ ((True ∨ p3) ∧ p4)) → p1)) ∧ p5) ∨ ((((p3 → (p2 ∨ (True ∧ True))) → p3) ∧ p2) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166000055322045138076726993549 : (((p5 ∧ p1) ∨ (((p1 ∧ ((p5 ∧ (p5 ∨ (p2 → True))) ∨ (True → True))) ∧ False) ∨ False)) ∨ ((p1 ∧ (((True ∧ False) → p2) ∧ False)) → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60857451849974528042081420582 : ((True ∧ (p4 ∨ ((p5 ∨ (p4 → (((p1 ∨ p1) → p5) ∧ p5))) ∨ ((p5 ∧ False) → (p4 → (((p3 ∨ p2) ∧ (False ∧ p1)) → p4)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699110960597689060294706862071 : ((((p5 ∨ ((p1 → p2) ∧ ((((p1 ∨ p1) → p1) → p2) ∧ p2))) ∨ ((p3 ∧ (False ∨ (p4 ∨ p4))) → ((False ∧ (True ∧ p2)) ∨ True))) ∨ p3) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172432597752432446184641602521 : (((p4 ∨ (p2 ∨ (False ∨ False))) ∧ (((p1 ∧ ((True → p2) ∧ False)) ∨ p3) ∧ p1)) ∨ ((((p1 ∨ True) → p5) → (p2 ∧ (True ∨ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252491080445214475444519340737 : ((p5 → p1) ∨ (False ∨ ((((((((False ∧ True) ∨ (p2 ∧ (p4 → (True ∧ (p1 ∨ p2))))) ∨ p5) ∧ p3) → p4) ∧ (p1 ∨ p5)) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326878885619192685477923739403 : (True → ((((p2 → ((p5 ∨ ((False ∨ False) ∨ p1)) → (p3 ∧ p5))) → ((True ∧ (p3 ∧ (True → False))) ∧ ((False ∧ False) → p3))) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217895017485743364799001793821 : (((p3 → (True ∧ True)) → p3) → (((p1 ∨ p4) ∧ ((p5 → ((((p2 → p2) ∨ p1) → p5) ∧ (p2 ∨ False))) → ((p2 ∧ p5) → p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (True ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38619813277067942973921287763 : (((((((p3 ∧ False) ∨ (p2 ∨ p3)) → p1) ∧ False) ∨ ((((False ∨ (True ∨ (p2 ∨ p3))) → True) ∧ p5) → ((p4 ∨ True) ∧ p3))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789266607857689237795999060182 : (((p5 ∨ (((((p5 → (p1 → ((p5 ∨ True) ∧ p2))) ∨ (p3 → p3)) ∨ ((p1 ∨ p2) → True)) → p2) → ((p4 ∨ (p4 ∨ False)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173896292730310569699385227314 : ((((p4 → (p2 → ((p4 ∧ (p4 ∧ p1)) → (p2 ∧ (p3 ∧ True))))) ∨ p4) → p2) → ((p3 → p1) ∨ ((False ∧ (True → (p5 ∧ False))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760144412221654022069884196673 : (((p2 ∧ (((True → p4) → False) → (p3 → (((p3 ∧ p2) ∧ (p4 → p2)) ∧ (False ∨ ((p1 ∨ (p1 ∧ ((p2 → p1) ∨ False))) ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228224571716964889955273331627 : ((p5 ∧ (p3 ∨ p3)) ∨ ((p2 ∧ p3) ∨ (p5 → (((p3 ∨ (p3 ∨ True)) ∨ ((p4 → p1) ∧ (p3 ∧ p4))) ∨ ((p3 → p1) → (True ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_665077439237582770650405604324 : ((((p5 → ((p4 ∧ ((p1 → ((p4 → p4) → (((True ∧ (False ∨ True)) ∧ p1) ∧ ((p1 ∨ p2) ∨ p5)))) ∨ p1)) → p3)) → (p4 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68631964509949867325904133262 : ((p4 → ((p5 ∨ (p2 ∧ ((True ∨ p1) → (((p2 → p2) ∧ ((p3 ∧ (p4 ∧ p1)) ∧ p3)) ∧ (False ∨ (p4 → (p3 ∨ p4))))))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48185282141606639104250931154 : ((((True ∨ True) ∨ (((True ∧ p2) → p5) ∧ ((p1 → (((p4 ∨ (((False ∨ p4) → p4) ∧ p2)) ∨ p5) → p3)) ∧ True))) → (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217987742910169606168066292285 : (((p4 ∧ p1) ∧ (p4 → p1)) → ((((p3 → ((((p4 → p1) ∨ True) → False) ∨ (p1 → p1))) ∨ True) ∨ False) ∨ (p1 ∧ (False → (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230758535977480163083085706562 : (((True ∧ True) ∨ p1) → ((((p3 ∨ (True ∨ (p4 → (True ∧ (True ∨ (False ∧ ((p3 → p2) → ((False ∧ True) ∨ p3)))))))) → p3) ∨ p5) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693836673140015891752937219738 : ((((((p4 ∨ (False → p4)) ∨ (((p3 ∨ p1) ∧ p5) → (p3 ∧ True))) → p4) ∨ (True ∨ (((p3 ∧ (p3 ∨ p2)) ∧ (False ∧ p5)) → p1))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_116820763087642069246789379178 : (((p4 ∨ p4) ∨ (((True ∨ ((((p2 ∨ p5) → False) → (p5 ∨ (p5 → False))) ∨ p4)) → ((p3 ∧ (False → p4)) → False)) ∨ p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147237532170173912074081540431 : ((((((True → False) → (p3 → (True → ((p2 ∨ True) ∧ (p1 → (True ∧ p1)))))) ∧ (p1 ∨ p3)) ∧ False) ∨ p4) ∨ ((True ∧ p4) → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_388490992234904548209664630452 : ((((((False → True) ∨ ((((False ∨ p4) → False) ∧ (p3 → (p4 ∨ p3))) → ((p3 → True) ∨ p5))) → (((p1 → p3) → p5) ∨ p2)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_47370810751553121260621701145 : ((((p3 → p4) ∨ (((((True → (p4 ∧ p3)) → ((True ∨ False) ∧ p4)) ∨ p3) ∧ (p3 → (p2 → p3))) → (False ∧ True))) ∨ (True ∧ True)) ∨ False) := by
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
theorem thm_5_vars_226043780886121020814323619616 : (((p5 ∧ False) ∨ p4) ∨ (p4 ∨ (False ∨ (((((((True → p1) → p4) ∧ (False → False)) ∨ p1) ∧ False) → (p2 → ((p4 ∧ p3) ∧ False))) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195816084375053826406917485788 : (((p3 ∨ True) → (False → ((p1 → p3) ∨ p2))) ∧ ((True ∧ (p1 ∨ ((p1 ∨ ((p3 ∧ (p5 → False)) ∨ ((False ∨ p3) → p5))) → p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173001996299999992043638173027 : ((p5 ∧ ((p2 ∨ (p3 ∧ p5)) ∨ (False ∧ ((p1 → p4) ∨ (p3 → (p2 ∨ p3)))))) ∨ ((True → False) ∨ ((((p4 → p3) ∧ p2) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683420920452411315046450991637 : ((((False → (True ∧ (((p2 → (True → ((p5 ∧ p5) → p1))) → (p5 ∧ (p3 ∨ p3))) ∧ p3))) ∧ (p4 ∨ ((p4 → p2) → (p1 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477194319051525045215475875344 : ((((((p4 ∧ (p2 ∧ p1)) → ((p5 ∧ p3) ∧ p3)) ∧ p5) → (((((p4 → (p1 → (p3 ∧ p4))) ∧ p3) ∨ (p1 ∧ False)) → p5) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142997442695302258725325809754 : ((True → ((p1 ∨ (((p2 ∧ p3) ∨ (((p1 ∨ p5) ∨ p5) ∧ p1)) ∨ True)) → ((False ∧ (p3 ∧ p3)) ∧ (p1 ∧ p2)))) → ((False ∧ p4) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ (((p2 ∧ p3) ∨ (((p1 ∨ p5) ∨ p5) ∧ p1)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∨ (((p2 ∧ p3) ∨ (((p1 ∨ p5) ∨ p5) ∧ p1)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197087402370114622237318927475 : (((p1 ∧ (p4 ∨ (p1 ∨ (p2 → p4)))) ∨ p2) ∨ (p5 → (p2 → (p2 ∨ ((False → (((False ∧ p1) ∧ ((p1 ∨ p1) → p3)) → p1)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2069217985673003634522286961 : (((((p3 → True) ∧ p4) → ((p1 → (((p5 → p2) ∧ (p2 ∧ p5)) ∧ p4)) ∧ p4)) ∧ p4) ∨ (((p5 ∧ (p4 ∧ p2)) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147718928938788245694661426071 : (((((p5 ∧ p1) → (p5 ∧ (False ∨ (False → True)))) ∨ ((p5 ∨ False) → ((p4 ∧ p1) → (False ∧ p1)))) → p4) ∨ ((p3 ∧ (p3 ∨ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661206960820163835088681023886 : (((((((False ∨ p2) ∧ (p4 ∧ p1)) ∨ ((p1 ∧ (True ∧ p3)) → (((False ∧ False) ∨ True) ∨ (True ∨ p2)))) ∨ (p5 → p5)) → (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305172587811869540587133309483 : (p1 ∨ (((((p4 ∧ True) ∧ ((False → (p4 ∨ (p2 → False))) ∧ (p5 ∨ p1))) ∨ p1) → ((True ∧ False) ∨ False)) ∨ ((p3 ∨ (p4 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141562252325994374532715246467 : (((True → (p2 → False)) ∨ (((p5 → p1) ∧ (((p4 ∧ ((p4 ∧ p4) → False)) ∨ p5) ∨ p3)) ∨ ((p1 ∧ p3) → p1))) → (False ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246629298009175707243576332489 : ((p5 ∧ p3) ∨ ((((p2 ∧ (((((p2 ∧ p1) ∨ p3) ∨ (((p2 ∨ p3) ∨ (False → p1)) ∨ False)) ∨ p5) → True)) → False) ∨ True) ∨ (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_858030966484912055222427956832 : ((((((((((p1 → (p3 → p1)) ∧ p1) ∨ (p2 → ((True → (p3 → p2)) ∧ False))) ∨ True) → p1) ∧ ((p5 ∧ p5) → p4)) → p1) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p1 → (p3 → p1)) ∧ p1) ∨ (p2 → ((True → (p3 → p2)) ∧ False))) ∨ True) → p1) ∧ ((p5 ∧ p5) → p4)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((((p1 → (p3 → p1)) ∧ p1) ∨ (p2 → ((True → (p3 → p2)) ∧ False))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46893464846454832406962991018 : ((((((p4 ∨ ((p3 ∧ (True → p5)) → (p3 ∨ ((False ∨ p1) ∨ (p4 ∧ (p1 ∨ (False ∧ p3))))))) → p3) → p5) ∨ p2) ∨ (p1 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136390994100167084049698944956 : (((p1 ∧ ((p5 → p5) → True)) ∨ ((((((p4 → False) ∧ (p5 ∨ p3)) ∧ p3) ∧ (True ∨ p2)) ∧ p5) ∧ (False → p1))) ∨ (p4 → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691509923341867793435548944976 : (((((False → p5) → (p4 ∨ ((p2 ∨ (False → (p1 → ((p5 ∨ False) ∨ True)))) → p4))) → ((((p2 → p2) ∨ False) → (p1 ∨ p2)) ∨ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p2 ∨ (False → (p1 → ((p5 ∨ False) ∨ True)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124637837202343986310016947712 : (((((p2 → (p1 ∨ p5)) ∧ p4) ∨ True) → (((((p2 ∨ (p1 ∨ p4)) → False) ∨ p3) → ((True → (p1 ∧ True)) → p1)) → p5)) → (p5 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → (p1 ∨ p5)) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p2 ∨ (p1 ∨ p4)) → False) ∨ p3) → ((True → (p1 ∧ True)) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h15 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116592079765389517691020816712 : (((p4 ∨ p5) ∧ (p5 ∨ (((((p3 ∧ (((p2 ∧ (p5 → True)) ∧ (p4 ∧ p4)) → (p3 → p3))) ∨ p2) → p2) ∧ p1) ∧ p1))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147583480084410759108463873788 : ((((True → (p5 ∨ (p3 → ((p4 → (p1 → (((True → p1) ∨ p5) ∨ (False ∨ True)))) → p4)))) ∧ True) → p1) ∨ (p5 → (p3 → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64260256743814677208691746270 : ((False ∨ (p4 ∨ (p3 ∨ (((False ∨ (((False ∨ p3) ∧ p3) ∨ ((p3 ∧ (True → p4)) → p2))) ∧ p5) → ((p4 ∧ p1) ∧ (p1 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646789839337744251631971613558 : ((((p2 → ((((p2 → p4) → p3) ∨ (p5 ∧ ((True → (p4 ∧ True)) → (p5 ∨ (True ∧ False))))) ∨ (p4 ∧ ((p1 → True) ∨ p2)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209479300343480041950205616353 : ((p3 → ((p3 ∨ p3) ∨ (p4 → True))) → ((((True → (False ∧ True)) ∨ ((((p2 ∨ (True → True)) ∨ False) → p4) ∨ p3)) ∨ (p2 → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56558478395345679381345320427 : (((p4 ∨ ((p4 → p1) → p4)) → (((False ∨ (p1 → p2)) → (p1 → ((p2 ∧ (False ∨ p3)) → p2))) → (p1 → ((p3 ∧ p2) → p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40445733106041301899301417522 : ((((((p5 ∨ (True → (True ∧ p2))) → p3) ∧ ((False ∧ False) ∨ ((True ∧ (p4 → p2)) ∧ ((p4 ∨ p5) → (True → p2))))) ∨ False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774278646322135186225963602857 : (((False ∨ (((p2 → (((((p1 ∨ p4) → p4) ∨ (p1 ∨ (False ∨ p3))) → p4) ∨ ((p5 ∨ p1) → p2))) ∧ p1) → (p4 ∨ (p2 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165787660051087452565908858528 : (((p4 ∨ ((p4 ∨ p2) ∧ True)) → (p2 ∧ ((p5 ∧ ((p5 → p2) ∨ False)) ∧ (p1 ∧ True)))) ∨ (True ∧ ((p5 ∧ (False ∨ p1)) → (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307195865871890569747857449969 : (p1 ∨ (p1 ∨ ((((p5 → (((p5 → p2) → True) → ((p3 → p2) → p3))) ∨ ((p1 ∧ p5) ∨ (p4 ∧ p2))) ∧ p5) ∨ (p4 → (p5 ∨ True))))) := by
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
theorem thm_5_vars_784843884500535534969492288006 : (((p3 ∨ (p1 → (((((True ∨ (p5 ∨ True)) → False) ∨ (False → ((p3 ∧ (((False → p2) ∧ p2) → False)) ∧ (p5 ∧ p2)))) → p5) → p5))) ∨ p1) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True ∨ (p5 ∨ True)) → False) ∨ (False → ((p3 ∧ (((False → p2) ∧ p2) → False)) ∧ (p5 ∧ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667307250253041789618198111609 : (((((p4 ∧ p2) ∨ ((p4 → (((((p4 ∧ True) ∨ p3) ∧ p5) ∨ False) → (False ∨ False))) ∨ ((True ∨ True) ∨ p1))) ∧ ((False ∨ True) ∨ False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745027421031400430961201935064 : ((((p4 ∧ p1) → (p2 ∨ (((p5 → ((((p4 ∧ p2) → True) ∨ (p3 → True)) ∨ p1)) ∧ (p1 ∨ True)) → (p2 ∨ ((p2 ∧ p5) ∨ p4))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41090831107025962088385481660 : ((((((False → p3) ∨ (((p3 → (p1 ∧ (True → p5))) → p3) ∨ ((False ∨ (True ∧ p3)) → p5))) → p5) ∧ ((p2 ∨ p4) ∧ True)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305223744341299247270908595158 : (p1 ∨ ((((((True ∧ p5) ∨ False) ∨ p2) ∧ (p2 ∨ p4)) ∨ ((True → (p2 ∨ p2)) ∧ ((False ∨ False) ∧ p3))) → ((p2 → (p3 ∨ False)) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h4
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
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60662419481143021627660444520 : ((True ∧ ((False ∨ ((True ∧ False) → (p3 ∧ ((p1 ∨ False) ∨ ((p2 ∧ True) ∧ ((False → p5) ∨ p1)))))) → ((p5 ∨ (p2 → False)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244311818231356037653882494068 : ((False ∧ False) ∨ ((((p3 ∧ True) ∨ (p4 → p3)) ∨ ((((((p2 → p4) ∨ False) ∨ p1) ∧ p5) ∨ ((True ∧ p1) ∨ True)) → (p2 → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195224319471006995296095972853 : ((((p5 → True) → (p1 ∧ p2)) ∨ (p2 ∨ True)) ∧ ((p1 ∧ (p5 ∧ p5)) → ((((p5 ∧ p1) ∧ (((False ∨ False) → True) ∧ p2)) ∧ True) → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200268689500161607748754953918 : (((p1 ∨ (p2 ∨ p3)) → (p4 ∧ (p3 ∧ False))) → (((p2 ∧ ((((((p5 ∧ p4) ∨ (p1 → False)) ∧ p1) → p1) → p4) → p5)) ∧ True) → p1)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ (p2 ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65745537047806720836365509463 : ((p4 ∨ ((((False → (False → ((((p5 ∨ p1) ∨ (((p3 ∧ p5) → p2) → p4)) → False) ∨ p2))) ∧ p3) ∨ p5) → ((p5 → p4) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667913515701195054998338631664 : ((((p2 ∨ ((False ∧ (p1 ∧ ((((True ∨ p2) ∧ p2) ∧ (p4 ∨ False)) → p4))) ∧ ((p5 ∧ p3) ∧ (True ∨ p5)))) ∧ (True ∧ (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116614656654480280373529234109 : (((False → True) ∧ ((((p1 ∨ (p5 ∧ p1)) → ((p4 ∧ False) ∨ (p1 ∨ p1))) ∧ (p4 ∨ (p5 ∨ (p4 ∧ (True ∧ True))))) → p3)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724479881904244049908325328943 : ((((True ∨ (p5 → p3)) ∧ ((p2 ∨ (((((False ∨ p5) ∧ (False ∧ ((p3 ∧ p2) ∧ False))) ∧ ((p1 → p2) ∧ p2)) ∨ p4) ∨ True)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42602889899917000984654386327 : (((p2 ∨ (p4 → (((False → (p5 ∨ (p3 → p2))) ∨ ((p2 ∨ ((p3 ∧ False) → (p2 ∨ True))) ∧ (p2 ∧ (p1 ∧ False)))) → p1))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613312244473362091510726680408 : (((((((True → p1) → p1) ∨ (((p1 ∧ (True ∨ (p4 ∧ p4))) ∨ p4) ∨ (False → (((p3 ∧ p4) ∧ p2) → p5)))) → (p4 ∨ p5)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_126828493617278878890661497326 : ((p5 ∧ (((True → ((((p5 → (p5 ∨ (True ∧ p1))) → True) ∧ (p4 ∧ p2)) ∨ p1)) → True) ∨ (True ∧ ((p2 → p3) → p5)))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338085655842541671402623281269 : (p1 → ((p5 → (False ∧ (((p2 ∨ (True ∨ True)) ∧ p5) ∧ p2))) → ((True → ((p5 ∨ False) ∧ (p3 → (((False ∧ p5) ∨ False) ∧ p5)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115765014611091401987633954925 : (((p4 ∨ (((p1 ∨ p4) → p4) → p1)) → ((p3 → (((True ∧ p1) → ((p2 ∧ p1) ∧ (p2 → (False ∧ p5)))) → p5)) ∨ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340917299892523268636355258588 : (p2 → ((((((p5 ∨ p2) → p4) ∧ (p2 → p3)) → p3) → ((False ∧ ((((p4 → p1) ∨ p4) → False) ∨ False)) ∨ (p2 → (p4 ∨ p2)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48940119985789503046405705554 : (((((p1 ∨ (True ∨ (p2 ∧ p3))) ∧ (p4 → (((p4 ∧ (p3 ∧ (p5 ∨ (False ∧ p5)))) ∧ False) ∧ True))) ∧ True) ∨ ((p5 ∨ True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316499679384509630452859742976 : (p3 ∨ (p2 ∨ (((p2 ∨ p4) ∨ ((((((p4 → p3) → p5) ∨ (p1 → p4)) ∨ p3) ∧ True) → (((p4 ∨ True) → p3) ∧ True))) ∨ (False → p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40170979567425826494856502537 : (((((True ∧ (False ∨ ((p1 → p4) ∨ p5))) ∧ ((True → (((p3 ∧ p1) ∧ ((p1 → (p4 ∨ p1)) ∨ p2)) ∨ False)) ∨ p4)) ∧ p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168112962638013759535778502412 : (((True → (True ∧ (p3 ∨ False))) ∨ ((p5 ∨ (p2 ∨ ((False → (True ∨ False)) ∨ p5))) ∨ p3)) → ((p2 ∨ p2) ∨ (False → ((True ∧ p4) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- False on the left can always be used.
        apply False.elim h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h12
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- False on the left can always be used.
            apply False.elim h12
            -- False on the left can always be used.
            apply False.elim h12
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- False on the left can always be used.
            apply False.elim h14
            -- False on the left can always be used.
            apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201826649893646216216053260106 : ((((p5 ∨ p5) ∧ (p2 ∧ True)) ∨ True) ∧ ((False ∨ (p1 → ((p1 ∧ p1) ∧ ((p1 → p4) ∧ False)))) ∨ (p1 ∨ (((True ∧ p5) → True) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_49076009599453699099567231331 : ((((((((p2 ∧ (((p1 → p2) ∨ p4) ∨ p1)) ∧ p5) → (True → p3)) → p2) → (p4 ∧ p4)) → (p4 ∨ False)) ∨ ((False → p3) ∨ p5)) ∨ p2) := by
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
theorem thm_5_vars_42949251974195120686624279690 : (((p4 → (p3 ∧ ((((((p1 ∨ p2) ∨ (((((p2 → p1) ∨ True) ∧ p4) ∨ p2) → True)) → p5) ∧ (p2 → p5)) ∨ p1) → p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708589836749945893626070575080 : (((((p1 ∧ (True ∨ (p2 → (False ∨ True)))) ∨ p5) → ((((p5 → p5) ∨ (p1 → ((p5 ∨ (p3 ∨ p1)) ∨ p5))) ∧ (p5 ∨ p5)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_965831138748591096702126654346 : ((((p4 ∧ p3) ∨ ((((p4 → p4) ∨ p5) → ((p5 ∨ (((p1 ∨ p1) → (False ∨ (p4 → p5))) ∨ True)) ∨ p2)) → ((p1 ∧ p5) ∧ p4))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p4 → p4) ∨ p5) → ((p5 ∨ (((p1 ∨ p1) → (False ∨ (p4 → p5))) ∨ True)) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h6
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136205562133562600994065059358 : (((p3 ∨ ((p2 ∨ False) ∨ (p4 → True))) ∧ ((p3 ∨ p1) ∧ ((((p1 ∧ (p4 ∧ p2)) ∧ (p1 ∨ p3)) ∨ p2) ∧ True))) ∨ (True ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152845954123143083821045820821 : (((p2 → True) → (p2 → ((True → (((((p1 → p5) → p3) ∨ ((False ∧ p1) ∨ p1)) → p5) ∧ p1)) ∧ p5))) → (((p1 ∧ p3) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60174555414365667179949886856 : (((p5 ∨ False) → ((p4 ∨ False) ∨ (((((True ∧ (p5 → (p2 ∧ p5))) ∨ (p1 ∨ (p4 ∧ p1))) ∧ p2) ∨ p1) → ((False ∨ p4) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234832582628244698998123310706 : ((p5 → (p2 ∨ p4)) → (True ∧ ((p4 → ((((p1 ∧ p2) ∨ False) → (((p1 → p1) → p5) ∧ (p3 → p3))) → p3)) ∨ ((False ∨ p2) → p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39225559281447926533416771949 : (((True ∧ (p3 ∧ ((p1 ∨ (((p5 → ((p4 ∨ (p5 → (p5 ∧ True))) → p3)) → p2) ∧ (p1 → ((p5 ∨ p5) → False)))) ∧ False))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350247459852849975854554486587 : (p4 → ((False ∧ ((((True ∨ (p5 ∧ (((p1 ∧ p1) → ((False ∨ ((False → p2) ∨ False)) → True)) ∧ False))) → p1) → (p1 → False)) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319455847078316273240843150405 : (p4 ∨ (((p2 ∨ (p3 ∧ (p4 ∧ ((p4 ∨ p2) ∧ p4)))) ∨ (p5 ∨ False)) ∨ ((p1 ∧ ((True → p5) ∧ ((True ∧ (p1 ∨ False)) ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



