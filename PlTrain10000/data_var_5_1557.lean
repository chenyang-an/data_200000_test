variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118810199993464576020210891657 : ((True → ((((p3 ∨ (p5 ∧ (p3 ∨ p4))) ∨ (((False ∧ True) ∧ p4) ∨ ((True → ((p2 ∨ False) ∨ p3)) ∧ False))) → False) ∨ p3)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207715111087860388784434995661 : (((p1 ∧ (p2 ∧ (p3 ∧ p2))) → p5) → (((((((((p1 → (p3 ∧ p2)) ∧ p5) ∨ p1) ∧ p2) ∧ p4) ∧ (False ∨ p4)) ∨ p3) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326991008072546688731745137841 : (True → ((((((p4 ∧ p4) → ((p1 ∨ (p1 ∧ p2)) ∨ p4)) → (p1 ∧ p1)) ∨ ((p1 ∧ p2) ∧ p3)) ∧ (((p4 ∧ True) ∧ p5) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246339449175627587988457518072 : ((p4 ∧ p5) ∨ ((p2 ∧ ((p5 ∧ ((p4 ∧ p1) ∧ True)) ∧ p4)) ∨ ((((p2 ∨ False) ∨ ((p1 → (p4 → True)) ∨ p1)) → (False → p4)) ∨ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135017828953651778644453139486 : (((True → (((p4 → False) ∨ (p2 ∨ ((p2 ∨ p2) ∧ (p3 ∨ p2)))) → (((p2 ∧ False) ∧ p1) ∨ p4))) ∧ (p3 → p4)) ∨ ((True ∧ False) → p2)) := by
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
theorem thm_5_vars_69043987539455865826080909004 : ((p5 → (((False ∨ ((p1 ∧ True) ∧ p2)) ∧ (((p2 ∧ ((p3 ∧ (p1 → (p4 ∨ False))) ∧ p2)) → (p1 ∧ (p1 ∨ p5))) ∧ False)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263683894322474980545545898754 : (True ∧ (((p4 ∨ ((p1 → ((p3 → ((((p2 ∨ p5) ∨ p4) ∨ True) ∧ p1)) ∧ p4)) ∧ p4)) ∨ True) ∨ (p4 → (((p1 → p4) ∨ True) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192789578072694699476654704201 : (((p1 ∨ (p1 → (((p3 ∧ p1) ∧ p2) ∧ p3))) → p1) → (((p3 ∧ (p1 → (((False ∨ (p5 ∧ (p3 ∨ p4))) → p3) ∧ p4))) ∧ p2) → p1)) := by
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
  have h7 : (p1 ∨ (p1 → (((p3 ∧ p1) ∧ p2) ∧ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216261611101934331674454811561 : ((p1 → (p4 ∨ (p4 ∨ p2))) ∨ (p5 ∨ ((((p4 ∧ ((True → True) ∧ (True ∧ p3))) → (False ∧ (False → (p2 ∧ False)))) → (p5 ∨ True)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_134111377593873248929357957242 : (((((p1 ∧ (False → p2)) → (((False ∨ p4) ∧ (True ∧ (p3 ∧ ((p1 → p4) ∨ p1)))) → p5)) ∧ (p5 ∧ p4)) ∨ True) ∨ (p5 → (p1 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248886225357506487928368844121 : ((p3 ∨ p5) ∨ ((p3 ∨ ((p5 → (p4 ∧ (((p2 → (p2 → p2)) ∧ False) ∧ p1))) ∧ False)) ∨ ((p3 ∨ (p1 ∧ (p4 ∨ (True → p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64286698146808939847877656713 : ((False ∨ (p2 → (((p3 ∧ (p2 ∨ True)) ∧ p2) ∨ ((p5 ∨ (p5 ∧ (((p4 ∧ (p3 → p5)) ∧ (p1 ∨ True)) ∧ True))) → (p4 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184475033948190660820217384949 : (((((False ∧ (False ∧ p1)) ∧ (p2 → p1)) ∨ p2) ∨ (p1 → p3)) ∨ ((p5 ∨ (p4 ∨ p2)) ∨ ((p3 → (p1 → p1)) ∧ ((True ∧ p1) ∨ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65646982902658098623725069453 : ((p4 ∨ (((False ∧ p2) ∨ ((p5 → (p1 ∧ (p3 ∨ True))) → (p4 → (p2 ∨ (((p1 → False) ∧ (p3 → (p5 → p2))) ∧ p2))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164859199019357194111556977898 : (((p1 ∨ (p2 ∧ (p3 ∨ ((True → p3) → (((False ∨ (False → p1)) ∨ p3) ∧ p1))))) ∨ p1) ∨ (p4 ∨ (p5 → (p2 ∨ ((True ∨ p1) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65632028838460902127757253053 : ((p4 ∨ (((((((p2 ∧ (False → ((False → p5) ∧ p4))) ∧ p1) ∧ (p1 ∧ p5)) ∨ (p2 → p1)) → (False ∧ True)) ∧ (p3 ∨ p2)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42842934243620614255589387689 : (((p2 → ((p5 ∧ (((((p1 ∧ (p2 ∨ p2)) → p2) → (p3 → True)) → (p4 ∨ (False ∧ True))) ∧ ((p4 ∧ p1) ∧ p3))) ∧ p5)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200489010121921257126049658142 : (((p1 ∧ p5) → ((True ∨ p3) ∧ (p3 → p5))) → ((p3 → ((p5 ∧ ((p2 → (p4 ∨ False)) ∨ p1)) ∧ ((p1 → p3) ∧ p1))) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213402887357943731484787463713 : (((p1 ∨ (False ∨ p4)) ∧ p2) ∨ (((p5 → (((p4 ∨ ((p4 ∨ p2) ∧ (p3 → p1))) ∧ True) ∨ p4)) ∧ p3) ∨ (p4 ∨ ((p2 ∧ p5) ∨ True)))) := by
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
theorem thm_5_vars_49189718949869093971752349225 : (((((p5 ∨ p3) ∧ p3) ∧ (((((p1 → p2) → ((p3 ∧ (True ∧ p2)) ∨ True)) ∨ False) ∧ (p4 ∨ p3)) ∨ p4)) ∨ (False → (p4 ∧ p2))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54287328287280083699497584651 : ((((False → (p4 ∨ p3)) → ((p2 ∨ p5) → p5)) ∧ ((p3 ∧ (False ∧ ((True ∧ (p5 → p4)) ∨ p1))) ∧ ((True ∨ (p4 ∧ p5)) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57975133185971252921862877062 : (((p3 → (False → False)) → (p1 ∧ ((p3 ∨ True) ∧ ((p1 ∧ (p5 → (((False ∧ (((p5 ∨ p1) ∨ True) ∧ p4)) ∧ p3) ∨ p5))) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311811029312801382839401931035 : (p2 ∨ (p1 ∨ ((((p4 → p4) → False) ∧ (((((p5 ∧ True) → ((p3 → (p2 ∨ p2)) → p1)) ∧ p4) → (False ∧ p5)) ∨ (p5 ∨ p1))) → p2))) := by
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
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p4 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : (p4 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h14
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302556679487310310341350360961 : (False ∨ (p1 ∨ ((((((p5 → ((p1 → ((p4 → p2) ∨ p1)) → p3)) ∨ True) ∨ p3) ∧ (p2 ∨ ((p3 ∨ (p4 ∨ p4)) ∧ p2))) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218440841026582869628783260842 : (((p3 ∧ p2) → (True → p3)) → (True ∧ (True ∧ ((p5 ∧ p5) → (((((False ∨ p3) ∨ False) → p4) → (p2 ∧ (p4 ∧ p2))) ∨ (False → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166402176039817603024298210362 : ((False ∨ (p5 ∨ (((p2 ∨ p2) ∧ (False ∨ (((p3 → p5) → p1) ∧ (p2 ∧ p1)))) ∧ True))) ∨ ((True ∨ ((False → True) ∧ p4)) ∨ (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207850955232975165357892530440 : ((((p5 → p1) ∧ True) ∧ (False → True)) → ((p2 ∨ p1) ∨ (False ∨ ((False ∨ (((((p4 ∧ p2) ∧ (p4 ∧ p1)) ∧ p5) ∧ False) ∧ p1)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h16.left
    let h20 := h16.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59007497506497798431728652900 : (((p3 ∧ p3) ∨ ((((p4 ∧ (p5 ∧ p4)) ∧ (True ∧ (((p2 ∧ p3) ∨ False) ∨ p2))) ∨ (((False ∧ p3) ∨ (p4 ∨ p3)) ∨ True)) ∨ False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_174159700471546892794483799726 : ((((p3 → ((p3 ∧ p3) → p3)) ∨ ((p5 → (p1 → p5)) → p4)) ∨ (p5 ∨ p2)) → ((((p2 → p3) ∨ (p2 ∨ p4)) ∨ (p2 → True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313249114140427116499539914420 : (p3 ∨ (((p4 ∧ p2) → ((((False ∨ (True → (False ∨ (p2 ∨ (p1 ∧ ((p1 ∧ p3) ∨ (False ∨ p3))))))) → (p5 → False)) ∨ p4) ∨ p2)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_116378474102182490408645659553 : ((((p1 → True) → p3) → (False ∨ ((((p1 ∧ ((False ∧ True) → p2)) → (p4 → p5)) → (p4 ∧ ((p1 → True) → True))) ∨ p1))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47092180457659266446049920681 : ((((p4 ∧ (p3 → ((((((p1 ∧ p3) ∨ p2) ∨ p2) ∨ p1) ∧ False) ∧ (((False ∨ p1) ∨ p5) → p5)))) → (p5 ∧ True)) ∨ (p3 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607422735120177770853110592604 : ((((((False ∨ p2) ∨ (((p2 ∧ ((p1 ∨ False) ∨ ((False ∧ p4) ∧ p3))) ∨ p2) ∨ ((((True ∧ p3) ∧ False) ∨ p5) ∧ p2))) ∧ p2) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178618581889852775700571295697 : ((((False → ((True ∨ p2) ∧ p5)) ∧ p1) → ((p3 → (p1 ∧ p3)) → p5)) ∨ (True ∧ (((p3 ∨ p4) → p2) ∨ ((p1 → p3) → (p5 → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44351105074826276856655950088 : ((((False ∨ ((p3 ∧ p2) ∨ (True → ((p4 ∨ ((p1 → (True → p4)) → p3)) ∧ p4)))) → (((p1 → p5) → True) → (p4 ∨ p3))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60077288868741480273589274987 : (((p2 ∨ p4) → ((True ∧ ((((p2 → (((p3 ∧ p1) ∧ p1) → ((p3 → p4) → p3))) → p4) ∨ False) → p1)) ∨ (p1 → (p1 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147897406033691480808275492886 : ((((True ∧ ((((False ∧ (p1 ∧ True)) ∧ ((p3 ∨ p4) ∧ (True → False))) → p5) → p5)) ∨ True) ∧ (p2 → p5)) ∨ (False ∨ (p3 → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746698732180732146472512911328 : ((((p3 ∨ p2) → (((p1 ∧ (((True ∧ False) ∧ (p2 ∨ True)) ∧ p4)) ∧ ((((p3 ∧ False) → p5) → (True → p4)) ∨ True)) ∨ (False → p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126985597159518075286745087567 : ((True ∨ (p1 ∧ (((p3 → p1) ∨ ((((p2 ∨ p1) → p4) → (p2 → (((False ∧ p5) ∧ (False → p4)) ∧ p4))) ∨ p5)) ∨ p3))) → (p2 ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260609038774970149150824315690 : ((p3 → p2) → (((p4 ∨ (((p1 ∨ p2) → p1) ∧ p2)) → (False → p2)) ∧ (((((True ∧ (True ∨ p1)) ∨ p1) → False) ∧ (p5 ∨ p5)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : ((True ∧ (True ∨ p1)) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : ((True ∧ (True ∨ p1)) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148937501246336553899726731851 : (((p5 ∧ ((True ∨ p4) ∧ p2)) → ((((p4 → True) ∨ (False ∧ (p5 ∨ (p4 ∧ (p3 → p2))))) → False) ∨ p2)) ∨ (((False ∨ p5) ∨ p3) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708873761879547556058325098512 : (((((p4 ∨ ((p5 ∧ p4) ∧ False)) ∧ (p5 → p2)) → (((p3 ∧ (True ∨ (True ∨ (False → (False ∧ p1))))) ∨ p3) → ((p4 → False) → p2))) ∨ False) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h23 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h24 := h3 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- False on the left can always be used.
          apply False.elim h27
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h1.left
        let h32 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h34 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h33
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h35 := h3 h34
          -- False on the left can always be used.
          apply False.elim h35
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Conjunctions on the left can always be decomposed.
          let h39 := h37.left
          let h40 := h37.right
          -- False on the left can always be used.
          apply False.elim h38
  case inr h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h1.left
    let h43 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h44 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h45 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h44
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h46 := h3 h45
      -- False on the left can always be used.
      apply False.elim h46
    case inr h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h47.left
      let h49 := h47.right
      -- Conjunctions on the left can always be decomposed.
      let h50 := h48.left
      let h51 := h48.right
      -- False on the left can always be used.
      apply False.elim h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48634364342754430193996821926 : ((((False ∨ (p2 ∧ ((p5 ∧ p5) ∧ ((p5 → (False ∨ (True ∧ p5))) ∨ (True ∧ p5))))) ∨ (p3 → (p5 ∨ p5))) ∧ (p4 ∧ (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52182138933688493720476139962 : (((((True ∨ p1) → (False ∨ p2)) ∧ ((((p3 → p5) → (True → p3)) ∧ p4) ∨ p3)) → ((p1 ∧ p2) ∨ (False ∧ ((p5 ∨ p1) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112118173593150440010068384157 : (((True ∧ (((p2 ∨ (p1 ∨ (p1 ∧ p3))) ∧ (((p3 → p2) ∨ (False ∧ ((p4 → True) → (p2 ∧ p1)))) → p4)) ∧ p3)) ∨ True) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46401095222068278490255654596 : ((((p3 ∧ ((p5 → ((p2 ∨ True) ∧ p1)) → p5)) ∧ (((True ∨ ((p4 ∨ p1) ∧ (p2 ∧ p2))) ∧ (p5 → p5)) ∨ p3)) ∧ (p5 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52968905408184094330446602122 : (((((((p1 → False) → (False ∧ True)) ∧ p4) ∨ (p4 → True)) → False) ∧ ((p5 ∨ ((p3 → ((p2 ∧ False) ∨ p2)) ∨ p5)) ∨ (False → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301079206513551092358672457825 : (False ∨ ((((True → ((False ∨ True) → p1)) → (False ∨ p5)) → True) → ((((p1 ∨ ((p4 → p1) → p4)) ∨ False) → p2) → ((p2 ∨ p1) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48144189646472075677317605886 : (((((p4 ∧ p1) ∧ True) → (p1 ∨ (p4 → ((p3 → p3) → (p3 ∨ (True → (p2 ∨ (((p1 ∧ p2) → True) → p4)))))))) → (p2 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720976297967292461686936093330 : (((((True → p2) ∧ (p4 → p5)) → (p3 → (((False ∨ p4) → ((((True ∧ True) ∧ (p5 ∧ p5)) ∨ p1) → False)) → ((p5 ∧ p2) ∨ True)))) ∨ p2) ∧ True) := by
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
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116219355903869473704994046103 : ((((p1 ∨ p4) ∨ p5) ∨ (((True → (((p2 ∧ (p1 ∧ ((p1 → p2) ∨ (False → (p1 → p1))))) ∨ False) ∧ p1)) ∧ p3) → False)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155030875633934019494780430516 : ((((((p1 ∨ (p2 ∧ p2)) ∨ (p3 ∧ (p5 ∨ p4))) ∨ p1) → False) ∨ (True ∨ ((True ∨ p3) ∧ p5))) ∧ (((p3 ∧ True) ∨ (p5 ∧ p1)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65787009223571871845575018263 : ((p4 ∨ ((p1 ∧ ((p2 → ((p5 ∨ False) ∨ (p4 → (p1 → p2)))) ∨ p1)) ∧ ((True → True) ∧ (((p2 → False) ∧ p2) ∧ (True ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310075811504791965627412649668 : (p2 ∨ ((p4 ∨ (((p2 ∧ (p1 ∧ ((True ∧ p2) → p3))) → (p3 → p3)) → (p4 ∧ p3))) → ((p5 ∧ ((False ∧ p1) ∨ p2)) ∨ (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 ∧ (p1 ∧ ((True ∧ p2) → p3))) → (p3 → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h4
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350233773965194446789752716333 : (p4 → (((p4 ∧ p5) → (p3 ∨ ((p5 → (p1 ∧ ((p5 ∨ (p3 ∨ ((((p3 ∨ p3) ∧ True) ∧ p2) ∨ p2))) ∧ (p2 → p1)))) ∧ p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247358649401838839607789319193 : ((False ∨ p1) ∨ ((((p4 ∧ True) → ((True → False) ∨ (p3 ∧ (True → p5)))) → (((p3 ∧ True) ∧ ((p1 ∧ p3) ∨ p4)) ∨ True)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624220035036379194163600555965 : ((((p3 ∨ ((((p4 → p1) → (p1 → (((False ∧ p4) ∨ ((p3 ∧ p1) ∨ p4)) ∧ ((p4 ∨ p3) ∨ (False ∨ p5))))) ∨ True) ∨ p5)) ∨ p5) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244206921356606325924943353624 : ((True ∧ p5) ∨ ((p2 ∨ ((((p5 ∧ p4) ∧ (True ∧ True)) ∧ p4) ∨ (p3 → (((p4 → False) ∧ True) ∨ p3)))) ∨ ((p1 → (p5 ∧ p3)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252570815335043017286429981585 : ((p5 → p3) ∨ (((((False → (p1 ∨ p5)) → False) ∧ p1) ∧ (p2 → (False → (((p1 ∨ False) ∧ p4) → (((False ∨ False) → True) → p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179023984724060348856859907320 : (((p1 ∨ p3) → ((p4 ∨ True) ∧ ((p4 ∨ p1) ∧ (False ∨ (p5 → p1))))) ∨ (((p3 ∨ False) ∧ (((p2 ∧ (True → p5)) ∧ p3) ∧ False)) → p1)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354041745636559734219492946248 : (p4 → (p4 → (((p5 ∧ p3) ∨ (((p3 ∨ p2) ∨ (p3 ∨ p4)) ∧ True)) ∧ (p4 ∧ (((True ∧ p3) ∧ False) → (((p4 → p3) ∨ p2) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37183694378770605644912829266 : (((((((True → p1) ∧ p4) ∧ (p1 ∧ (p4 ∨ (p3 ∧ p5)))) ∨ ((p3 ∧ (((p5 → p2) → (p1 ∧ p4)) → True)) → p3)) ∧ p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170030811416326670423494502698 : ((((p1 ∨ True) ∧ ((p1 ∨ p4) ∨ (p4 ∨ (p2 → p2)))) ∨ (p3 ∨ (p2 ∨ p3))) ∧ (p4 ∨ (True ∧ ((((p5 ∧ p4) → p3) → True) ∨ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254758084647861106238072691010 : ((p3 ∧ p4) → (((p1 → p2) → (((p1 ∨ ((p2 ∨ p1) ∨ (p2 ∨ p5))) → p1) ∧ (p3 ∧ (p5 ∧ (True ∧ ((p4 ∨ True) → p4)))))) ∨ p3)) := by
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
theorem thm_5_vars_228934734662026851778238263745 : ((p4 ∨ (p3 ∨ p5)) ∨ (True ∧ (((p5 ∨ False) → ((p4 ∧ (p1 ∧ False)) → ((True ∧ p5) → (False ∧ True)))) → (p4 ∨ (False ∨ (False → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_358747354097171771877073278595 : (p5 → (p5 → (p2 ∨ ((p4 ∨ p1) → (p3 ∨ (False ∨ (((p4 ∧ (p4 ∧ p5)) → (((p2 ∨ False) ∧ ((p1 ∨ p2) ∨ p2)) → True)) ∧ True))))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209495515335146699228209784901 : ((p3 → (p5 ∨ ((True ∧ p2) ∨ p3))) → (p2 → ((p2 → (((((p1 → p5) ∨ False) ∧ p4) ∧ True) ∧ (p2 ∨ (p5 ∧ False)))) ∨ (p2 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650180118557706461631616291771 : ((((((((p2 → (p1 ∧ False)) ∨ (p4 → (p3 ∨ ((p2 → True) ∧ False)))) → False) ∧ False) ∨ (((p5 → p4) ∨ True) ∨ p2)) ∧ (p4 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262449420557069434603545893752 : (True ∧ ((False ∨ (((((p3 ∧ True) → ((False ∧ (True ∨ ((p4 ∧ p2) ∧ p5))) ∨ (p4 → (p3 → p3)))) → p4) ∧ (True ∧ p2)) ∨ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158778825541377775015368298184 : ((p5 ∧ ((((False → (((((p1 ∧ False) ∨ p5) → False) ∨ p1) → p4)) ∧ (p4 → False)) → p1) ∧ False)) ∨ (p4 ∨ ((p5 ∨ p4) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_181358469314541369371703640668 : ((False ∨ ((True ∨ True) ∨ (((False ∧ (p1 ∧ (p5 ∧ False))) ∧ p4) ∧ p4))) → (p4 ∨ (((True ∧ ((p3 → True) → p1)) ∧ False) ∨ (p5 → True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210519895064152761523661824403 : (((p5 → (p2 → p2)) ∨ p4) ∧ ((((((p1 → p4) ∧ ((p1 → (p1 → (p5 → p1))) → p1)) ∨ False) ∧ p1) ∧ ((False ∨ p4) → True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134926782651986821790841119531 : ((((((p4 → False) ∨ ((((p1 → p1) ∨ p4) → p5) ∧ (True ∨ (p4 ∧ (False → p3))))) → p3) → p5) ∧ (False ∧ p2)) ∨ (p4 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46682577844660438694003363058 : (((p2 ∨ ((((((True → (True ∨ p2)) ∧ (p5 ∧ True)) ∧ p1) ∨ (p2 ∧ (True ∧ p3))) ∨ p5) ∧ ((False → p4) ∨ p3))) ∧ (p3 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671599506249349306207061734825 : ((((p5 → ((p4 ∨ True) ∧ (((((p5 ∨ (True → p4)) ∨ p2) ∨ p1) → p4) ∧ ((p4 ∧ p3) ∧ (p5 ∧ p4))))) ∨ ((p5 → False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736853767177673495746506947522 : ((((p2 → p4) ∧ ((((True ∧ (p1 ∨ (((False → p5) ∧ (p1 ∧ ((p4 ∨ p4) → (False ∨ False)))) ∨ (False ∧ p1)))) ∧ False) → p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61911310148835896138345677050 : ((p2 ∧ ((p3 ∧ ((p3 → p2) → (p1 ∨ (((p2 ∨ False) ∨ ((False ∧ ((p3 ∧ True) → p5)) → True)) ∨ p1)))) ∧ ((p5 → p2) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65088668029356702160135717725 : ((p2 ∨ (False ∨ (p5 → (((p1 → p2) → p4) ∨ (((((p1 ∧ (False ∨ True)) ∨ p5) ∨ p3) ∧ ((p1 ∨ p1) ∧ (False → p3))) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340048185117741714262158184216 : (p1 → (p2 → ((False → (((((p4 → True) ∧ (p3 → p4)) ∨ (p3 ∨ True)) ∧ (True ∧ p3)) ∧ p2)) → (p3 ∨ (((p4 ∨ p1) → p3) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179372701150623842370026256529 : ((p2 ∨ (p3 ∧ ((p4 ∧ ((p4 → (p1 ∧ p3)) → p5)) → (p2 ∧ p2)))) ∨ (True ∨ ((p2 ∧ (p5 → (p1 ∧ p1))) ∧ (p3 ∨ (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159376579383408613554417038461 : (((((False ∧ (p5 ∨ ((p2 → p3) → False))) ∨ (((True → p2) ∨ (p5 → p2)) ∧ p4)) ∨ p5) ∧ p3) → (((p3 ∨ (True ∨ p5)) → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (p3 ∨ (True ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : (p3 ∨ (True ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : (p3 ∨ (True ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h19
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346767893918563015197188440478 : (p3 → (((((p4 ∧ ((False ∨ p1) ∧ p3)) ∧ False) ∨ (((p2 ∨ p3) ∨ ((False → False) ∨ True)) ∧ True)) ∨ True) ∨ (p5 ∧ ((p2 ∧ True) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619840667823685657146672036001 : (((((p3 ∨ p4) ∧ (((p1 ∨ p3) → ((p5 ∨ ((p5 ∨ False) ∧ (False ∨ (p1 ∧ ((True → p4) ∧ False))))) ∨ (p3 → False))) ∧ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179141729847310926738652997940 : ((p1 ∧ (p3 ∨ ((p5 → (p1 ∧ False)) ∨ ((p3 ∨ (p4 ∨ p4)) → p3)))) ∨ (((p1 → (p5 → p5)) ∨ p3) ∨ ((p4 ∧ (p2 ∧ p1)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165869270020371064902257143487 : (((p2 → (True ∧ False)) ∨ (((((p3 → (p5 ∧ True)) ∧ (p2 ∨ False)) ∨ p5) → p4) ∨ p2)) ∨ (((p5 ∨ p2) ∨ p5) ∨ ((p1 ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156892667666726808680421989029 : ((((((p3 ∧ p5) ∨ False) ∧ ((p2 → p4) ∨ ((p2 → (p4 ∨ True)) ∨ (False ∨ p2)))) ∨ p1) ∨ p1) ∨ ((p5 → (p5 ∨ (p1 ∨ p1))) ∨ p3)) := by
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
theorem thm_5_vars_678630501999984412894333090724 : (((((p5 ∨ p1) ∧ ((p4 ∧ (p3 ∨ (False → (p2 → p3)))) → (p5 ∨ ((p5 → p2) ∨ (p3 → p5))))) ∨ ((p3 ∨ (p2 ∧ p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149567531667889784022863890875 : ((p2 ∧ (p3 ∧ (((p3 ∨ (((True → ((((p1 → p3) ∨ p5) → p1) → False)) ∧ False) → p4)) → p2) ∧ p5))) ∨ (p1 → (p1 ∨ (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43787630809899473514730320923 : ((((p3 ∨ ((p4 → ((((p5 ∨ p1) ∨ p5) → p4) ∧ (True ∨ (p2 ∧ (False ∨ (p5 ∨ (p1 ∨ (p4 → p3)))))))) ∧ p2)) → p4) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340774281711577182880692348851 : (p2 → ((((True → ((((p2 ∧ (p1 ∨ ((False ∨ False) ∧ ((p1 ∧ p1) ∧ p2)))) ∧ (p4 ∨ p2)) ∨ p1) → (p3 ∧ p4))) ∨ True) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64903366817152863299240410092 : ((p2 ∨ ((((False ∧ True) ∧ (p2 ∨ False)) ∨ ((((True ∨ p5) → (p4 ∧ (p1 → p1))) → p5) → p4)) ∧ (p2 ∨ (p4 ∨ (p4 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59095729291809785874144490645 : (((p5 ∧ p4) ∨ (False ∨ ((((p1 → (p1 ∧ ((p2 ∧ (p2 ∨ ((p3 ∧ False) → (p3 ∨ p1)))) → p5))) ∨ p1) → (p4 ∧ p2)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206478396947170278380065932766 : ((p5 ∨ ((p1 ∧ (False ∧ p1)) ∧ p3)) ∨ ((p2 ∧ True) ∨ ((((False ∧ False) → True) ∨ (p2 → (p1 ∧ ((p2 ∨ True) ∨ (p2 ∧ p3))))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_51556722711355512384543255180 : (((p5 ∧ (p3 ∨ (((((p1 ∧ True) → p5) ∧ (p1 ∨ p1)) ∧ (False ∨ (p5 → False))) ∨ p2))) → ((((False ∧ False) ∨ p4) ∨ True) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53264684798963626255924695610 : ((((p1 → p5) → (False ∨ (((False ∨ (p1 → p2)) ∧ p3) ∧ p4))) ∨ (False → ((((True ∧ p4) → (p1 ∧ p1)) → (True ∧ p3)) ∧ p5))) ∨ p4) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117743825231027324705610295691 : ((p4 ∧ ((True → ((p2 ∨ p1) ∨ ((p4 ∧ ((((p2 → False) ∨ p2) ∨ p1) ∨ p4)) ∧ ((True ∨ (p3 → p1)) → p2)))) ∧ p3)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45455042016071017133455799231 : (((True ∨ (False ∨ (True ∧ (p1 → (p2 → ((((p5 ∨ (p4 ∨ (p3 ∨ (p3 ∧ True)))) ∨ (p5 ∧ p3)) ∧ True) → (True → p4))))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109835179002297187956119138662 : ((p5 ∨ ((True → False) → ((p5 ∧ (p4 → (p1 ∨ True))) ∧ ((p5 ∧ p4) ∨ (p5 → ((p5 → (p5 → True)) ∧ (p1 ∧ p3))))))) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622219525850717377646161183372 : ((((p2 ∧ (p1 ∨ (((p5 ∧ p3) ∧ p4) ∧ (False → ((p1 ∧ ((p4 ∧ False) ∨ ((p2 → p4) ∨ (p5 ∧ (True ∨ p1))))) ∨ p4))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133863778408420017255988429488 : (((p2 ∧ ((((p2 → True) ∨ (False → False)) → (p5 ∧ p2)) ∧ ((p5 ∨ p4) → ((True → False) ∧ (False → p4))))) ∧ p5) ∨ ((False ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



