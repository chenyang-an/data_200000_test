variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149357692220990325985634536385 : (((p5 ∨ p1) → (True → ((p1 → p2) ∨ (False ∧ ((False ∧ (((False → p1) ∨ (False → False)) ∨ False)) ∧ p5))))) ∨ ((True ∨ (p3 ∨ p3)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150070881159237856550794448565 : ((True → (((p3 → p3) → (False → (p4 → False))) → (((p3 ∨ ((p4 → True) ∨ (True → p1))) → p3) ∧ p2))) ∨ (False ∨ ((p2 ∨ False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149994333175396585666907266058 : ((p4 ∨ (p5 ∨ (p3 → ((((True → True) ∨ p1) → ((p5 ∨ ((p3 ∨ (False → False)) ∧ p4)) → p5)) ∨ p2)))) ∨ (((p3 → True) ∨ p3) ∨ p5)) := by
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
theorem thm_5_vars_617703429641855651392409153322 : ((((((p1 → (False → p5)) → (p5 ∨ p5)) ∨ ((p1 → (p5 ∧ (((p4 ∧ p5) ∧ p4) ∧ (True ∨ p4)))) ∨ (True → (p2 → p3)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385680714764345756843457853245 : (((((((p3 → (p3 ∨ p1)) → False) ∨ ((False ∧ True) ∨ ((p3 → ((p5 ∨ p1) ∨ (p2 ∨ (p3 ∧ True)))) ∨ p3))) ∧ (p5 → p5)) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183910948939227439951386215956 : ((((p5 → p3) → (p2 ∧ (False ∨ (p5 ∨ (p3 → p4))))) ∧ p3) ∨ (((((p1 → ((p4 ∨ p5) → p2)) ∨ p2) → (p4 → False)) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48696721675784872582245529841 : ((((p5 → ((True ∨ (False ∧ (True ∨ p3))) → True)) → (False ∨ (p2 ∧ (True → ((False ∨ p3) ∧ (p4 ∨ p5)))))) ∧ (p2 ∨ (p2 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118223322151105606876912666195 : ((p1 ∨ (((True ∨ (True ∧ (True → p4))) ∧ ((((False ∧ p1) ∨ p2) ∨ p4) ∨ (p5 ∧ (((False ∨ p3) ∧ p1) ∨ p2)))) ∨ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206409411004784547127374459092 : ((p3 ∨ ((p4 → p5) → (p5 ∨ p3))) ∨ ((False → ((p2 → p2) ∨ False)) ∨ (((((p2 → (True → (p2 ∧ p5))) ∨ False) → p5) ∨ True) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646800270301957156995510235608 : ((((p2 → (((((p1 ∨ False) ∧ True) ∨ True) ∧ ((p4 ∧ p3) → ((p3 ∨ p3) → p2))) → (((p3 ∧ p3) ∧ p1) ∧ (p3 ∧ p2)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318844856346948405392962605968 : (p4 ∨ (((((p1 → (False ∧ p4)) ∨ ((p2 ∨ ((p1 ∨ p1) ∧ p5)) ∧ ((False ∧ (p5 → p4)) ∨ False))) ∨ p2) ∧ False) ∨ ((False → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328228916792956956441694917327 : (True → ((((True ∨ (((p3 → True) ∧ False) → (p4 ∧ p2))) → (((p5 ∧ p3) → p2) ∨ (True → p4))) ∨ True) ∧ (((p3 ∨ True) ∨ True) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629534190573389789017602541227 : ((((((((p1 ∧ (p3 ∧ p3)) ∨ ((p5 ∧ p3) ∨ ((((False ∧ p2) ∨ p1) → p3) ∨ True))) → (p5 ∨ p1)) → (True → p3)) ∨ p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98813638612209912662808480072 : ((True → ((((p5 ∨ (p3 → (p1 ∧ (False ∧ False)))) ∧ p4) → (p2 ∨ ((True → p2) → ((p5 → p4) → (p2 → (False ∧ p3)))))) ∧ p2)) → p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110861500619265064701453678889 : ((((((((p5 ∧ p2) → p1) → True) ∨ ((p4 ∨ ((p1 → ((p5 → True) ∧ (p3 → True))) → p2)) → p5)) ∨ p1) → p3) ∧ False) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111887229377378863169406797072 : ((((((((p5 → p5) → p3) ∨ False) → False) ∨ (p4 ∨ ((True ∧ p4) ∧ p1))) ∧ (p3 → ((p4 ∨ p5) ∧ (p5 ∧ p5)))) ∨ p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303875904985040232209275029915 : (p1 ∨ (((((p3 ∨ ((p3 ∨ (p5 ∧ (p2 ∧ p3))) ∨ p5)) ∨ True) ∧ (False → (p3 ∧ (p3 ∧ True)))) ∧ (p3 → (True ∨ (p5 ∨ p4)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68251735537973422598105595646 : ((p3 → ((((p4 → p4) ∧ (p1 ∨ (((p3 → (p1 ∧ (p1 ∧ p4))) ∧ (True ∧ ((p2 ∧ p3) ∨ p2))) → p4))) ∨ p2) ∧ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39973850836595376950122862345 : (((p4 → (p3 ∧ (p3 ∨ ((False ∨ (False ∨ p1)) ∧ (((((p3 → (p1 → False)) ∨ p1) ∧ (False → False)) → p2) ∧ (True ∧ p5)))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52246163768042203270774258754 : (((True ∨ ((p4 → ((((False ∧ p5) → p1) ∧ p2) → p3)) ∨ ((p1 ∧ p5) ∨ p2))) → ((p3 ∧ p2) ∧ ((p5 → p2) → (p1 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188729638856347170910884076531 : ((((False ∨ (False ∧ False)) ∨ (p3 → p1)) → (False → p3)) ∧ (((p4 → p5) ∨ (p4 ∨ ((((True → p2) ∨ p2) → p4) ∨ (p4 ∨ True)))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_137445322099975147707748794341 : ((p4 ∧ (((((True → True) ∨ p1) → (True ∧ True)) → p4) ∨ (p5 ∨ ((False ∨ (p5 ∨ (False ∨ False))) ∨ (p1 → p2))))) ∨ (p3 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196657768870899268865662395722 : (((((p2 ∧ p5) ∧ (False ∨ p2)) ∧ p1) ∧ True) ∨ (True → ((p4 ∨ (True ∧ (p3 → (((True ∨ (True ∨ p5)) → p2) ∧ False)))) → (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310112459183565614728258255838 : (p2 ∨ (((True → ((p5 → p4) → ((p5 ∧ ((p1 → p2) ∨ p5)) ∨ p3))) ∧ p5) ∨ (True ∨ (p1 → (True → (((p3 ∧ p5) ∧ p5) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157382587958112241859496869321 : ((((p1 ∨ (((False → p5) ∨ p3) ∧ (p1 → (p1 → ((p2 ∨ p2) ∨ True))))) ∧ p3) ∧ (True ∧ p3)) ∨ ((False ∧ (p3 → p1)) → (True ∨ p2))) := by
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
theorem thm_5_vars_311953638266575503020586702126 : (p2 ∨ (p3 ∨ ((p2 → ((p2 → p3) ∨ p3)) ∨ ((((p2 ∧ ((False ∨ p2) → False)) ∧ p3) ∧ p1) ∨ (False ∨ ((True ∧ p4) ∨ (p5 → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_262615487848517630568183141149 : (True ∧ (((((((p5 ∧ (p2 → (p1 ∨ ((p5 ∧ False) ∨ (p5 ∧ p4))))) ∨ p3) ∨ p1) ∨ (False → p1)) ∨ (p1 ∨ (p4 ∧ p4))) → False) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∧ (p2 → (p1 ∨ ((p5 ∧ False) ∨ (p5 ∧ p4))))) ∨ p3) ∨ p1) ∨ (False → p1)) ∨ (p1 ∨ (p4 ∧ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740394808650941634860194872998 : ((((p1 ∨ p3) ∨ ((p3 ∧ ((p5 ∧ True) ∨ (((((((p1 ∧ ((p3 → p1) ∨ p5)) → p5) → False) ∨ p3) ∨ p3) ∧ p1) ∨ p1))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104074676647402600818005747792 : (((p4 ∧ ((((p1 ∨ p2) ∨ ((p3 ∨ p1) ∧ True)) → ((p5 → (p1 → ((p2 ∧ p2) ∧ (False ∧ p1)))) ∨ True)) → False)) → p3) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∨ p2) ∨ ((p3 ∨ p1) ∧ True)) → ((p5 → (p1 → ((p2 ∧ p2) ∧ (False ∧ p1)))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h4
  -- False on the left can always be used.
  apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135866155325984924922535038092 : ((((p3 ∨ ((p2 ∧ ((p4 ∨ p5) ∨ False)) ∧ p4)) ∨ (p4 ∨ p1)) ∨ (p2 → (((p1 ∧ p5) ∧ p4) → (p2 → p4)))) ∨ ((p5 ∨ p4) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695074473100842306029184291196 : (((((p5 → ((((p5 → p2) ∨ p5) → (p5 ∧ (True ∧ True))) ∨ True)) ∧ p2) → ((((True ∧ (p2 ∨ p4)) → (False ∨ False)) ∨ p2) ∨ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53853146035201778065404452485 : ((((p5 ∨ (p2 ∨ False)) ∧ (p3 → ((p2 ∧ p3) ∨ True))) ∨ (p2 ∨ (p1 ∨ ((((p1 ∨ p1) ∧ p5) ∧ False) ∨ ((p1 ∨ p1) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60712044807214868963949640714 : ((True ∧ ((((True ∨ (p2 ∧ p2)) ∨ p1) → True) ∧ (p3 ∨ ((p5 → (((False ∧ (p5 ∨ True)) ∨ p4) ∧ p1)) ∨ (p3 ∨ (p2 → True)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766139726394138975358309149600 : (((p4 ∧ ((p4 ∧ p1) ∧ (p5 ∧ ((False → (((p3 → p5) → p5) ∧ (p1 ∨ (True ∧ (p5 ∧ True))))) → ((p1 → (p4 ∧ p2)) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15217865306415864044737312241 : (((p1 → (True ∧ ((p3 → ((True ∨ ((p5 ∨ (False ∧ ((p4 ∨ p3) → (p1 → p4)))) → (p4 → p5))) → p5)) ∧ p3))) ∨ (False → False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113876196148745064191664235637 : (((((p5 ∨ ((((p4 ∧ p5) ∨ p3) ∧ p1) ∨ p2)) → (p3 ∨ ((p2 → True) ∧ (False ∨ p4)))) ∧ p1) ∧ ((p4 ∧ p2) → True)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61880247359176251201999271924 : ((p2 ∧ ((((p2 ∧ p2) ∧ p2) → (((False ∧ (((p5 ∨ p4) ∧ True) → p4)) ∧ p4) ∧ ((p2 ∧ (p2 ∧ p1)) → True))) ∧ (p5 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165528000692883150370465360895 : (((p3 ∧ (p4 → ((p2 → ((p4 ∨ True) ∧ p5)) → p4))) → ((p5 ∨ (p5 → True)) → p4)) ∨ (((p1 → (p4 ∧ True)) → (p5 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262420019322864788773385671625 : (True ∧ ((p1 ∧ (p4 ∨ (p4 ∨ (((p4 → (((((p2 → (False ∨ False)) ∧ p2) → p4) ∨ p2) ∧ p5)) → ((p1 ∨ p4) ∧ p1)) ∧ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64048291695288940340746653180 : ((False ∨ (((p5 → (p3 ∨ p2)) ∨ ((p2 ∧ ((p1 ∧ (p4 ∧ (p3 ∨ (p4 ∧ (False ∨ False))))) ∨ True)) ∨ p3)) → (False ∨ (True ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643631450399906736994177806288 : ((((p4 ∧ (p2 → (True → ((p2 ∨ (True ∨ p5)) ∧ ((False → ((((p3 → (p3 → False)) ∧ p3) ∧ (p1 ∧ True)) ∨ p1)) → True))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147485075501795610891725421622 : (((p4 ∧ ((((((True → p1) → (p4 ∨ p1)) → (p2 → p3)) ∨ (p5 ∨ False)) → False) ∧ (p5 ∨ p2))) ∨ p5) ∨ ((False ∧ p1) → (p3 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639427908035064656885472896409 : (((((True → (p3 ∨ (p2 → p4))) → (((True ∧ (False ∨ (p1 ∧ p4))) → (p2 ∧ ((p3 → ((p3 ∨ True) ∧ p5)) ∨ p2))) → p5)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129311276807894158248228804811 : ((((p4 ∧ p3) ∧ (((((((p2 → p5) → (False ∨ p1)) ∨ p2) → p4) ∨ ((p3 ∧ p2) ∧ p2)) → p1) ∧ p1)) ∨ True) ∧ ((p4 ∨ True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157509427487985127871379022706 : (((p2 ∧ ((False → False) ∧ (((p2 ∧ p2) → False) ∧ ((False ∨ p3) ∨ (p2 ∧ True))))) ∨ (True ∧ p4)) ∨ (((False → (p3 ∧ True)) → False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p3 ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137944483188893898433913164882 : ((p5 ∨ (((False ∧ p5) ∧ (p1 ∧ ((((p2 → p3) ∨ (p1 → ((p3 ∧ False) ∧ True))) ∨ p3) ∧ (True ∨ p2)))) ∧ True)) ∨ ((True ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47111915943183356971160147617 : (((((((p4 → p3) ∨ ((((p5 → p2) → (True ∨ p3)) ∨ p1) → p4)) ∨ (p1 ∧ p5)) → False) ∨ (False → (p4 → False))) ∨ (True ∧ p1)) ∨ False) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89026781267474011049257748177 : ((((True → p3) ∧ p4) ∧ ((((p1 ∧ False) ∨ (p5 ∨ (p2 ∨ p1))) → (False → p2)) ∧ ((p4 → ((True ∧ (True ∨ p2)) ∧ p1)) ∨ p5))) → p3) := by
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
  cases h7
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110985127787337237970256011490 : (((((False → p5) ∧ (p4 ∧ (True ∨ ((True → ((p1 ∨ p3) ∨ p3)) → (p5 → (p2 ∨ (p4 ∧ False))))))) → (p4 ∧ p3)) ∧ True) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116950319175377641643479649692 : (((p2 ∧ p2) → ((((p4 → ((p2 ∨ (p2 ∧ p4)) ∧ False)) ∧ (p1 ∨ (p5 ∧ p5))) ∧ p5) ∨ (((p1 → False) → True) ∨ True))) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319682996338202409013193702279 : (p4 ∨ ((p4 ∧ ((p4 ∨ (p5 ∨ p3)) → (False → p1))) → (((((p2 → True) → p3) → p2) ∨ ((p4 ∨ (p2 ∧ (True → p2))) ∧ p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_769600262384770858767319352262 : (((p5 ∧ (p5 ∧ (p1 → ((p2 ∧ (((p4 → False) ∨ (p5 ∨ p3)) ∧ p5)) ∧ ((p1 ∧ (p1 ∨ p2)) ∧ (((p4 ∧ False) ∨ p2) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163532721400016953556637274810 : ((((p2 ∧ False) → True) → (((p5 ∧ (p2 → (p3 → p5))) ∨ (False ∨ True)) ∧ (False → p4))) ∧ (((p4 ∧ p5) ∨ p1) ∨ (True ∨ (p2 ∧ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733898315015823462095442177844 : ((((True ∨ True) ∧ ((((True → ((p3 ∨ (((p4 ∨ p3) → (p2 → True)) → (p5 → p3))) → p1)) → (False ∧ False)) ∧ (p1 → p4)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114940827917618184183453941824 : (((((True ∨ p3) → p1) ∧ (p4 ∧ ((p3 ∧ (p2 → p5)) ∧ (p2 → p3)))) → (p5 ∧ ((p4 ∧ ((p3 ∧ p1) → False)) ∧ p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234897202251856182139198426539 : ((True ∧ True) ∧ (((((p2 ∧ ((p3 ∨ p3) ∧ (p4 ∨ (((p2 ∨ True) ∧ p3) ∧ (p4 ∧ p5))))) ∧ (p2 ∨ p1)) ∨ p2) ∨ (p3 → p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172280908214735630425846754772 : (((p2 ∧ (True ∧ (False ∨ (True → (p1 ∨ p1))))) ∨ (p3 → (p1 ∨ (p1 → True)))) ∨ (p1 ∨ ((p2 → p3) ∨ ((p4 ∨ p1) ∨ (p1 ∧ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_42922450210761017873970177463 : (((p4 → (((((((False ∧ ((p5 ∧ p1) ∨ True)) → (((True ∧ (True ∨ p4)) ∧ p1) ∧ p4)) ∧ True) ∨ p4) → False) ∧ p2) ∨ True)) ∨ p4) ∨ p5) := by
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
theorem thm_5_vars_679831921069128130764741136703 : (((((False ∨ ((p4 → ((p5 → (((True → False) → p5) ∨ False)) ∨ (p1 ∧ p5))) → (p3 ∧ True))) ∨ p5) → ((p2 ∧ p3) ∧ (p1 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173714824394978269869083447641 : (((((((p5 ∨ ((p5 → p2) → p5)) ∧ p4) ∨ p1) ∨ p3) ∨ (p5 → p3)) ∨ p2) → (((p4 → p5) ∨ p5) ∨ ((True ∨ (False → True)) ∧ True))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Conjunctions on the left can always be decomposed.
          let h6 := h5.left
          let h7 := h5.right
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h8 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451894398988573044936880017276 : (((((((True → p3) ∧ True) ∧ True) ∨ ((((p5 ∧ ((p4 ∨ False) ∨ (p3 ∧ p5))) ∧ p2) ∨ p3) ∨ p5)) ∨ ((False ∧ p1) → (p5 → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323809053746172431324600567415 : (p5 ∨ ((p3 ∨ (((p1 → p3) ∨ (((p2 ∨ p5) ∧ ((p2 ∧ (p1 ∧ p3)) ∧ p1)) ∨ True)) ∨ True)) ∨ (((p1 ∨ p5) ∨ True) ∧ (p3 ∧ False)))) := by
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
theorem thm_5_vars_233630841517640082294935707709 : ((p2 ∨ (True ∨ True)) → (True ∧ ((((((((p4 ∨ p3) ∨ False) ∨ p1) ∨ False) → p4) ∨ True) ∨ (p1 → (p5 → p1))) ∧ ((p3 ∧ p4) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38416337329241876556185999848 : ((((((p5 → p4) ∨ p3) ∧ ((True ∧ p1) → (((p2 → True) ∧ p5) ∨ False))) ∧ (p1 ∧ ((((p1 ∨ p2) → False) ∧ p3) ∧ True))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303867253262876222892533303957 : (p1 ∨ (((True → (True → (((((((p3 → p5) → (p3 ∨ p5)) ∧ (True ∧ True)) ∧ p5) ∨ p2) ∧ p2) ∧ p3))) ∨ (p1 ∨ (True ∧ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_111000280351136058504258378642 : (((((p5 → (p2 ∨ p3)) ∨ ((((p4 → True) ∨ True) → ((p2 ∧ p5) ∨ (p5 → p5))) ∨ p5)) ∧ (p2 ∧ (p2 ∧ False))) ∧ p3) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608334175859678183936047068419 : ((((((((p4 ∨ p4) → False) ∨ (((p2 ∧ (p1 → False)) ∨ (p2 → ((p3 ∨ (p5 → p2)) ∨ (p3 ∧ True)))) ∧ p5)) ∨ p5) ∨ True) ∨ False) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_42734611406224032736736848154 : (((True → (((p1 → (p5 ∧ p1)) → ((((p1 ∧ (True ∨ p2)) ∨ (p5 → True)) → ((p3 ∨ p2) → p4)) ∨ False)) ∨ (p5 → p3))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608690300468608362577991144055 : (((((((p1 → (p2 ∧ ((p3 → (True → p1)) ∧ ((True ∧ True) ∧ ((p4 ∨ p4) ∨ (p1 → p4)))))) ∧ p2) → (p4 ∧ p3)) ∨ p1) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165928181965576161403653291727 : (((p3 ∧ p4) ∧ ((((p3 ∧ True) ∧ (p2 → ((p5 → (p3 ∨ p4)) ∨ p4))) ∧ p5) ∧ True)) ∨ (True ∨ (((p1 ∨ p5) ∨ False) → (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207738772114858741587076724739 : (((p5 ∧ ((p4 ∧ False) → p3)) → p1) → (((True ∧ p2) → (p1 → ((p3 ∨ False) ∨ (p1 ∧ ((p1 ∧ p3) ∨ (p1 → True)))))) ∨ (p5 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225197871577623568492038559509 : (((p4 ∧ p4) ∧ p1) ∨ (p1 ∨ (p4 ∨ (((p4 → (p3 → ((p4 ∨ p3) ∧ ((False ∨ ((p5 → False) → p3)) ∨ (p2 ∨ p5))))) ∨ p2) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702166551290439126112708567563 : ((((p5 → (p3 ∨ (((p4 ∨ p1) ∧ True) → (False ∨ p3)))) ∧ ((((p1 → ((p2 → p1) → p5)) ∧ ((p1 ∨ p5) ∨ True)) → p1) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41718443442670478761660422310 : (((((p4 ∨ (p3 ∨ p4)) ∧ p1) ∧ ((((p3 ∧ False) → False) ∧ (True ∧ (p4 ∧ (True ∧ p3)))) ∧ ((p1 → (p3 ∧ p2)) → True))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68176698807042601740793842845 : ((p3 → ((((p3 ∨ (p1 ∧ (False → (p5 → (p1 ∧ (p2 ∧ (p4 ∧ p3))))))) → (True ∧ ((p4 ∧ (p3 ∨ True)) ∧ p4))) ∨ p3) ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136352703185709448573183170760 : (((p2 → (True → (p3 ∧ p5))) ∧ ((((False ∨ p1) ∨ (p3 → ((p2 ∨ p4) ∨ p3))) ∧ p2) ∧ (p4 ∨ (False → p5)))) ∨ (True ∨ (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752943599804511563650996195318 : (((False ∧ (((((((p5 ∨ (True ∧ False)) ∨ ((p4 → False) ∨ p5)) → p1) ∨ (p5 ∨ ((p3 → True) ∨ p1))) → p3) → (p1 ∨ p3)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662995554962710751384002333444 : ((((((p2 → False) ∨ True) → (p4 → (p2 ∧ (p4 ∨ (p4 ∧ (p5 → ((True ∧ (p1 ∧ ((p4 → p3) ∨ p5))) ∧ p5))))))) → (p3 → p3)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163304396781825636035084828642 : ((((p5 → (False ∨ p3)) → (p3 ∧ False)) ∨ (p5 ∨ (True ∨ (p2 → ((p5 ∨ p1) ∧ True))))) ∧ ((p1 ∧ True) → ((p1 ∧ (p1 ∨ p2)) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755449008898881180022561695714 : (((p1 ∧ ((((False ∨ p3) → False) → ((p4 ∧ (False ∨ ((p2 ∧ (((False ∨ False) ∨ ((True ∧ p4) → p5)) → True)) ∨ False))) ∧ p4)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38693335476858236202467267822 : ((((((p4 ∧ True) ∨ (False ∨ p4)) ∨ p3) ∨ ((p3 ∨ (((((p4 → (True ∧ True)) → False) ∨ p1) ∧ p2) ∧ p2)) ∨ (p4 ∧ False))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_796657827735388162106343949 : ((True ∧ (((((True ∧ p1) → p5) ∨ p5) ∧ (p1 → p4)) → (False ∨ (((p5 ∨ (True ∧ (p5 ∧ p2))) ∧ (p3 → p3)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304117962524711337772999261361 : (p1 ∨ ((p3 → (p5 → (((((p1 → (p3 → p3)) ∧ (((((p3 ∧ p4) ∧ p5) ∨ (True ∧ False)) ∧ p4) ∧ p4)) → False) ∧ True) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141553397681239491745856768423 : (((p1 ∨ (p2 → p4)) ∨ ((p2 ∨ (((p4 ∧ (((p3 ∧ (False ∧ p2)) ∧ p1) ∨ p2)) ∧ (p2 ∨ p4)) → True)) ∧ p2)) → ((p1 → p5) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
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
theorem thm_5_vars_798694338355823918753920340522 : (((p1 → (((p2 ∨ (p3 ∨ False)) ∧ p1) → ((True ∧ (False ∧ ((((p4 ∨ True) ∧ ((p2 ∨ False) ∨ p1)) → (p2 ∧ p5)) ∧ p4))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344651748036736638063543461144 : (p2 → (p2 → (((((True ∧ (p1 → (((p1 ∨ (p2 ∨ p1)) ∨ True) → p1))) ∨ True) ∨ p2) → (((p4 → p3) → (p4 → p3)) → p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161491081903328003638737093327 : ((p4 ∧ ((True → (((True → (p4 ∧ ((p5 ∨ p5) ∧ p2))) → p3) ∨ (p2 ∧ (p5 → p2)))) ∧ True)) → (p2 → ((p4 ∧ (p3 ∨ False)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345481967249381997577257629450 : (p3 → ((((((p1 → False) → (p3 ∧ (p1 ∨ (((p4 ∨ p3) ∨ (p3 ∨ p5)) ∧ p2)))) → p5) ∨ p4) ∧ ((p5 → (True → p3)) ∧ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149189225996106274587945246039 : (((p2 → p2) ∧ (p4 ∨ (True ∧ ((p5 ∨ (p1 ∨ False)) ∨ ((p4 → p4) ∧ (False ∨ (p2 → (True → p1)))))))) ∨ ((False ∧ (p2 → True)) → p2)) := by
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
theorem thm_5_vars_55239534851232520548934976739 : ((((p1 ∧ p4) ∧ ((p3 ∨ p2) ∧ True)) ∨ (((True → (p1 ∨ False)) → (True → ((p5 ∨ (p1 → p5)) ∨ True))) → (p5 ∨ (p2 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59074864665785833716925820801 : (((p5 ∧ p1) ∨ ((((p2 ∨ p3) ∧ (((False → p4) → (p2 → ((p4 ∨ p1) → False))) → (p4 ∨ ((p2 → p5) ∧ p2)))) → p5) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166489855269923089929286100829 : ((p3 ∨ (((p3 → True) → False) ∨ ((True ∧ ((p2 → p3) ∨ ((True ∧ p3) → p2))) ∧ p3))) ∨ (False → ((True ∨ p1) → (p3 ∨ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66362730200075646038528254736 : ((p5 ∨ (False ∨ (p2 ∧ (p4 ∧ ((p1 ∧ ((True ∧ (((p1 ∨ p5) → False) ∧ p1)) ∨ p1)) ∨ (p4 → (((p3 → False) ∧ p1) ∧ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65566833787841051234267508745 : ((p3 ∨ (p3 → (((p1 → (False → (p3 ∧ (False ∧ (p2 ∨ (p5 ∨ p5)))))) ∧ ((p1 ∨ p2) → False)) → ((p3 → False) ∨ (p2 → p1))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48204659500314086155449822045 : ((((p3 ∧ p4) → ((((p2 → ((True ∨ True) ∨ p2)) ∧ ((False → False) ∨ p3)) → (p4 ∨ ((False ∧ p5) → False))) → False)) → (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107954670642536386792111997773 : (((p3 → False) ∨ (p5 → (((p4 ∧ (p3 ∧ (p2 ∧ p4))) ∨ ((p3 ∧ True) → (p4 ∧ ((p1 ∨ p2) ∨ (True ∨ p2))))) ∨ p5))) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52047623778418374783507746985 : (((p1 → ((((p5 → p1) ∨ p3) ∧ (p2 ∨ (p2 ∨ True))) → ((p5 ∨ p5) ∨ p4))) ∨ (p4 ∨ (True ∧ ((p1 → (p5 → p5)) ∨ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164437655056648697856247921099 : ((p5 → (True → ((p4 → (p4 ∧ p2)) → (p1 ∨ ((p3 → False) ∨ ((p5 ∨ p4) ∧ True)))))) ∧ (True ∧ (((p2 ∧ (p2 ∨ p3)) ∨ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356446967926929084185607138673 : (p5 → (((p1 ∧ p1) ∧ (False ∨ ((p3 ∨ False) ∧ (p1 → (p1 → p2))))) ∨ ((p3 ∧ (p4 → True)) ∨ ((p5 → ((p1 ∨ p5) ∧ p2)) → True)))) := by
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
theorem thm_5_vars_110764384560025328997768553166 : ((((p4 ∨ ((True → p2) → (p4 ∨ ((p1 → p3) ∨ ((p1 ∨ p2) ∧ ((True → (p1 → (p2 ∧ p3))) ∧ False)))))) ∧ p4) ∧ p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



