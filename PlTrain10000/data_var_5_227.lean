variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319818853083859143393982623941 : (p4 ∨ (((False ∧ (p1 ∧ True)) → True) ∧ (((p3 ∧ p5) ∧ p3) → (((((p1 → ((p3 ∨ (p4 ∧ False)) ∧ False)) ∧ False) ∨ p4) ∨ p4) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47101041155936456463728789705 : ((((((((p4 → (p5 ∨ p4)) ∨ (p5 → p4)) → ((p4 ∨ False) ∧ p1)) → p3) → (p4 ∧ p5)) ∧ (p4 ∨ (p4 ∨ False))) ∨ (p2 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350214776506254132212203640724 : (p4 → (((p3 ∨ p4) ∧ ((((p2 ∧ ((p3 → p2) ∧ (p5 → p1))) → False) ∧ False) ∨ (True ∨ (p2 ∨ (p3 ∨ (p3 → (True → p3))))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165751661046747572007022123082 : (((p2 ∧ ((p4 → p3) ∨ p2)) ∨ (((p3 ∧ ((p5 ∨ p5) ∨ True)) ∨ (p1 ∨ p1)) ∧ True)) ∨ (True ∨ (p2 ∨ ((p5 → p4) ∧ (p2 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731826063754137334364927569129 : ((((p4 → (p3 ∧ False)) → (((p2 ∨ (p5 → p3)) → True) → (False ∨ (p5 → ((((p1 ∨ (p2 → False)) ∧ True) ∧ p3) ∨ (False → p5)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338245434058764884611928444525 : (p1 → ((False ∧ ((p1 ∧ (p5 → p4)) → p1)) ∨ (p5 → (((p1 → (p4 ∧ (False ∧ ((p4 ∧ p3) ∨ p2)))) → ((p3 ∨ False) ∨ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49155054419118861488922556161 : ((((p5 ∨ ((p2 ∧ (False → p5)) ∨ (p3 → p5))) ∨ ((p3 ∨ (p2 → False)) ∨ (p3 ∨ ((p5 → False) ∨ True)))) ∨ ((p1 ∧ True) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60923899082867544122824607910 : ((False ∧ ((((p4 → p3) → ((p4 ∧ (False → p2)) ∧ ((False ∨ False) ∧ p1))) ∨ (False → (p1 ∧ (True ∧ (False → (p3 ∨ False)))))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731860376107011669065456098701 : ((((p4 → (p5 ∨ p2)) → (p3 → (((True → (((((p3 → ((p5 ∧ p1) ∧ p4)) ∨ True) ∨ True) ∧ p2) ∨ p4)) → (p5 ∧ True)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200708513196902152848074034513 : ((p2 ∧ (p3 ∧ ((p1 ∧ p2) → (p5 ∨ p3)))) → (p4 → (((p3 → p1) ∧ False) ∨ ((p1 ∧ ((p1 → (p1 → (p1 → True))) ∨ False)) → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191322239884612531474660356816 : (((p1 ∧ True) ∨ ((p4 → (p3 ∨ p3)) ∧ (p2 ∨ p4))) ∨ ((((p2 → True) ∨ (p1 → (p2 → (p2 ∨ p4)))) ∧ p1) → ((True ∧ False) → p3))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56151574128052258819882148251 : ((((p4 → True) → (True ∧ p5)) ∨ (((p3 → p3) ∧ (p5 ∨ ((p3 ∧ (p1 ∨ p1)) ∧ ((p4 ∨ p1) ∨ (p1 → True))))) → (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22131873439275245011053600843 : ((((p2 → ((p4 ∧ True) → p3)) → (True → False)) ∨ ((p4 ∨ True) ∨ (((p1 ∨ False) ∨ False) ∧ (((p4 → (p2 ∨ p1)) ∨ p4) → p2)))) ∧ True) := by
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
theorem thm_5_vars_33822913381307102112615993410 : ((p5 ∨ ((p5 ∧ (((p2 ∨ p3) ∨ False) → (p4 ∧ (((True → (p4 ∧ (p4 ∧ False))) ∧ p5) ∨ p1)))) ∨ ((True ∨ p5) → (p4 → True)))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58716175282470958587487831623 : (((p3 → False) ∧ ((False ∨ (((p5 ∨ (True ∨ ((p5 ∧ False) ∧ False))) → p2) ∨ ((p4 ∧ (True ∨ (p4 ∧ True))) ∧ p3))) ∨ (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66504678872555541682635261944 : ((True → ((p2 ∨ ((((p2 → p3) ∧ (p2 → True)) ∨ ((p4 → (p1 → (p3 ∧ p5))) ∧ p4)) → (((False ∨ p2) → False) ∨ p5))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158196650887432855956795897188 : ((((p2 ∨ p3) ∧ p3) ∧ (p2 ∧ (((p5 ∧ ((p1 ∧ True) ∨ p1)) ∨ (p4 ∨ (p2 ∧ False))) ∨ p1))) ∨ ((True ∨ True) ∨ ((p4 → True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58787607091973291795256775705 : (((p5 → True) ∧ (((((False ∨ ((p4 → ((p3 ∧ (True ∧ p5)) ∨ False)) ∨ True)) ∧ ((p1 → False) → p1)) ∧ p4) → (True ∧ False)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170408969097242444380887375270 : ((((False ∧ p1) → p1) ∨ (((p3 ∧ (p5 ∧ (p1 ∧ (True ∨ p2)))) ∧ p1) ∨ True)) ∧ ((p4 ∨ ((p2 ∧ False) ∨ p5)) ∨ ((p4 ∨ True) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178352714786839240530899079426 : (((False ∨ ((p2 ∨ (p4 ∨ ((p4 ∧ p5) → p2))) ∨ p5)) ∨ (p4 ∨ p2)) ∨ ((False → p5) ∨ (p4 → ((p3 ∨ (p1 ∨ p2)) ∨ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216042362777076713981797754311 : ((p5 ∨ ((p4 → True) → False)) ∨ (p3 ∨ ((((p2 ∧ True) → (p1 ∧ ((False ∨ False) ∧ p1))) → p1) ∨ (p2 ∨ ((p1 → True) ∨ (p5 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184312857338685154069555750604 : ((((p3 ∨ p1) ∧ ((p1 ∨ (p2 ∨ p5)) → (p3 ∨ p2))) → p5) ∨ (p1 ∨ ((p2 ∨ ((p5 → p3) ∨ ((p5 ∧ p1) ∧ p5))) → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181410057616150253492065912021 : ((p2 ∨ ((p4 ∨ (False → (((p3 → False) ∨ p3) ∨ p5))) → (True → False))) → ((((((p1 ∨ p4) ∨ p3) → (p4 ∨ p4)) → p3) ∧ True) ∨ True)) := by
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
theorem thm_5_vars_739249694509403430863217669472 : ((((p4 ∧ p2) ∨ ((p4 ∧ (False ∧ ((p3 ∧ ((p1 ∧ (p1 → (p5 ∧ p4))) ∧ p1)) ∨ (True ∨ ((True ∨ p1) → (p5 → p1)))))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164446367141501759313338306130 : ((((((True ∨ p3) ∧ (p3 ∧ ((p1 → p3) → (False → (p4 ∨ p4))))) → p1) ∧ p4) ∧ p5) ∨ (True ∨ (p1 ∧ (p3 → ((p2 ∨ p1) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172183758023194345828646407251 : (((p4 ∨ (((True → p1) → (p4 → (p3 ∨ p3))) ∨ p3)) ∨ (True ∨ (p2 → p4))) ∨ (True ∨ (p2 ∨ (((p5 → (False ∧ p2)) → p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60207738374904252037227835450 : (((True → True) → ((p1 → ((p3 → p5) ∧ p3)) ∨ (p4 → (((p3 ∨ (p5 → (False → p5))) → ((p3 ∧ p3) → (p1 → False))) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191039508288693956942579591399 : (((((p5 → p4) ∨ p1) → p2) → (False ∧ (p3 ∨ p5))) ∨ ((((p3 ∨ p1) ∨ False) ∨ ((p4 ∧ (p1 ∧ p4)) ∨ (False → (True ∧ True)))) ∨ False)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66714012783758979610617611945 : ((True → ((p1 → p1) ∧ (((p1 ∧ ((True → ((False ∧ True) → (p2 → (False ∧ (True ∧ (p3 → False)))))) → False)) ∨ (p5 ∧ p1)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135549492139366093508960159938 : ((((p1 ∨ p1) ∧ (p4 → ((False → (p2 ∧ p4)) ∧ (((p1 → p2) ∧ p3) ∨ p5)))) ∧ (p1 ∧ ((True ∧ p1) → False))) ∨ (False → (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264853591747456615759574386584 : (True ∧ ((p4 ∨ p2) ∨ ((True ∨ p5) ∧ (((p2 ∨ p4) ∧ p4) ∨ ((p4 ∧ ((True → p3) ∧ p4)) ∨ (((p4 ∧ p4) ∧ (p1 → p3)) → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225549507880706062874185786263 : (((True → p3) ∧ p5) ∨ (((p2 ∧ p4) ∨ (True → p4)) → ((((False ∧ ((p5 ∧ p2) ∧ (p5 ∨ False))) ∧ True) ∨ (True → False)) ∨ (p2 → p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68176076071695026938809771809 : ((p3 → ((((p1 ∧ (((p5 ∧ (False → p1)) ∧ (p5 ∧ (p4 ∨ (((p3 ∨ p2) ∨ p2) → False)))) ∨ True)) ∧ (False → True)) ∨ True) ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609319612618068742909089668573 : ((((((p1 → p1) ∧ ((p2 → ((False ∧ (((p5 → (True ∧ p4)) ∧ p1) ∨ p2)) ∧ p2)) ∧ (False ∨ ((p5 ∨ False) ∧ False)))) ∨ True) ∨ p1) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_342195169746267673153837147680 : (p2 → (((((((p1 → p4) ∨ True) ∧ ((p5 ∧ p4) ∧ ((p4 → p4) ∧ p2))) ∨ p5) ∨ (p4 → True)) → p1) → ((p5 → (p3 ∧ p4)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((p1 → p4) ∨ True) ∧ ((p5 ∧ p4) ∧ ((p4 → p4) ∧ p2))) ∨ p5) ∨ (p4 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643288386055335229215729548 : (((p4 ∨ ((((p1 → p3) ∧ (False ∨ p2)) ∧ (p1 ∨ ((False ∧ (True ∨ (p3 → p3))) → p5))) → p3)) ∧ ((p1 ∨ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191462868050441514492913113507 : (((p5 → True) → ((p4 → ((p3 ∧ p3) ∧ False)) → p4)) ∨ ((p2 ∧ p2) → (((p1 ∧ p1) ∨ p3) ∨ (p1 ∨ ((p5 ∨ p2) ∨ (False → p4)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51904153591285169762934453270 : ((((((p4 ∧ False) ∨ ((p5 ∨ (p4 ∨ p5)) ∧ p3)) ∨ (p3 → p4)) ∧ (False ∧ p2)) ∨ ((p1 → (p2 ∨ ((True ∧ True) ∨ True))) ∨ p2)) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722960500116449374202951732778 : (((((p5 ∧ p5) ∨ True) ∧ ((((p3 ∧ (p5 ∨ False)) ∧ p1) ∧ ((((True ∧ (p1 ∨ (True ∨ True))) → p3) → (p4 ∧ p4)) ∧ p3)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112490091526764448595486955780 : ((((False ∨ (((((p3 → True) ∨ p2) ∧ ((False ∧ False) → p1)) → (p2 → ((p1 ∨ p3) ∧ (p4 ∧ True)))) → False)) ∨ False) → p5) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117410490005689526306201625028 : ((p1 ∧ ((True ∨ (((p3 ∨ (((p5 ∨ (((p5 → ((p3 → True) ∧ True)) → p4) ∧ p3)) → p5) ∧ p2)) ∨ p3) ∨ p5)) → p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656871096462172991324265417462 : (((((p3 ∨ (True ∨ (p5 ∨ p2))) ∧ (((((False ∧ p2) → p4) ∧ (p3 → ((p4 ∧ (p4 ∨ p4)) → False))) ∧ p3) → p1)) ∨ (p5 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147056505624686026115444015572 : ((((((((p5 → False) ∨ (p3 → p5)) → p4) → p3) ∨ p4) → ((p2 ∨ (p2 ∧ p4)) ∨ (p1 ∧ p3))) ∧ p4) ∨ (True ∨ (p5 ∧ (p3 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46751653099757933473288968077 : (((p1 → ((p3 ∨ (True ∧ True)) → ((p4 ∧ False) ∧ (p1 → (((p3 ∧ (False ∧ p5)) ∨ p1) ∧ ((False → p5) ∨ p4)))))) ∧ (p4 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252143280961817741635918794695 : ((p4 → p3) ∨ (((((p5 ∨ ((((((False ∨ p3) ∧ False) ∨ p1) ∨ p3) → ((p4 ∨ False) ∧ p2)) ∧ p5)) ∧ (False → p4)) ∨ True) ∨ p3) ∨ False)) := by
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
theorem thm_5_vars_49318924668234137614819758170 : (((p3 ∨ (((p2 ∨ (p2 ∧ (p1 ∨ True))) ∧ (p2 ∧ ((p3 → (p2 ∧ False)) ∧ False))) ∨ ((p1 → p1) ∧ True))) ∨ (p3 ∧ (p3 ∧ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316688104628768797640306376537 : (p3 ∨ (p5 ∨ (((((p1 ∨ p1) ∧ p4) → (p5 ∧ (((p5 ∧ (p3 → p5)) ∨ False) → p2))) ∨ (False ∧ p1)) → (((p2 ∧ p1) ∨ p2) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42297679093640431771846853896 : (((p2 ∧ ((((False ∨ ((p4 ∨ ((p5 ∧ (p4 ∨ p1)) ∧ p1)) ∨ (p1 ∧ p5))) → (True ∧ True)) ∨ (p2 → (p2 → p1))) → p5)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783328335023420012085742976010 : (((p3 ∨ (((p1 ∧ p3) ∨ ((p1 → ((True ∨ (False ∧ True)) ∨ (((p2 → p4) ∨ True) ∧ p2))) ∧ p5)) → ((p1 ∨ True) ∧ (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142547370946927962356022342948 : ((True ∨ ((False ∧ p3) ∨ (((p3 ∧ ((((p1 ∨ ((p4 ∧ (p4 ∧ True)) → p5)) ∧ False) → p5) ∨ p4)) → False) ∨ p5))) → ((p4 → p3) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
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
theorem thm_5_vars_196939978694526631080990695282 : (((((False ∧ (p5 → p2)) ∧ p5) ∨ p5) ∨ p1) ∨ (p1 ∨ ((True ∨ p4) ∧ (p5 ∨ ((((p1 ∧ p3) ∧ True) ∧ False) → (True ∨ (True ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254223605305484384290363547980 : ((p2 ∧ p2) → (((((p4 ∨ False) ∧ p1) ∨ (((p4 ∧ (p1 ∧ False)) → p1) ∧ (False ∧ ((p2 ∨ True) ∧ p1)))) ∨ True) ∧ (True ∨ (False ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148964041634798503597143195184 : ((((True → p2) ∨ False) ∧ (((((p3 → p1) ∨ p5) → False) ∨ ((p5 → (True → (True ∨ True))) ∧ p1)) → p3)) ∨ ((p4 ∨ True) ∧ (p4 → p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321201388536910093701738682125 : (p4 ∨ (p3 ∨ (((p4 ∨ True) ∧ p4) ∨ ((p4 → ((p5 ∧ (p2 ∨ (((p4 ∨ p3) → p2) ∧ (False → True)))) → (p4 → (p5 → p2)))) ∨ True)))) := by
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
theorem thm_5_vars_142665489986602195554341474235 : ((p1 ∨ ((p3 ∧ (p2 ∨ ((((p1 → p4) → (p3 → False)) → p5) ∧ p2))) ∧ (p2 → (((p2 ∧ p2) ∧ p5) ∨ False)))) → ((p4 ∨ p1) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51306420765527595554173053716 : (((p2 ∨ (((((p4 → (True → p2)) → p1) ∧ ((False → (False → False)) → p1)) ∧ p3) ∧ p5)) ∨ ((True ∨ ((p1 ∧ False) ∧ p3)) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166308956800378221603953342722 : ((p5 ∧ (((False ∧ (p3 → (((True ∨ (True → (p4 → False))) → False) ∨ p5))) ∨ p2) ∧ p1)) ∨ (False → (((p3 → p1) ∧ (False → p2)) → p5))) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115449246028919861314957201008 : ((((p1 ∨ (p5 → p1)) ∨ (p2 ∨ (p5 ∧ p4))) ∨ (p2 → (p2 ∨ (((True ∨ (((p2 ∧ p1) → False) ∧ p2)) → p2) → p5)))) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313376425814495673382687316370 : (p3 ∨ (((((((p3 → ((p5 → (p2 ∧ True)) ∧ (True ∨ p3))) → (True ∧ (p4 → (p2 → p2)))) → False) ∧ (p4 ∨ p1)) ∧ p4) ∧ p4) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 → ((p5 → (p2 ∧ True)) ∧ (True ∨ p3))) → (True ∧ (p4 → (p2 → p2)))) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h9
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186711793966374773199572161134 : (((((p3 ∨ p4) → p2) → (p1 ∧ p1)) ∨ (p2 ∨ (p2 ∧ True))) → ((True → p4) ∨ ((p4 → True) ∨ (((p3 ∧ (p4 → p5)) ∨ p5) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785980507136761754924261450190 : (((p4 ∨ (((False ∧ (p4 ∧ (p5 → p2))) ∨ ((((((p1 ∨ p1) → (True ∧ (p2 ∨ True))) ∧ p1) ∨ p3) ∧ True) ∧ False)) ∨ (p1 ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_184236741877217843920279984069 : (((((p3 ∧ (p1 → ((p3 ∨ p3) ∨ p4))) ∨ p4) → p4) → p5) ∨ (p2 → ((p2 ∧ (True → (p2 ∨ ((False ∨ p3) ∧ (p1 ∨ p2))))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64184220914103752603719518486 : ((False ∨ ((True → True) → (((((((p2 ∨ (p3 → p2)) ∧ p4) → False) ∨ False) ∧ (((p4 ∨ False) → p3) ∨ False)) ∧ p2) ∧ (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60545936342548927170973888229 : ((True ∧ (((p5 ∧ p2) ∨ ((((p1 ∨ p3) ∧ p1) ∧ p5) ∧ (p1 ∧ ((p2 → p3) → (((True → (p3 ∨ p1)) ∧ True) ∧ p1))))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314946832823782500281748653222 : (p3 ∨ (((p4 → (((p3 ∧ p5) → (p3 ∧ False)) ∨ p4)) ∨ p4) → (False ∨ ((((p2 ∨ (p4 → p5)) → True) → (True ∧ False)) → (p2 ∨ p5))))) := by
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
    have h4 : ((p2 ∨ (p4 → p5)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p2 ∨ (p4 → p5)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257684594426712724532348795333 : ((p3 ∨ p3) → (((p1 ∨ p3) → (((True ∨ ((p4 ∨ p2) ∧ (p4 ∨ p3))) ∨ False) ∧ (((False ∧ False) → (p4 → p4)) → p2))) → (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∧ False) → (p4 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p1 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : ((False ∧ False) → (p4 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- False on the left can always be used.
      apply False.elim h20
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h22 := h16 h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654483142942454777074104316349 : ((((((p3 ∨ p5) → ((p4 ∧ (((p1 ∨ p3) → (p1 ∨ p5)) ∨ (((True ∨ p1) ∨ p2) ∨ p1))) ∨ (p4 → True))) ∨ p2) ∨ (p5 → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56408313474221663115516439733 : ((((True → (p5 ∧ True)) → p2) → (p5 ∨ (((p5 ∨ p1) ∨ ((p4 ∨ ((((p2 → p1) ∧ False) ∧ True) → False)) ∨ p1)) ∧ (p5 → p2)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (True → (p5 ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59911750606056345660987416412 : (((p5 ∧ p2) → (p1 → (p2 → (p2 ∧ (p3 ∨ (((p5 ∨ (p3 ∧ False)) → ((True ∧ (True → (False → (p5 ∧ True)))) → p3)) ∨ True)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62586597935437700708208310203 : ((p3 ∧ (p2 → ((True ∧ (True → False)) → ((True → (True ∧ ((((p3 → (p5 → p4)) ∧ p5) ∨ ((p4 ∧ p4) → p3)) ∨ p5))) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49595255599555857326090941881 : ((((((p2 → ((p3 ∨ p1) ∨ p2)) ∨ True) ∧ (p1 ∨ (p3 ∧ p5))) → (((p2 ∨ (True → True)) ∨ p3) ∧ p5)) → ((p2 → p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340848751164028450403190636604 : (p2 → (((((((p5 → (p3 ∧ True)) → (p2 ∧ False)) ∧ p4) ∨ p2) ∧ ((True ∧ True) → ((False ∨ p1) → True))) ∨ ((p2 → p5) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_831982138401214797191265336 : ((p5 ∧ (p5 ∧ (p2 → (((False ∧ p1) ∧ (p5 ∨ ((False → (p5 ∧ True)) ∨ ((p2 → ((p2 ∨ p3) ∧ p2)) ∨ True)))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147296000869311758827303840083 : (((((p1 → ((((p5 → p1) ∨ (((p4 → (False → True)) ∨ False) ∧ p3)) ∧ True) ∧ p3)) ∨ p4) → p1) ∨ p5) ∨ (True ∨ (p5 ∧ (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620154830362717174819069127009 : (((((p1 ∧ p5) ∨ (((p3 ∧ (p1 ∧ p4)) ∨ p3) → (((False ∧ ((p1 ∧ p3) → (p4 → p3))) ∨ p3) ∧ ((p3 ∨ p4) → p5)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165080654214443981064515138220 : (((True ∨ (p2 → (((p5 → (False ∧ p5)) ∨ (p4 ∧ ((p5 → p2) ∧ p3))) → False))) → p4) ∨ (((((p4 → p4) → False) ∧ False) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110926862481069899211833372242 : ((((p5 → (((p1 ∨ True) ∧ p3) ∧ (p1 → ((((((p4 → p5) ∧ p2) → p1) ∧ p3) → (p5 ∨ p1)) → p5)))) → p5) ∧ p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65244356682516798664348394854 : ((p3 ∨ ((((p2 ∧ ((p5 ∨ p3) → p5)) ∨ (((((True → (p2 → p4)) ∧ p5) ∨ (p1 → (True → p3))) → p4) ∨ p2)) → p4) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49208706275501882789199670747 : ((((p2 ∨ (p1 ∧ p1)) → (((p5 ∨ (p3 → False)) ∨ ((True ∧ ((p1 → p5) → False)) ∧ p4)) ∨ (False → p4))) ∨ (False → (False ∧ p5))) ∨ p1) := by
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
theorem thm_5_vars_357461552993740860882794492759 : (p5 → ((p2 → p3) → ((p4 → p5) ∧ (((((p2 → p2) → False) ∨ (p2 ∧ p3)) ∨ p2) ∨ ((p5 ∨ True) ∨ ((p4 ∧ p2) → (p4 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179332203471415409392307133232 : ((p1 ∨ ((p5 → (((p1 ∨ p1) ∨ p1) ∧ (p1 ∧ p5))) ∨ (p3 ∨ True))) ∨ ((((p5 ∨ ((False ∧ p2) ∨ p1)) ∧ (True ∨ p4)) ∨ p3) ∧ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136586978662682176523746674354 : (((p5 ∧ (True ∧ False)) ∨ (((p2 ∧ (((p1 ∨ p4) ∨ p4) ∧ (p3 → (p1 ∨ False)))) ∨ (p2 → (p4 ∨ p5))) ∨ True)) ∨ ((p2 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256663496960725890820563552336 : ((p1 ∨ False) → ((p2 ∧ (((p5 ∧ (p4 ∨ p3)) → p3) → p2)) ∨ (((p3 ∧ ((p5 ∨ p4) ∨ (False ∧ p3))) ∧ p3) → (p1 ∨ (False ∨ p2))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119512685903410024302408120251 : ((p5 → (((p2 ∧ p3) → ((((p4 ∧ (p4 ∨ p5)) ∧ ((True ∨ ((p1 → p5) ∧ True)) → p1)) → False) ∨ (p2 → True))) ∧ p4)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207999173120477530867036177315 : ((((p1 → True) ∨ p1) ∨ (p3 → p5)) → (((True → p1) ∧ p2) ∨ (((p5 ∧ (False ∧ p5)) → False) ∨ (p2 ∧ ((p3 → p4) → (p5 → False)))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322571961274464484020638361292 : (p5 ∨ ((p4 ∨ ((((((True ∨ p4) → (p2 ∨ (p2 → True))) ∨ (((p1 → ((p2 ∧ True) → p4)) → True) ∨ True)) → p1) ∨ False) → p1)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((True ∨ p4) → (p2 ∨ (p2 → True))) ∨ (((p1 → ((p2 ∧ True) → p4)) → True) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648134508658383435345891847872 : ((((((True ∧ p2) ∨ (p5 ∧ ((p2 ∨ (p3 → ((((p1 ∨ ((p4 ∨ p1) → p5)) ∧ p1) ∧ p2) ∧ p4))) → p1))) ∧ p1) ∧ (False ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112624200026890731243511243972 : ((((((((False ∨ (p4 ∨ p2)) ∨ (p2 ∧ p4)) → (((p1 ∨ True) ∧ (False ∨ p3)) ∨ False)) ∧ False) ∧ p2) → (p3 ∧ p1)) → p2) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52085831029153738812166092544 : ((((((True ∨ p1) ∨ (p4 → ((True → p5) → (p4 ∨ (p2 ∧ True))))) ∧ p1) ∨ p5) → (p3 ∧ ((p5 → ((True ∨ p5) ∨ False)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232691332143599904379129479989 : ((p1 ∧ (False ∨ True)) → ((p4 ∧ (((((p1 ∧ p5) ∧ ((p2 → (False → p3)) → (p1 ∧ ((p2 ∨ False) → False)))) ∨ p3) → p4) ∧ p4)) ∨ p1)) := by
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
theorem thm_5_vars_110838775059575612144449968211 : ((((p2 ∨ ((((((p4 ∨ p2) → False) ∧ p5) ∧ p2) ∨ (p4 ∨ (p3 ∧ (((False ∨ p5) ∨ p5) → p3)))) ∧ p5)) ∨ p1) ∧ p2) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776640052685929060150030898018 : (((p1 ∨ ((p1 → ((p4 ∨ (p1 ∧ (p4 ∧ p4))) → ((p3 → ((p3 → p5) ∧ p4)) ∨ ((p2 ∨ p4) → ((p4 → p1) → p2))))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_685549673405400777389647438907 : (((((False → (False ∧ (True ∧ (((True ∧ (p5 ∧ p4)) ∨ True) ∨ ((p4 → p4) ∨ p2))))) ∧ True) → (((p2 ∧ True) ∨ (p2 → True)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46440586794269700158108913350 : (((((p1 ∨ (p2 → p4)) ∨ p2) ∧ ((((False → (p4 ∧ True)) ∧ True) → (False ∧ (False → p2))) ∧ ((p1 → p2) ∧ p4))) ∧ (True ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356042079827877780928742292619 : (p5 → ((p1 ∧ ((True → (p5 ∨ (((((True ∨ p3) ∧ True) ∨ p2) → p1) ∧ (p2 → (p4 → True))))) → p4)) ∨ (p5 → (True ∨ (p3 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134519113134360391886226850632 : ((((True → ((((p4 → p5) → (p5 ∨ p2)) → p3) ∧ (((True ∧ (p3 ∨ (p2 ∨ p1))) → p5) ∨ p4))) ∨ p2) → p4) ∨ (p3 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621555423042714180833918062930 : ((((False ∧ ((((False → p5) ∧ (((p2 ∧ ((p1 ∧ p2) → p1)) ∨ True) ∨ p3)) ∧ p1) ∧ (((p5 → p4) ∨ p5) → (p4 ∧ p3)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_138055580132056983057028719415 : ((True → (False ∧ ((p1 ∧ p5) ∨ ((((True → (False ∨ p1)) ∧ p2) ∨ False) → (((p3 ∧ (p2 → False)) ∧ p4) ∨ p4))))) ∨ ((True ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682009156726525623566715244779 : ((((((True ∧ p4) ∧ (((((p5 → (p5 ∨ (p4 ∧ p2))) ∨ p5) ∨ p4) → True) → p2)) ∨ p1) ∧ ((((p3 ∧ p2) ∨ False) ∧ p5) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328604302957470414627690509990 : (True → (((p5 ∧ (p1 ∨ (p4 ∧ (((False ∨ p2) ∨ p5) ∨ (p4 ∨ p3))))) ∧ True) ∨ (True ∨ (p4 ∧ ((p2 → (p4 ∨ p4)) ∨ (p2 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



