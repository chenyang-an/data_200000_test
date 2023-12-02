variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156975037100781699220001268668 : (((((p1 ∨ ((p4 → (p1 ∧ False)) → p4)) ∧ False) ∧ (((False ∧ p5) → p4) → (True ∧ p4))) ∨ False) ∨ (True ∨ (True ∧ (p5 ∨ (p4 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784782171423398761481947383081 : (((p3 ∨ (True → ((True ∧ p1) ∧ (False ∧ (((p2 ∨ p3) ∧ ((False → False) → False)) ∧ (p4 → (((p1 ∨ (True ∨ p5)) → p5) → False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177722798157358875547641248096 : (((((False → p3) ∧ (p4 ∨ p5)) ∧ ((p1 → p3) → (False ∧ p2))) ∧ p1) ∨ (((p1 ∧ True) ∨ p2) ∨ ((p5 ∧ p2) → ((p4 → True) ∧ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759068102502393352976974640218 : (((p2 ∧ ((p3 → (((p1 → p4) ∨ (p4 ∧ ((True ∧ p1) ∧ p4))) ∧ ((((False ∧ p4) ∨ p5) ∧ ((p3 → p3) ∨ p1)) ∨ p2))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213660356472931929221817182593 : ((((True → p1) ∨ p1) ∨ p2) ∨ (True → ((False ∧ (p1 → ((p2 → p4) ∧ (True → (p2 → p3))))) ∨ (p5 ∨ (((True ∧ p4) ∧ False) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_58904949167811643816912194310 : (((False ∧ p5) ∨ (p5 ∨ (((((p1 → (False ∧ (p3 ∧ (p3 ∨ True)))) ∨ False) → p3) → True) ∧ (((False ∨ p3) ∧ p4) ∨ (p4 ∨ True))))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225658645576753640669330941229 : (((p2 → p2) ∧ p1) ∨ ((((p5 ∧ p5) ∨ p2) ∨ ((True ∧ p5) → (p1 ∨ (p5 ∨ (True ∧ False))))) ∨ ((True ∧ (p2 ∨ (p5 ∨ False))) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354893025073114524340888584830 : (p5 → ((p4 ∧ (((p3 ∨ (((False ∨ False) ∧ (((p4 ∧ True) ∨ ((p5 ∧ p4) ∧ False)) ∨ p1)) ∧ p5)) ∨ ((p3 ∨ p3) → p2)) ∧ p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10269270462050420278745462686 : (((p3 ∨ ((p2 ∨ p3) ∨ ((p3 ∨ ((((p2 → False) ∨ (True ∧ p2)) ∨ ((((p1 ∨ False) ∧ p3) ∨ p4) ∧ p4)) ∨ False)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61096767324271001185700630191 : ((False ∧ (((p4 → (True → ((((False → (p5 ∨ p4)) ∧ True) ∧ False) ∨ p3))) ∨ (p4 ∧ p2)) → (((p1 ∨ p4) ∧ False) ∧ (p1 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58421211946435759767681934802 : (((p2 ∨ p3) ∧ (p3 ∨ ((((False ∨ p5) ∨ p4) ∨ (((p2 → False) → (p2 ∧ p5)) → p3)) ∨ (((p3 ∧ (False ∧ p4)) ∧ p3) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137385825617787500491402291952 : ((p3 ∧ (((True ∨ p2) → p1) ∨ (((p2 ∨ p1) ∧ (True ∧ (p4 ∧ ((True → (p5 ∨ p4)) ∧ (p3 ∨ p5))))) ∨ True))) ∨ (p2 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37874453592844484892327522408 : ((((((p4 ∧ (p5 → (p4 → ((p2 → p5) ∨ (p4 ∧ ((True ∧ (p3 ∧ (p5 ∨ p4))) → p5)))))) → p5) ∧ p3) ∧ (p2 ∧ p3)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199568100887660853151656764203 : (((((False → p5) ∧ (p4 ∧ p2)) ∨ False) → p5) → (((p4 ∨ p2) → p2) → (((p1 → p4) ∧ (p2 ∨ (p1 → True))) ∨ (True → (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258948191820029073521882589265 : ((True → p3) → (((p2 ∧ p1) ∨ ((p3 → (False ∨ (False ∧ False))) ∨ (((p3 ∧ ((p1 ∧ (p2 ∨ p5)) ∨ p5)) ∨ p5) → (p1 ∨ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205240767095869285917044528340 : ((((p4 ∧ False) ∨ p4) ∨ (p2 ∧ p5)) ∨ ((p2 → (False → ((p4 ∨ ((p4 ∨ False) → (False ∨ (p1 → p2)))) ∨ (p2 ∨ (True → True))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243806916057731213551943743284 : ((p5 → p5) ∧ (False ∨ (((((p2 ∨ p5) → (p3 → True)) → p3) → (((((False ∨ p4) → False) → (p2 ∧ p5)) ∨ True) → p2)) ∨ (True ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57294043296941388328199102425 : ((((p2 → p4) → p2) ∨ ((p4 ∨ (p3 ∨ (p3 ∧ (True → (p1 ∧ p1))))) ∨ ((True ∧ ((p2 ∧ p5) → p2)) ∨ (p4 ∧ (p2 → p1))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656273313329386865957724573435 : ((((((p5 ∧ (p4 ∨ p4)) ∨ (p3 ∨ ((p2 ∧ p1) → (False ∧ p4)))) ∧ (p2 → (p4 ∨ (p2 ∧ (p4 → (p5 ∧ p2)))))) ∨ (True ∨ p2)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_663165968759737408703287364227 : (((((False → True) ∧ ((p3 ∧ (False → (True → True))) → ((p1 → p1) ∧ ((False ∧ p1) ∨ (True → (True ∧ (p3 ∧ True))))))) → (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112176895081587398902044254331 : (((p4 ∧ (((p2 → ((p2 ∧ p4) → (False ∨ (((True → (p1 ∨ p4)) ∧ False) → p1)))) ∧ p4) ∨ (p5 ∧ (p3 ∨ p1)))) ∨ True) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629678059487406833144769933188 : (((((((((True ∧ (((True ∨ p5) ∨ True) ∨ p2)) ∧ p1) ∨ ((p4 ∨ p1) ∧ p4)) ∨ p4) ∨ (((p3 ∨ p5) ∧ p3) → p4)) ∨ p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197222848576641883347345110843 : ((((False ∨ ((False → True) ∧ p4)) ∨ p2) → False) ∨ ((True ∧ p4) ∨ (((False → False) → p5) ∨ ((p2 → p1) → ((p4 ∧ (False ∧ p3)) → p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116068906075193208077923267950 : ((((p3 ∨ p5) ∧ p2) ∧ ((True → p4) ∨ ((True ∨ (((p4 ∨ False) → ((p3 ∨ False) → ((p2 ∨ True) ∧ p1))) → False)) → p1))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116870614282875173158725153510 : (((p2 → False) ∨ (p5 ∧ (((p2 → ((False ∧ p3) → p4)) ∧ (((p5 → ((p3 ∨ p5) ∧ (p2 ∨ p1))) → p2) → p4)) ∧ p3))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208818524264322369794470885515 : ((p3 ∧ ((False ∨ (p5 ∨ False)) → p1)) → (p1 ∨ ((p1 → p4) → (((True ∨ ((p4 ∨ (p1 ∨ True)) → ((p4 ∨ p5) ∨ p1))) ∧ p1) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662664652450079298355186039154 : (((((p2 → (p5 ∨ (True ∧ True))) ∧ (p2 ∨ (p5 ∨ (((p4 ∧ p3) → (p2 ∨ (True ∨ False))) ∧ (True ∨ (p2 ∧ False)))))) → (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663784578059162392817230671278 : ((((p2 ∧ ((((p4 ∧ True) → p1) ∨ (p1 → (p5 → True))) ∧ ((False ∨ ((True ∨ True) ∧ ((False ∧ p3) ∧ p3))) → p1))) → (p5 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753033300460832239253262003440 : (((False ∧ (((p3 → p4) ∧ ((((p1 ∨ (((p2 ∨ True) ∧ p2) ∨ p5)) ∨ (p2 → (True ∧ p5))) → p3) ∧ ((p5 ∨ False) ∨ p3))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51932961916609371743038359833 : ((((p1 ∧ ((True ∧ (False → ((True ∧ p4) ∨ True))) ∨ p2)) → (p4 ∧ (p4 ∨ False))) ∨ ((False → (p3 → ((p5 → p5) → p5))) ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52102718140772379958312103647 : ((((False ∨ (((p3 ∧ False) → p3) ∧ ((((p5 ∨ p4) ∨ True) ∧ p2) → p4))) ∨ p3) → (((p5 → True) → (p5 ∨ p5)) → (p5 ∨ p4))) ∨ p5) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h8
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h14
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312354117673398601419377582831 : (p2 ∨ (p3 → ((p4 → (False ∨ (((p4 ∨ (False ∨ (p3 ∨ p4))) ∧ ((p2 ∧ (((p4 ∨ (False ∨ True)) ∧ p4) ∨ p5)) ∨ p1)) → False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206519035896771790744416515439 : ((p5 ∨ (p3 → ((False ∧ False) ∧ p5))) ∨ ((p3 ∧ p4) → (((p1 ∨ (p5 ∨ False)) → (((True ∧ p4) → (p5 → p2)) ∧ p5)) ∨ (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_793952969129807014693742691807 : (((True → (p5 → (False ∨ (((p4 ∧ (((((p3 → False) ∧ p2) ∨ p4) → p3) ∨ ((p2 ∨ p2) ∧ False))) ∨ (p3 ∨ (True → p1))) ∨ True)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322267407109027473017521503596 : (p5 ∨ (((p5 ∧ ((p3 ∧ (p4 ∨ ((p3 → (False ∧ (p4 ∨ (((p5 ∧ p3) ∨ p1) → p4)))) → p5))) ∨ (p3 → (False ∨ p3)))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214827882148505666090913374316 : (((p4 ∨ p3) ∨ (p5 → p4)) ∨ ((((True → p1) → (p1 → p4)) → ((((p1 ∨ False) ∧ p4) → p4) ∧ p1)) ∨ (p3 ∨ (p5 → (p3 ∨ True))))) := by
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
theorem thm_5_vars_47015216416167244430049620509 : ((((p4 ∧ (((True ∧ (p4 ∧ p3)) → p3) → ((((p3 ∧ False) ∨ (p5 ∨ p2)) ∨ False) ∧ ((p4 ∧ p1) → True)))) → False) ∨ (True ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1623964353007687686114987564 : (((((((p3 → p4) ∨ p2) ∨ (p5 ∨ p2)) ∨ p3) → (p2 ∨ ((False → p5) ∧ p1))) → ((True ∧ (p3 ∧ True)) ∧ p1)) → (p1 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((p3 → p4) ∨ p2) ∨ (p5 ∨ p2)) ∨ p3) → (p2 ∨ ((False → p5) ∧ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h8
          -- False on the left can always be used.
          apply False.elim h8
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h9 =>
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
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h3
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246303374532376473521424616016 : ((p4 ∧ p4) ∨ (p1 → ((p3 → (False ∨ (((p2 ∧ p2) ∨ True) → (((p2 ∧ p5) ∨ True) ∧ p2)))) → (((False ∧ False) ∧ p2) ∨ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110869451596593514074520506404 : ((((((p3 → p5) ∧ (False ∨ ((((((((p1 ∧ True) ∨ p5) ∧ p1) ∨ p4) ∨ p3) → False) ∧ p2) → p5))) → p1) → p3) ∧ p3) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702479441190553764245933837804 : (((((p5 → (((p1 → p1) ∧ (True ∨ False)) ∧ False)) ∨ p1) ∨ ((p1 → (True ∧ ((p1 ∧ ((p5 → p1) → p5)) ∧ (p1 ∨ p5)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257583082705519340016238063982 : ((p3 ∨ p1) → ((p3 ∧ p4) ∨ (True ∧ (((p2 ∨ (p3 → (((p3 → p4) ∨ p3) ∧ (True ∧ (True → False))))) ∧ ((p4 ∨ p4) ∨ p1)) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_97206538048886977781771723781 : ((p2 ∨ ((p5 ∨ ((((p5 ∧ (p1 ∧ (p4 ∨ True))) ∨ (True ∨ p2)) ∨ False) ∨ ((p3 ∨ (p5 ∧ False)) → (p2 → (False ∧ p2))))) → False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 ∨ ((((p5 ∧ (p1 ∧ (p4 ∨ True))) ∨ (True ∨ p2)) ∨ False) ∨ ((p3 ∨ (p5 ∧ False)) → (p2 → (False ∧ p2))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203847940746556119659377936586 : ((False → ((p4 ∨ True) → (True ∨ p4))) ∧ ((((((p3 ∨ (p5 ∨ True)) ∨ p4) ∧ p3) ∨ p1) ∨ (p2 → p4)) ∨ (p2 ∨ (p3 ∨ (p3 → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634972165159213508847797828587 : (((((((p2 ∧ ((p4 ∨ (p4 ∨ (p1 ∨ False))) ∧ (False → (p3 ∧ (p4 → p3))))) ∨ (p3 ∨ p1)) ∧ p1) → (False ∧ (p3 ∨ False))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40549182238430796250914345524 : ((((True → ((True ∨ (p3 → (p2 → False))) → (p1 → ((((((True → False) ∧ p4) ∨ (p3 → False)) ∧ False) ∨ p5) ∧ True)))) ∨ True) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134915840907455176233900812338 : ((((((p3 → (((p1 ∨ p2) → p2) ∧ (p3 ∨ (p5 ∨ p5)))) → p4) ∧ (False → (p1 → True))) ∨ p5) ∧ (p1 ∨ p1)) ∨ (p4 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148813828223681757188584799716 : ((((p5 ∨ p4) ∧ (False → (p4 → False))) → ((p1 ∧ (((True ∧ p4) ∨ (p5 ∨ True)) ∨ (False → p2))) ∨ p3)) ∨ (p3 ∨ ((p3 ∧ False) → False))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169038374671425946080925952904 : ((p2 → ((p2 ∨ (p2 ∧ (p1 → p2))) → ((p5 → (p5 → ((p4 → p5) → p4))) ∨ False))) → (((((p1 → p5) ∧ p3) → False) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227684718250173213133712308491 : ((False ∧ (p5 → p3)) ∨ (((p2 ∨ False) ∨ True) → (p2 → ((p4 → (p2 → ((p5 ∧ p1) ∧ (((True ∨ p4) ∧ p2) ∧ (False ∨ p5))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133973378110818558017299307089 : (((((((p5 → ((p4 → ((p1 → False) ∧ ((p4 ∧ p2) → (False → True)))) ∧ p2)) → p5) ∨ True) ∧ p4) ∧ p5) ∨ p1) ∨ (p3 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138716948760744567810954758418 : ((((p1 ∨ (p3 ∨ (p5 ∧ (p3 ∧ p4)))) ∧ (((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) → False)) ∧ p4) → ((p3 ∧ False) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h22 : ((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h24 := h20 h22
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h27 : ((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h29 := h20 h27
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h35 : ((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h36
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h37 := h20 h35
      -- False on the left can always be used.
      apply False.elim h37
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h40 := h38.left
  let h41 := h38.right
  -- Disjunctions on the left can always be decomposed.
  cases h40
  case inl h42 =>
    -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
    have h43 : ((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h44
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h39
    -- We have shown the premise of h41, we can now drive its conclusion.
    let h45 := h41 h43
    -- False on the left can always be used.
    apply False.elim h45
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h48 : ((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h49
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h50 := h41 h48
      -- False on the left can always be used.
      apply False.elim h50
    case inr h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- Conjunctions on the left can always be decomposed.
      let h54 := h53.left
      let h55 := h53.right
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h56 : ((p2 → p4) → (p4 ∨ ((p4 ∧ p1) → (p3 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h57
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h58 := h41 h56
      -- False on the left can always be used.
      apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130194442479994153285135319117 : (((p2 → ((p3 ∨ ((p1 ∧ p4) ∧ ((p5 ∧ True) ∨ p4))) ∨ (((p5 → (p1 ∧ p4)) ∧ p1) → p2))) ∨ (p5 ∨ p2)) ∧ ((p1 ∧ p1) ∨ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302905816298145357066621370456 : (False ∨ (True → (p1 ∨ (p3 → (p1 ∨ ((p5 ∨ (((p1 → True) ∨ ((p3 → (p1 ∨ True)) → p1)) → (((p5 ∨ p3) ∨ p5) ∧ p3))) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319859645582598947471050160225 : (p4 ∨ (((p2 ∧ (p1 ∧ p3)) ∨ p2) ∨ (False → ((((p2 ∨ True) ∧ (p2 ∨ True)) → (p5 → (p1 ∨ p4))) ∨ (((True ∧ p2) → p2) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46406510993856624609888126321 : (((((p4 → (p2 ∧ True)) → ((p2 ∨ True) ∧ p2)) ∨ ((((True → (True ∧ p4)) → False) ∧ (p4 ∨ p5)) ∧ (p4 ∧ p5))) ∧ (False ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309812543765530372163521895660 : (p2 ∨ ((p2 ∧ (p2 ∧ ((False ∧ ((p3 ∨ p1) → ((p1 ∧ (p3 ∨ (p1 ∨ True))) → (p4 ∨ False)))) ∨ p3))) ∨ (p2 ∨ ((p1 ∧ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47008160612934653699009274716 : (((((False ∨ False) → ((((True ∨ True) ∧ p4) ∨ ((((p5 ∨ p2) ∧ (p1 ∧ p5)) ∧ True) ∨ (p2 ∧ p3))) → p4)) → p4) ∨ (p5 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57958654866475101918045902980 : (((p2 → (p3 ∧ p4)) → (p3 → ((p3 ∧ p2) ∨ (((((False → ((p3 ∧ p3) ∨ p1)) → ((True ∧ p1) ∧ p5)) ∧ False) → p4) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351572335131499117127767899806 : (p4 → (((p3 ∨ (p4 → ((True → True) ∧ p4))) → ((False → p2) → ((p2 ∨ p4) ∧ (False ∧ p5)))) → (False ∧ ((p3 ∨ p3) ∧ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (p4 → ((True → True) ∧ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : (p3 ∨ (p4 → ((True → True) ∧ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h12
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h18 := h15 h16
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- False on the left can always be used.
  apply False.elim h20
  -- Implications on the right can always be decomposed.
  intro h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215777503374635881321908277187 : ((p1 ∨ ((p3 → p1) → p3)) ∨ ((p5 ∧ ((True → (p2 ∧ (p1 ∨ (p5 → p4)))) → ((p2 → True) ∨ (p3 → p5)))) ∨ (p2 → (True ∨ True)))) := by
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
theorem thm_5_vars_3926334446803682787180642239 : (False ∨ ((((((p3 → p1) ∨ True) ∨ (False ∧ False)) ∨ p2) ∧ p1) → (((False ∧ (((p1 ∨ (p1 ∨ p3)) → False) ∨ p5)) ∨ True) ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348256852608877267726831928449 : (p3 → (True ∧ (((p3 → (p5 ∨ ((p5 ∧ ((p3 → (p5 ∧ True)) ∧ p3)) ∨ ((p5 ∨ True) ∧ (p2 ∨ p5))))) ∨ p3) ∨ ((p5 ∧ p2) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312517607883635008741374541849 : (p2 ∨ (p5 → (p3 ∨ (((p5 → p3) ∧ True) ∨ (((p1 ∧ (p4 ∨ p2)) ∨ (p3 ∧ (p4 → p5))) ∨ ((False ∨ (p3 → p1)) → (p5 ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696748709030413717941544393742 : (((((((p5 ∨ False) → (p3 ∧ (p3 → p2))) ∨ (p1 → True)) → False) ∧ ((p3 ∧ p5) ∧ ((((True ∧ p4) ∧ True) → (p5 → p5)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57537620430231758327452648616 : ((((True ∧ True) ∧ p3) → ((((p2 ∧ p1) ∨ True) ∧ ((p1 → (p4 ∧ ((p2 ∨ p2) ∧ (False ∨ p4)))) ∨ (p2 ∧ p2))) ∧ (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2013495652627541451586771656 : (((p1 → p5) ∧ ((p4 → (False → (p1 ∧ p4))) → ((p1 → p4) ∧ ((p3 ∧ p5) ∧ (True ∧ False))))) → (p4 ∨ ((p5 ∧ p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → (False → (p1 ∧ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258176149387704882768332938152 : ((p4 ∨ p4) → ((((p2 → (((True ∨ p3) ∧ (p1 ∧ p4)) ∨ p3)) → (p2 ∧ False)) ∧ (p3 → p5)) ∨ ((True → p1) ∨ ((p5 → p4) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738199860909158272330519078251 : ((((False ∧ p3) ∨ ((p5 ∨ ((False → (p3 ∧ (False ∨ True))) ∨ ((((p4 → p1) ∨ (p2 → False)) ∨ p1) → p1))) → ((p5 ∧ False) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663578006452432101123795380238 : ((((True ∧ (False ∨ ((((((p5 ∧ p1) ∨ True) ∨ p4) ∨ (((p2 ∧ p1) ∧ p3) ∧ False)) ∨ (p5 ∨ (p3 → p2))) ∨ p4))) → (p1 ∨ True)) ∨ p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Disjunctions on the left can always be decomposed.
            cases h9
            case inl h10 =>
              -- Conjunctions on the left can always be decomposed.
              let h11 := h10.left
              let h12 := h10.right
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h12
            case inr h13 =>
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
          let h18 := h16.left
          let h19 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h18.left
          let h21 := h18.right
          -- False on the left can always be used.
          apply False.elim h17
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118690923199532513991471343656 : ((p5 ∨ (((((p1 → ((True ∨ (p3 ∧ (p1 → p4))) ∨ p4)) ∧ (p1 ∧ False)) ∧ ((p4 → (p5 ∨ p4)) → False)) ∨ p5) ∨ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137195505256876979327488105166 : ((False ∧ (False ∧ (((p4 → (p5 ∨ (p2 ∧ (((False → ((p2 ∧ p1) ∧ p5)) ∧ p5) → (p3 ∧ p3))))) ∧ p2) → False))) ∨ ((False ∨ False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_39536870343875801926111378821 : (((False ∨ ((p4 ∨ p4) ∨ (p1 ∧ ((((p5 ∧ (True ∨ False)) ∨ p2) ∧ ((((p4 ∧ True) → p2) → (p3 ∨ False)) ∨ p1)) ∧ p1)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118464192578110735152521644233 : ((p3 ∨ ((p5 → ((((p3 ∧ (p5 → ((((p1 → p4) ∨ p2) ∨ False) → p2))) ∧ (p5 ∧ p3)) ∨ False) ∧ (p2 ∨ p5))) ∨ True)) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799120146607350069068722881327 : (((p1 → (True ∧ (p5 ∨ ((p1 ∧ p3) ∨ ((p4 ∧ ((((p5 ∨ p5) → (p1 ∧ p3)) ∨ (p4 → p2)) ∧ (p2 → (p2 → p4)))) ∨ True))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_237916370530864743016641811484 : ((True ∨ True) ∧ (False ∨ (((False ∨ p2) ∧ p2) ∨ ((p5 → p1) ∨ (p2 ∨ ((False ∨ ((p1 ∨ (p5 ∧ p2)) ∨ (False → (p2 ∨ p4)))) ∨ False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756595607295524168980331499248 : (((p1 ∧ (((((p5 ∧ False) ∨ p5) ∧ p4) ∧ ((p5 ∧ (p4 → p2)) ∨ ((p3 ∧ True) ∨ p4))) ∨ ((True → (p5 ∧ True)) → (p2 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117470087734410949798308739058 : ((p1 ∧ (p2 ∧ ((p2 ∨ (p1 ∨ ((p4 ∧ p5) ∨ p5))) ∨ ((((p4 → p5) ∧ True) → (p5 ∧ p3)) ∧ (p1 ∨ (False → p1)))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320021952827862289135602903404 : (p4 ∨ (((p1 ∧ p5) ∨ p1) ∨ (((((p5 → False) ∧ (((p5 → p1) ∨ p4) ∨ (True ∨ p4))) ∨ (p5 ∧ p2)) ∨ (p2 ∧ p3)) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_262465549212415868496676814288 : (True ∧ ((p2 ∨ (p5 → (((False ∨ ((p5 → p3) → p4)) ∨ (p3 ∨ (((p4 ∧ True) ∨ p2) ∨ ((p2 ∧ p4) ∨ (p4 ∧ False))))) ∨ p5))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_204383732545222414686300124807 : (((p5 ∨ (p4 ∨ (p1 ∨ p3))) ∧ p1) ∨ ((p1 ∧ True) → (p5 → (((p4 ∧ p4) ∨ p2) ∨ (((p1 ∧ p2) → p1) → (p5 ∧ (p5 ∨ p4))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114915992338167370991144242660 : ((((p2 ∨ (p5 ∧ (((False → p5) ∧ (False → (p1 ∨ p2))) → False))) ∨ False) → (((((p1 ∧ p5) ∨ p5) ∧ p3) ∨ p3) ∨ p2)) ∨ (p3 ∧ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((False → p5) ∧ (False → (p1 ∨ p2))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h7
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58741471825061592596076779837 : (((p3 → p4) ∧ (False ∨ ((((p1 → ((((p3 ∧ p5) → (p2 ∨ True)) ∧ p4) ∧ ((p5 ∨ p5) ∧ (p2 ∨ p5)))) ∨ p2) → p5) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149554915554940795244015149943 : ((p2 ∧ (((p1 ∨ (p5 → (p4 ∧ p1))) ∨ (True ∧ p4)) ∨ (p1 ∨ (True → (((False ∧ False) → False) → False))))) ∨ (p3 → ((False ∧ False) → p1))) := by
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
theorem thm_5_vars_179609235200957616933931029913 : ((p3 → (p2 ∨ ((((p5 → p4) ∧ (p5 ∨ p4)) → (p1 ∧ p2)) → p5))) ∨ (p2 → ((((p2 ∧ (p4 → p3)) → True) → (p4 ∧ p4)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ (p4 → p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178668394132808848557150669925 : ((((p4 → p4) → (p5 → p4)) ∧ (p4 ∨ (p3 ∧ (p1 ∧ (True ∧ p4))))) ∨ ((((((p3 ∨ True) → p3) → p3) ∧ False) ∧ (p5 ∨ True)) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780227765977428763099304529162 : (((p2 ∨ (((((((p3 → p5) ∧ (True → (p2 → (True ∧ False)))) → p2) ∧ True) ∧ ((False ∧ p2) → p1)) ∧ p1) → ((p1 ∧ p3) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263884021432381650787848672392 : (True ∧ ((((p2 ∧ (p3 → p3)) → (p5 → (((p1 ∨ True) → p1) ∧ False))) ∨ p1) ∨ (((True ∨ p3) → False) → (p5 → ((p3 ∧ p4) ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117462525338181214683259732811 : ((p1 ∧ ((True ∨ p3) → ((((False ∧ (p3 ∨ (p2 → p4))) → (p1 → p3)) ∧ p4) ∧ ((((p4 ∧ True) → p5) ∨ False) ∨ p3)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167283868753892368112274506904 : (((((((p5 ∧ True) → p4) ∧ p1) → ((p5 → ((p2 ∧ p1) ∧ p2)) ∨ False)) ∨ True) → p1) → ((True ∧ (((True ∧ p5) ∧ p3) ∨ p4)) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (((((p5 ∧ True) → p4) ∧ p1) → ((p5 → ((p2 ∧ p1) ∧ p2)) ∨ False)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : (((((p5 ∧ True) → p4) ∧ p1) → ((p5 → ((p2 ∧ p1) ∧ p2)) ∨ False)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118828628838272609989917926901 : ((True → ((True → (((True ∧ p2) ∧ p5) → (((((p1 ∨ False) ∨ ((p2 → True) ∧ p3)) ∧ p2) → (False → p1)) ∨ p5))) → p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83256374115398360465060222332 : ((((p3 ∨ ((((p3 ∧ ((p2 ∧ (p1 ∧ p2)) ∨ (p1 ∨ p2))) ∨ True) ∨ p5) ∨ p4)) → False) ∧ (((True ∨ False) ∧ (p3 ∧ p4)) ∨ p1)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p3 ∨ ((((p3 ∧ ((p2 ∧ (p1 ∧ p2)) ∨ (p1 ∨ p2))) ∨ True) ∨ p5) ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ ((((p3 ∧ ((p2 ∧ (p1 ∧ p2)) ∨ (p1 ∨ p2))) ∨ True) ∨ p5) ∨ p4)) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328290720372575111683563326596 : (True → ((((((False → (p2 → p5)) ∧ (p4 ∧ p4)) → p2) ∨ False) ∨ ((p3 ∧ (p1 ∨ (p2 ∨ p3))) → p3)) ∨ (((True ∨ p4) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135413672933709931254860302444 : ((((p2 ∨ p2) ∧ (p5 ∧ (p5 ∨ ((p5 ∨ (p3 ∨ p2)) → (False ∨ (p4 → (p1 ∧ p4))))))) ∨ ((False → True) ∨ p2)) ∨ (p1 ∨ (p1 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216367600124618064364393275737 : ((p3 → ((False ∨ p4) → False)) ∨ (((False ∧ ((p5 ∧ False) ∧ True)) ∧ (True ∧ p4)) ∨ (False → (((p2 ∧ p5) → ((p4 ∨ p2) ∧ p2)) ∧ p3)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147695812137107150909073057614 : ((((((p1 ∧ (((p5 ∧ p1) → (p3 ∨ True)) ∧ p2)) ∨ p1) ∨ p1) ∨ ((p5 → (p3 ∨ p4)) ∨ p3)) → p4) ∨ (((True ∨ p4) ∧ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180594462156900110019370149463 : (((p3 → ((p3 ∧ False) → (p3 → (p3 ∨ p2)))) → ((False ∨ p4) ∧ False)) → ((((((p2 → True) ∨ (p1 ∧ p2)) ∧ p4) ∨ p2) ∧ False) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((p3 ∧ False) → (p3 → (p3 ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (p3 → ((p3 ∧ False) → (p3 → (p3 ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h10
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (p3 → ((p3 ∧ False) → (p3 → (p3 ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- False on the left can always be used.
    apply False.elim h23
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h18
  -- We need to get the right conjuct of h24 based on <expert-advice>.
  let h25 := h24.right
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137704084125606633989237677303 : ((p1 ∨ (((((p1 ∧ ((p2 ∨ False) ∨ True)) → False) → (p5 → (p2 → True))) → p3) ∨ ((False ∧ (p2 ∨ p3)) → True))) ∨ ((p1 ∨ True) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694561438397743593571822846205 : ((((p2 ∧ ((p3 ∨ (False → (True ∧ p1))) ∧ ((p3 ∨ (p4 ∧ p2)) ∧ True))) ∨ (False → (p1 ∨ (p5 ∨ (((p3 ∨ p2) ∨ p3) ∧ True))))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_134666704111643275887466008286 : ((((p4 ∨ (p5 → (p2 ∨ (p4 ∧ ((p5 ∧ p5) → p2))))) → ((p3 ∨ (p1 ∧ ((p2 ∧ p2) ∨ p2))) ∧ p5)) → p3) ∨ (False ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



