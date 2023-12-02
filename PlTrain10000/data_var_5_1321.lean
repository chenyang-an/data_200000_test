variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186069210746774583462194975721 : ((((p3 → ((p2 ∧ ((p5 ∧ p1) → p3)) ∨ False)) ∨ False) ∨ True) → (((p5 → True) → p5) ∨ ((p4 ∨ False) → ((True → (p1 → False)) ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193125384567311162439589444741 : (((((False ∧ p3) ∧ p2) → p2) ∨ (False ∧ (p3 ∧ p3))) → ((p1 ∧ ((((p3 ∧ p2) ∨ p4) ∧ True) ∧ p2)) ∨ (p4 → (True ∧ (p4 ∨ True))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196698111685324799486753368415 : ((((p4 ∧ (p5 ∧ (False ∨ False))) ∨ True) ∧ p3) ∨ (p3 → (False → (True ∨ ((p4 ∨ ((False → p1) ∧ (False → ((p3 ∨ p4) ∨ True)))) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224790804219323013015156035861 : ((p4 → (p2 ∨ True)) ∧ (((p1 ∨ ((True → p4) → (p3 → (((p3 ∨ (False ∧ (p4 → p3))) ∧ p4) ∨ (p5 ∧ (p2 ∨ p3)))))) ∨ p3) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301239686196455268453249961339 : (False ∨ (((p1 ∨ (p3 → (p1 ∧ True))) ∧ p2) ∨ (p5 ∨ ((((p1 → (p3 → ((True ∨ p2) → (p3 → p1)))) ∨ p3) ∨ (False → p5)) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670462827359853773767125107350 : (((((p5 ∧ True) ∧ ((p4 ∧ p2) ∨ ((True ∧ ((p4 ∧ (p5 → p5)) ∨ p1)) → (p1 ∧ (False ∧ (p1 ∨ p3)))))) ∨ (p1 ∧ (p3 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42147731931451905989756225735 : ((((True → p3) → (p4 → (p1 ∨ (p1 ∧ (((p1 → p5) → (False ∧ p2)) ∨ ((((True ∧ p2) ∧ p1) ∨ p3) ∧ (p3 ∧ p2))))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743636393849200334895946659650 : ((((True ∧ p1) → ((p4 → (p4 ∨ (p1 ∧ (p3 ∧ (p5 ∧ p4))))) ∧ ((p5 → ((p3 ∧ p4) ∧ False)) ∨ (((False ∨ p2) ∨ p2) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725152603884977096216962887026 : ((((p1 → (True → p3)) ∧ (p4 → ((((p2 → False) → (((p4 ∧ (p5 → p5)) → p5) ∧ (p3 ∨ p2))) ∨ p1) ∨ (p5 ∨ (p3 ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112793618076319164387136849537 : (((((True ∨ ((p2 ∨ p5) ∧ True)) ∨ p1) ∧ ((p1 ∨ (p3 ∨ (p5 → (p4 ∨ p3)))) → ((False ∧ (p3 ∧ True)) → True))) → False) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207751396390523499244511652057 : (((False ∨ ((False ∨ p3) → True)) → False) → (False ∨ (((((p3 ∨ (p3 ∧ p4)) ∨ True) ∧ (True → p2)) → ((True → p2) ∧ True)) → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((False ∨ p3) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51859721590395266579770767967 : (((((((True ∨ (True ∧ (((p3 ∨ p4) → p5) ∨ p4))) → False) ∨ p2) ∨ p4) ∨ False) ∨ ((p1 → (True ∨ p3)) ∧ (True → (p5 → True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179652860934917604641399761783 : ((p5 → ((False ∨ ((p1 → p2) ∨ (p4 ∧ (p1 ∧ p1)))) ∧ (False ∧ p4))) ∨ (p3 ∨ ((((True → (p4 ∨ True)) ∧ False) ∧ False) → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_61011572818655360371995974491 : ((False ∧ (((p1 ∨ True) → (p2 ∧ ((False ∨ (((p4 → p5) ∨ (((True → p5) ∧ (p3 ∨ p1)) ∨ (p1 ∧ p4))) → True)) ∧ p1))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224271879154741039675631863418 : ((False → (False ∧ p4)) ∧ ((((False ∧ (((p1 → (p1 ∨ (((p4 → p3) ∨ (p1 → p5)) ∧ True))) → False) ∧ True)) ∨ True) ∧ (p3 ∧ p2)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67810671329261851743405699704 : ((p2 → (((p5 ∨ (p5 → False)) → (p4 ∧ ((((False ∨ True) ∨ ((p2 ∧ (p2 → (p1 ∧ p5))) → (p3 ∨ True))) ∨ p4) → False))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124734716127626991960281298841 : ((((True ∧ (True ∨ p5)) → p4) ∧ ((((((p1 → True) → ((True → p2) → p3)) → p1) ∨ ((True ∨ p3) ∧ p2)) ∨ p2) ∧ p2)) → (p4 → p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696065424774532807631770631078 : ((((p4 ∧ ((p1 → (p1 → (p1 → (((p1 ∧ False) → True) → p2)))) ∧ p5)) → ((((p3 → p2) → (p4 ∨ p3)) ∨ (p3 ∨ p3)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348982236784307157632556866302 : (p3 → (p4 ∨ (((((p3 → p2) → (p2 ∧ p3)) → False) ∧ ((p1 ∨ p1) ∧ (p1 → ((p2 ∧ True) → ((False → True) ∨ p4))))) ∨ (False → True)))) := by
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
theorem thm_5_vars_185353460541788389318638601269 : ((p4 ∧ ((p4 ∨ p1) ∧ ((((True ∧ p1) → p4) → p4) → p1))) ∨ (p1 ∨ ((((p2 ∧ ((p4 ∨ False) → (p3 ∧ p2))) ∧ False) ∧ p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53563050006132372936985824237 : (((((p3 ∨ ((p3 → p1) ∧ (False ∨ p1))) → p2) ∨ False) ∧ ((False → ((p3 ∨ p3) ∧ ((p1 ∨ ((p2 ∧ p5) → True)) → p1))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766579283011861019847545104734 : (((p4 ∧ (p4 ∧ (p4 ∧ ((p2 → ((((False ∨ p5) → (((p3 ∧ p5) ∧ p1) ∨ p5)) ∨ (p2 ∨ (p5 → True))) ∨ False)) ∨ (p4 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161938442821099775276028664620 : ((p2 → ((((True → p3) ∨ p1) ∨ (((False ∧ (False ∨ p2)) → ((False ∧ p4) ∧ False)) ∧ False)) ∧ p2)) → ((p5 → ((p5 ∨ True) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155641114085182001963092038915 : (((p2 → True) ∧ (p4 ∨ (((p4 ∧ p1) ∨ ((p5 → False) ∧ (p4 ∨ p5))) ∨ ((False → True) ∨ True)))) ∧ (((p2 ∨ (p5 ∨ p1)) ∨ True) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_184325159523564008182359735790 : ((((p3 ∧ False) → ((((p4 → True) → p4) → p1) ∧ p2)) → False) ∨ ((p4 ∨ (((p3 ∧ ((p2 ∧ (False ∨ p3)) ∨ p3)) → p3) ∨ False)) ∨ p5)) := by
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
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114725222359574442992005610944 : (((((((False ∧ p5) ∧ p3) ∨ True) → (p5 ∨ (p3 ∧ p1))) ∨ (False ∧ (p3 → False))) → (True ∧ (p3 ∨ (True ∧ (p5 ∨ p3))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206546561161865662760637585228 : ((True → ((p5 → p3) ∨ (p2 ∨ False))) ∨ (p2 ∨ ((p1 ∨ (p5 ∨ (p4 ∨ (p4 → (True ∨ ((True ∨ (p3 ∧ p3)) ∧ (False → p4))))))) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244449580521648518052015583980 : ((False ∧ p2) ∨ ((((False ∧ False) ∨ (((p1 ∧ (p3 → p4)) ∨ p3) → p3)) ∨ (True → ((p5 ∨ True) ∨ p3))) ∨ ((p2 ∨ (p2 ∧ p5)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680964632823085373743910806625 : (((((True ∨ False) ∨ (p5 ∨ ((((p4 ∧ (p5 ∨ p5)) ∨ p1) ∨ (p2 → ((p1 ∨ p2) → p1))) ∨ p2))) → (((False → True) ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303993749246745463010247504251 : (p1 ∨ (((False ∨ p4) ∨ (((p5 ∨ (p3 ∧ p2)) ∨ ((p2 → ((False ∧ True) ∧ p2)) ∨ p2)) ∨ ((p3 ∧ (False ∧ (p1 → p1))) → True))) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349958787813177090483494311249 : (p4 → (((((p2 ∧ p1) ∨ False) ∨ (p4 → (((((p1 ∨ (p1 → (p5 → (False ∨ p2)))) ∧ p5) ∧ p1) ∧ (p1 ∨ p2)) ∨ True))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159653818253587419275561302990 : (((((((False ∧ (False ∨ (p5 ∨ ((False → False) → (True ∧ p5))))) → False) → p1) ∨ p5) → p4) ∨ True) → (p4 ∨ (((p1 ∧ False) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_906966210412983991992240170932 : (((((p1 ∧ (p5 ∨ (p2 ∨ ((False ∨ (False → p5)) ∨ (p3 → True))))) ∨ (p2 ∨ (False → (p1 → True)))) → (p5 ∧ ((p1 ∨ p5) ∧ p2))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (p5 ∨ (p2 ∨ ((False ∨ (False → p5)) ∨ (p3 → True))))) ∨ (p2 ∨ (False → (p1 → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607665624178884535426738752274 : (((((p5 ∧ ((((((p2 ∧ (p3 ∧ (p2 ∧ p1))) → (True → (p1 ∨ p1))) ∨ True) ∨ (p3 → p1)) → p5) ∧ (p2 ∧ p4))) ∧ p2) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_49309366019355238436310536455 : (((p1 ∨ (p2 ∨ ((p3 ∧ (p4 ∨ p2)) ∨ (p3 → ((p5 ∧ (p1 → ((False ∨ (True ∨ p3)) ∧ p3))) → True))))) ∨ ((True ∧ False) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309658091336940930598414547147 : (p2 ∨ ((True → (((p3 ∨ (p5 ∧ (True → ((False ∨ (True ∨ p3)) → False)))) ∨ p1) ∨ (p3 ∨ ((True ∨ False) → False)))) ∨ ((p1 ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45040888515385451566197455667 : ((((p5 ∨ False) ∨ ((p4 ∨ (True → p4)) ∧ (p5 ∧ (((((p2 ∧ (p4 → p4)) ∧ (p2 ∧ True)) ∧ p3) ∨ (False ∧ p1)) → False)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134592486885400328874178541212 : (((((False ∨ (p1 ∧ (p1 ∨ (((p3 ∧ (p2 → p2)) ∨ p2) ∧ ((p3 → p4) → p2))))) ∧ True) → (p4 ∨ p2)) → p1) ∨ ((False → False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41428304313170067982100942567 : (((((False ∨ ((p5 → (p5 ∧ (p3 → (p5 → (p2 ∧ p4))))) ∧ True)) ∨ p4) → (p3 ∧ ((p3 ∧ p2) ∧ ((p2 ∨ p3) → p5)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621066205620197948724505571109 : (((((p2 → p1) → ((False → p5) ∧ (p2 ∧ (p3 ∨ ((p2 ∨ (p3 ∧ (True ∨ p3))) → (p2 ∧ (p1 → ((p3 → p4) ∨ p2)))))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_117510404342519353739239896083 : ((p2 ∧ (((p1 ∧ (((False ∧ (p2 → False)) → ((p3 ∧ (p1 ∧ p5)) ∧ (((p4 ∨ p4) → True) → True))) → p4)) ∨ True) ∨ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231899412513518479996719414950 : (((False ∨ True) → False) → ((((p1 ∨ False) ∨ ((((p5 → ((p2 ∨ p2) ∧ True)) → (p1 ∨ True)) → p5) ∧ (p4 → False))) ∨ p5) → (False ∨ p1))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217868647548599385972450201363 : (((False → (p4 ∨ p4)) → p5) → (((((True → p2) ∧ False) ∨ ((p5 ∧ p3) → (True ∧ p1))) ∧ ((p4 ∧ (p3 ∨ p3)) ∨ (p1 ∧ p5))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p4 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48424439176866970437566252417 : (((p3 → ((((p4 ∨ (p4 ∧ ((((p3 ∨ True) ∧ True) ∧ True) ∨ True))) ∨ p2) ∧ p3) ∧ (((p5 ∧ p1) ∨ p1) ∨ p3))) → (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168697370012838647889089218392 : ((True ∨ ((((True → False) → p4) ∧ (p4 → (((p1 ∧ (p3 ∧ False)) → False) ∨ p5))) ∧ True)) → ((((p5 ∧ True) → (p3 ∨ p4)) ∧ p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690243155968887778427552581360 : ((((True → (((p1 → (p1 ∧ ((False → ((p3 → True) ∧ p1)) ∨ True))) → p3) ∧ p5)) ∨ ((p4 ∧ (p3 → (p5 ∧ (True ∨ p3)))) → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962407704650117262057590808403 : ((((True → False) ∧ ((p5 ∨ (p2 → (((p5 → ((((p3 ∨ p5) → p2) ∧ p1) → p1)) ∧ p5) ∧ p2))) ∨ (((p2 ∨ p5) → p4) → p1))) → False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328197742659605697798807116263 : (True → (((False ∧ (p5 ∧ p2)) → ((p5 → p2) ∧ (True ∧ ((False ∨ ((p5 ∨ (p1 ∨ p2)) → p5)) → (p3 ∧ p3))))) → (p3 ∨ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690516646262850117917519181925 : (((((p3 ∧ ((p3 ∧ ((p1 → p5) ∧ ((True ∨ (p4 ∨ p2)) ∨ p2))) ∧ True)) ∧ p4) → (((True → ((p2 → False) → p5)) → p2) ∨ p3)) ∨ p4) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50263317530189382439860574323 : ((((((((True → p4) ∧ p2) → (((p4 → p1) ∧ p2) ∨ p5)) ∧ (p2 ∨ p3)) ∨ False) ∧ (p5 ∧ p1)) ∨ (True ∨ (p5 → (p1 ∧ p3)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50555268239982268471787528373 : ((((True → ((True ∨ (p1 ∨ (True ∨ (True ∧ p3)))) → (p3 → (((True → True) → False) ∧ p3)))) ∨ p2) → (False ∨ ((p3 ∨ p2) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245980490097957472916356627825 : ((p4 ∧ True) ∨ ((p1 ∧ (p4 ∧ False)) ∨ ((p1 ∨ (p2 → True)) ∨ ((p5 ∧ False) → ((False → (((p5 ∨ (p5 ∨ p5)) → p4) ∧ p5)) → p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111883145845012790404265297633 : ((((p1 → ((((False ∧ (p3 → (p5 ∧ p5))) ∨ p3) ∨ p5) ∧ ((p5 ∨ True) ∨ p2))) → ((p2 ∨ p2) → (p5 ∧ p3))) ∨ p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55055554569958633584339041064 : (((p1 ∨ ((p4 ∧ True) ∧ (p5 ∧ p4))) ∧ ((((p1 → ((False ∧ (p1 ∧ p4)) → False)) ∨ p3) ∧ p2) → (p3 ∨ (p1 → (p2 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48744239394564647892222640887 : ((((True ∧ (p5 → False)) → (((p4 ∧ (((p3 → (False ∧ (p4 → p2))) ∧ p3) ∨ (p2 → p4))) ∨ True) ∧ False)) ∧ (p4 → (True ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733561912166418567573830585236 : ((((p4 ∧ p4) ∧ ((((p4 ∨ p1) ∨ p3) ∧ True) ∨ ((False ∧ (p1 → p5)) ∧ (((False ∨ p5) ∧ ((p4 → p5) ∧ (True → p4))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116130287414664075067383549251 : (((p1 ∧ (True → p1)) ∧ (((p5 ∨ p3) ∨ p4) ∧ (((p4 → (True → ((p5 ∧ p4) → (p2 → p2)))) ∧ p2) ∧ (False ∧ p3)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208318685436444019634281867342 : (((False → p2) ∧ ((p5 ∨ True) ∨ p4)) → ((p3 → False) ∨ ((p2 ∨ (((True → (((p5 → p5) ∨ p2) → True)) ∨ p2) ∨ p4)) → (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208975700118094368697882748452 : ((True ∨ (p5 ∧ (p1 ∧ (True ∨ p2)))) → (((((p4 ∨ p1) → p1) ∨ p1) ∨ (p3 ∧ p5)) ∨ (p2 ∨ (p5 → (((False → p2) ∧ False) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111601004497977849837178279166 : (((((((((p5 → (True ∧ ((p2 ∧ (p4 ∧ False)) → p1))) ∨ False) ∧ (p2 ∧ (True ∨ True))) ∧ p2) → p3) ∧ p1) ∨ False) ∨ True) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300864450101868111296754018491 : (False ∨ (((((False ∨ p3) ∨ ((p3 ∨ (p2 ∧ p1)) → (p4 ∧ p4))) → p3) ∧ p3) ∨ ((p3 ∧ ((False ∧ p2) → (p4 ∧ (True → p3)))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232204528654791860716262139898 : (((False → p4) → p2) → ((p1 ∧ (p5 → (((((p5 ∧ (True → ((p2 → True) ∨ p3))) ∧ (p4 ∧ p3)) → (p2 ∨ p5)) ∧ p1) → p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264026822606593613653284872481 : (True ∧ ((p5 → (((p3 ∧ p5) → p3) ∧ ((p2 ∧ (False → p1)) ∨ p2))) → (((p5 ∧ ((((p3 → p2) ∨ p2) → True) ∧ p1)) ∨ True) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563199245503134422872220650 : (((p1 → (p2 ∨ (((p3 ∧ (p1 ∧ (p5 ∧ (False ∨ ((p1 → (p2 ∧ p5)) ∨ p5))))) ∧ ((True ∧ False) ∧ p2)) ∨ p1))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68965884611064560275774169996 : ((p4 → (p3 → ((((p2 → p2) → ((((p1 ∧ (p5 ∧ p4)) ∨ ((p2 ∧ (p3 ∧ (p3 ∧ p2))) ∧ p2)) ∨ False) ∧ p5)) ∨ p4) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698899969809908574089719630342 : ((((p2 ∧ (((p5 ∨ p5) ∨ p4) → (p5 ∧ ((p5 → p3) ∧ False)))) ∨ ((True ∧ (((p2 ∨ True) → (p5 ∧ True)) ∧ (p2 ∨ p1))) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_300277969220471603873516349960 : (False ∨ ((p1 → ((True ∧ ((((p1 → (p1 ∧ (p5 ∧ ((p4 ∨ False) → True)))) ∨ p5) → p2) → ((p5 ∧ p2) ∨ p4))) ∨ False)) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715821410163564347688953059082 : ((((((False → p4) → p4) ∨ p2) ∧ ((((((p5 ∨ ((p1 ∨ p2) → p2)) → False) ∧ ((p5 ∨ False) → p5)) → (p4 → p2)) ∧ p5) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51909922794946055786790241990 : (((((((True → False) → (False ∨ (p5 ∨ (p2 ∨ True)))) ∨ p4) → p2) ∨ (p2 ∨ p2)) ∨ (p5 → ((p3 → p3) ∨ (p1 ∨ (p4 ∧ p5))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809896245885733193010379820110 : (((p5 → ((p5 → (True ∧ ((True ∧ (p2 ∨ ((p2 → (((p5 ∧ (p4 ∨ False)) ∧ True) → True)) → (p1 → p1)))) ∧ False))) → (p4 ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173855997179005071309561551150 : ((((((p4 → False) ∨ ((p2 ∨ (p5 → (p4 ∧ p2))) ∧ p1)) ∧ True) ∧ True) → p3) → (p3 ∨ (((p5 → p3) → p2) ∨ ((p4 ∧ p2) → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669545496027385163529394611952 : (((((False → (((p5 ∨ True) → p4) → (p2 → (p3 ∧ (p5 ∧ ((p4 ∧ (p2 ∧ True)) → p1)))))) → (p3 → p3)) ∨ ((p5 → p1) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_186716093144262482360218771259 : ((((p1 ∨ p2) ∨ (p4 ∧ (False → True))) ∨ (p5 ∧ (p3 ∨ p3))) → ((p3 ∧ False) ∨ (((p3 ∨ p1) → (p3 → ((p3 ∧ p3) → p4))) → True))) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154312553640878970866206114402 : (((p4 ∧ (p2 ∧ ((((p5 → ((p3 ∨ (False ∨ p4)) ∧ p3)) → (p5 ∨ p5)) ∧ p3) ∧ p3))) ∨ True) ∧ ((False ∧ (p4 → p1)) → (True ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110813386931324553100524476710 : ((((((p4 ∨ False) → (p1 → ((p3 → p1) ∧ p1))) → (((p1 ∧ (p1 ∧ p1)) ∧ ((p5 → p2) ∨ p5)) ∧ p3)) ∨ p2) ∧ p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698325994871623038230833072501 : (((((((((p3 ∧ p5) ∧ p4) ∨ p3) ∧ False) ∨ p5) ∨ (True ∨ p2)) ∨ (True ∧ ((p2 → (((False ∧ p3) ∨ (p5 → p5)) → p3)) ∧ p4))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_115898383887127850902646270271 : (((((p2 → p4) ∨ False) → p4) ∨ (((True → p2) → False) ∧ (False ∧ (((p5 ∨ (p4 ∨ False)) ∧ p1) ∨ ((p3 ∨ True) → False))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181564346036816999497153431132 : ((False → ((p2 ∨ False) → ((p4 → (p1 ∧ False)) ∨ (p3 ∧ (p5 → p4))))) → (p1 → (((p1 → ((p5 ∧ p4) ∧ p1)) → p4) ∨ (p1 ∨ p4)))) := by
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
theorem thm_5_vars_42543557169609401332235186024 : (((p1 ∨ (((False ∨ p1) ∨ (((p5 → p5) ∧ p4) → ((p1 → p5) ∨ p3))) ∧ (((True → (p3 ∧ p1)) ∧ (p5 → p2)) → p1))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657113568153903570642047336452 : ((((((p3 ∧ p4) ∨ p1) ∨ (((((True → (p1 ∧ True)) → ((p5 ∨ p3) ∨ (False ∧ p5))) ∧ (p1 → p4)) ∨ p3) → p1)) ∨ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167445928184961710089559122059 : (((p3 ∨ (((False ∨ p3) ∧ (((False ∧ p2) → ((p2 → p5) ∧ False)) ∨ p4)) → p1)) → False) → (p1 ∨ (((p5 ∧ p4) → p4) ∨ (p2 ∧ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341995151405240640484359455380 : (p2 → (((p4 ∨ (p2 → ((p4 ∨ p4) ∧ p3))) ∨ (((True ∧ ((True ∧ p2) → ((p4 ∨ p1) ∧ p1))) ∧ p3) → p1)) ∨ ((p2 ∧ p3) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184588194878346260183285931828 : (((p3 ∨ ((p5 → (p3 ∧ (p2 ∧ False))) → p4)) → (p4 → p3)) ∨ ((True ∧ ((p5 ∨ ((True → True) → False)) ∧ p2)) → (p5 → (True → True)))) := by
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
theorem thm_5_vars_117355699098623507689707271505 : ((False ∧ (p4 ∧ (p4 ∨ (p5 → (((p4 ∧ (p5 ∧ p2)) ∨ ((p2 → (p5 ∧ p2)) ∨ (p4 → False))) ∧ (p4 ∧ (p1 ∧ True))))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787815542628881597212635095745 : (((p4 ∨ (p1 → (((((((True ∧ False) → (p5 ∨ ((True → (p3 ∨ p4)) ∧ p4))) ∧ (p1 ∧ p2)) ∧ p4) → (False ∨ False)) ∨ False) ∨ True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_178413638867352422995808380936 : (((p5 ∧ ((((p3 → p1) ∨ (p5 ∨ False)) ∨ p5) ∧ True)) → (p1 ∧ False)) ∨ (True ∨ (((p2 ∨ (p1 → False)) ∧ p5) ∨ (True → (p5 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340907146401824854605279171289 : (p2 → (((((((p5 → p3) → p5) → (p4 → p5)) ∨ p2) ∧ True) → ((p2 ∨ p2) → ((False ∧ p4) ∧ ((p2 ∧ (True ∧ False)) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76968727233792750476155716866 : (((((p5 ∨ p1) → (False ∧ ((p4 → p2) ∨ p3))) → ((((p5 ∨ False) ∨ (((p4 → True) → p2) ∧ False)) ∨ (True → False)) ∨ True)) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ p1) → (False ∧ ((p4 → p2) ∨ p3))) → ((((p5 ∨ False) ∨ (((p4 → True) → p2) ∧ False)) ∨ (True → False)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183904091029659192928005104716 : ((((False ∧ False) → (p2 → (((p5 ∨ p1) → True) → p3))) ∧ p2) ∨ (((p2 ∧ p5) ∧ p2) ∨ ((((p4 ∨ True) ∧ False) ∧ p4) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_2270580967547043032068219648 : ((((p2 ∨ (p4 → (p1 → (False ∨ p5)))) → (p3 ∨ (p5 → False))) ∧ False) ∨ (((p2 ∧ p4) ∨ ((p5 → (False ∨ False)) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148406513577835251230565001116 : (((((p2 ∨ (p1 → True)) → (((True → (True ∨ False)) → True) → p5)) ∧ True) → (((True → p1) → p3) → p2)) ∨ (False → ((p1 → p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161420640155520882789903016867 : ((p2 ∧ ((((((p3 → p5) ∨ True) ∧ (((False ∧ (True ∧ False)) → True) → p4)) ∧ p1) ∨ True) → False)) → ((False → p2) → ((p5 → p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((((p3 → p5) ∨ True) ∧ (((False ∧ (True ∧ False)) → True) → p4)) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (((((p3 → p5) ∨ True) ∧ (((False ∧ (True ∧ False)) → True) → p4)) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147409839968158916464161609318 : ((((p3 ∨ ((p4 ∧ p3) ∧ p5)) ∧ (False ∨ (p1 → (p4 ∨ (p1 ∧ ((True ∧ p3) ∨ (p1 → p2))))))) ∨ True) ∨ (p5 → (p1 ∨ (p3 → p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42340862035606727451276247683 : (((p3 ∧ (((p3 ∨ (p3 ∨ (((p1 ∨ p4) → False) → p1))) ∨ (((False → (p3 ∨ p1)) → False) ∧ (p4 ∧ p3))) ∨ (p1 → p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249323673122052274568777116034 : ((p4 ∨ p5) ∨ ((p1 ∧ p2) ∨ ((p4 ∧ (p4 → p3)) ∨ (p4 → ((True ∧ (p2 → (p1 → (p2 ∧ p2)))) → ((p4 ∨ p3) ∨ (False ∨ p4))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218610005791276427882536446421 : (((p4 → p5) → (p1 ∧ p5)) → (True ∧ (((p5 ∧ (((p1 ∨ (False → True)) ∨ (False ∨ p3)) ∨ ((p4 ∨ (True ∨ False)) ∧ False))) ∨ p5) → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
  case inr h20 =>
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65954882493682157776440133592 : ((p4 ∨ (p3 ∨ (p1 ∨ ((((p3 ∨ (True ∧ (p3 → (p2 ∨ (((p3 ∨ p5) ∧ ((p1 ∧ True) ∨ False)) ∧ p2))))) → p1) ∧ p4) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39826687780507212178250918758 : (((p1 → (((((p5 ∨ True) ∧ p3) ∧ ((p5 → p3) ∨ (p4 ∨ False))) → ((((p5 → False) → (p5 ∧ p4)) ∧ p2) ∨ False)) ∧ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217388052342914299647285223300 : (((True → (True ∧ True)) ∨ p4) → (((True → (False → p1)) ∧ p5) → (((p5 ∨ p4) ∧ ((p2 ∧ (p5 ∧ p5)) ∨ (p4 ∨ p1))) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177006899741206217827395005678 : (((p4 → p5) → (((p5 ∧ (False ∨ False)) ∨ (p4 → (p3 ∨ p2))) ∨ True)) ∧ ((p3 → ((True ∧ p3) ∨ (p4 ∧ (p4 ∧ True)))) → (p1 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



