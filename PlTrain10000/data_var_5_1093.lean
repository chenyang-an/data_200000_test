variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337651109688465369061249803018 : (p1 → ((((False ∨ ((False ∧ (p3 → (True ∨ p5))) ∨ p1)) ∧ ((p4 → (False ∨ True)) → p4)) ∨ p1) ∨ (((p4 ∨ p5) ∧ (p1 ∨ p3)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54084486217200173459485156529 : ((((p5 ∧ p3) ∨ (((True → False) ∨ (p1 ∨ p4)) ∨ p4)) → (p3 ∨ (p1 → (p2 → ((p3 ∧ ((p3 → p2) ∨ p4)) ∨ (p2 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171918762820853312621553979269 : (((p4 → (True ∨ (((p2 ∨ (p3 ∨ False)) ∨ ((p1 → True) ∨ p1)) → True))) → p5) ∨ (False → ((p5 ∨ (p4 ∨ ((p1 → p5) → p5))) ∧ p3))) := by
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
theorem thm_5_vars_191168527587747577734868290959 : (((False ∨ (p3 ∧ p3)) ∨ (p3 ∨ (False ∧ (p5 ∨ p3)))) ∨ (((True ∨ ((p4 ∨ p1) ∨ p1)) ∨ (((p5 ∧ p4) ∨ (p1 ∨ p5)) ∧ p1)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135090330625919348065657106037 : ((((((p4 ∧ (p5 ∧ ((True ∨ p2) → p4))) ∧ True) ∨ p5) ∨ ((p4 → p2) ∨ (p1 ∧ (p3 ∨ p3)))) ∨ (p4 → True)) ∨ ((p1 ∧ p2) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159079133279341120311087766025 : ((True → ((((p4 → p1) ∨ False) ∨ ((p2 ∧ (p4 ∧ (p4 ∨ (p4 ∧ (True ∨ True))))) ∨ p3)) ∧ p5)) ∨ ((((True → True) ∧ False) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309571804492973637627975935070 : (p2 ∨ ((((p2 ∨ p1) ∧ False) ∨ (((False ∨ (False ∧ ((p4 ∧ p3) ∧ p2))) ∨ (p3 ∧ (p5 ∨ p1))) → (p2 ∨ True))) ∧ ((p5 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208004747115127097399232171081 : ((((True ∧ p1) → p5) ∨ (p5 → p1)) → (((p4 ∧ (p2 ∧ p4)) ∨ ((False → p3) ∨ (p2 ∨ (((False → p1) ∧ p4) → p5)))) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730267727063332636149118766591 : (((((p3 → True) → True) → ((False ∧ (p4 ∨ (p5 ∧ (((p1 ∨ p3) ∧ p4) → ((p5 ∧ ((p2 ∧ p2) ∧ True)) ∧ p4))))) ∨ (True ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40473418955427736231690985882 : (((((p2 → (p4 ∧ False)) → (p5 ∧ ((True ∧ ((p4 → (False ∧ ((p3 ∨ (True ∧ p1)) ∨ False))) ∧ p2)) ∧ (p3 ∧ p5)))) ∨ p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191604199302132061281547044098 : ((p3 ∧ (((((True ∧ False) ∧ p4) ∧ p5) → p2) → p3)) ∨ (p1 → ((True → ((False ∧ p5) → p3)) → (p1 ∧ (True → ((p3 → p1) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783907814374874939870921964422 : (((p3 ∨ (((p2 → p2) → p5) ∨ ((p5 ∨ (p4 ∧ (p1 → p2))) ∨ ((p1 ∨ (True ∧ p5)) → ((p1 ∨ (False ∨ (p4 → True))) ∨ True))))) ∨ p5) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676011325392222480821729643942 : ((((((((p1 ∨ (p2 ∨ p3)) ∨ p5) ∧ p1) ∧ p3) → ((p4 ∧ ((p1 ∨ p5) → (p3 → p5))) ∧ False)) ∧ (p5 → (True → (True ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183769859260151362390793721169 : (((((p1 ∨ ((False → False) → (p1 ∧ False))) ∧ p5) ∧ p1) ∧ False) ∨ ((p5 ∨ (p2 ∨ ((p1 ∧ True) ∧ (p2 ∧ p4)))) → (p1 → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600181573911088413203915309431 : (((((False → False) → (p2 ∨ (False ∨ (((p2 ∧ True) ∨ ((p5 → (False ∨ ((p5 ∧ p1) ∨ p5))) ∨ ((p1 ∧ p1) ∨ p5))) ∨ p5)))) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348751517723612464232565574787 : (p3 → (False ∨ (((p3 ∨ p4) ∧ ((p3 ∧ p1) ∧ ((True → False) ∧ p2))) → ((True ∧ (((p2 ∧ p5) ∧ True) ∨ ((False ∧ p4) ∧ p3))) ∨ p5)))) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h16.left
    let h20 := h16.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h22 := h19 h21
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43583557080080995030651123392 : ((((((((((False ∨ (p2 ∧ (((p2 → p1) ∨ p2) ∨ p2))) ∧ p4) ∧ False) ∧ p4) ∧ False) ∧ ((p4 ∨ False) ∧ p4)) ∨ True) → False) → False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((False ∨ (p2 ∧ (((p2 → p1) ∨ p2) ∨ p2))) ∧ p4) ∧ False) ∧ p4) ∧ False) ∧ ((p4 ∨ False) ∧ p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213114784957015790841620375447 : ((((p4 ∨ p4) ∧ p4) ∧ p4) ∨ (p3 ∨ (((p2 ∨ ((p1 ∧ p5) → ((False ∧ ((p5 ∧ p5) ∧ (False ∧ p5))) → True))) → p1) → (p2 ∨ True)))) := by
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
theorem thm_5_vars_136436268229405636780147377056 : ((((p4 ∧ p3) ∨ (p5 ∧ p2)) → (((p5 ∧ ((p2 → (((p3 ∧ p4) ∨ (p3 ∨ p5)) ∨ p2)) → p3)) ∨ False) → p4)) ∨ (False → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69116710164047356459938478844 : ((p5 → ((((p2 ∨ (True ∧ (False ∧ False))) ∨ (p1 → (False ∧ p1))) → (((p3 ∨ False) ∨ (p5 ∧ (p3 ∨ p5))) ∨ True)) ∨ (p3 ∧ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105110204748490493328424108899 : ((((p1 → (p2 ∨ (p3 ∨ ((False ∨ (p5 ∧ False)) → (((p5 → True) → (False ∨ p1)) ∧ False))))) → p5) ∨ (p3 → (p5 ∨ True))) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345609994052818076776859494579 : (p3 → (((p3 ∧ p3) → (((((True ∨ (((False ∨ p2) ∧ (p1 ∨ (p3 ∨ (p2 → (p1 ∧ True))))) ∨ p4)) → p4) ∧ p3) ∧ False) ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136044365031286425080537147775 : (((True → (p2 → ((True ∨ p5) → (False ∨ (p3 ∨ True))))) → ((True → (((p5 ∨ (p4 ∧ True)) ∧ p3) ∨ p5)) → p2)) ∨ ((p4 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113566391011688405923641207467 : ((((p4 → p1) ∨ (((p5 ∨ ((p2 ∨ (((False ∧ p1) ∨ (p1 ∧ True)) ∧ True)) ∧ (p3 ∧ p1))) ∨ p4) ∧ p3)) ∨ (False ∧ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223953409965320603556632635057 : ((p4 ∨ (False ∨ True)) ∧ ((p1 ∧ p2) ∨ (((False ∧ ((p4 → (p5 → p1)) → ((False → (p3 → (p4 → p3))) → p4))) ∨ (True → False)) → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263563490006499171037277528324 : (True ∧ (((p4 → (((p3 ∨ ((((p5 ∧ p3) ∨ p1) ∧ (p4 ∨ p2)) ∧ p2)) ∧ p1) ∧ p5)) → (p2 ∧ False)) ∨ (p1 → (True ∧ (p2 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219119443195070511395779455216 : ((True ∨ (True ∧ (True → p4))) → ((((((p3 → False) ∨ p2) → (p3 → p4)) → (((p1 → True) ∧ (p3 → (p5 ∧ True))) ∧ False)) → False) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44723891266228500727901068702 : ((((((True → p2) → p5) ∧ p5) ∨ ((((False ∨ p4) ∧ (((p4 ∧ p3) ∧ p5) → True)) → (p1 ∨ (p4 → (p4 ∧ p3)))) → p5)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598958987833288767626137954051 : (((((p1 ∨ p4) ∧ ((p5 ∧ (((p1 ∧ False) ∧ ((True ∧ ((p3 ∨ ((p4 ∧ p2) → True)) → p5)) ∨ (p5 ∧ p2))) → False)) ∧ p3)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134278985628795803577119159964 : ((((p4 → False) ∧ (p5 ∧ (False ∨ (p1 ∧ (p2 ∧ (((p2 → (((False → False) ∧ p3) ∨ False)) → False) ∨ True)))))) ∨ p4) ∨ (True ∨ (p3 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46971107108250517004571068913 : ((((((((p4 ∨ p3) ∧ (p3 ∨ (((p4 → False) ∨ ((p4 ∧ False) ∨ p2)) → True))) ∧ p5) → (True → p4)) → p4) → p2) ∨ (True ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356209299759527319104511317631 : (p5 → ((True → ((((p3 ∨ True) → (p5 → p3)) ∨ (p1 ∧ ((p1 ∧ p3) → (p1 ∨ p3)))) ∨ p1)) → ((p4 ∨ (p5 → p1)) ∨ (p3 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46850581057911094205952089348 : (((((p1 → p5) ∧ (p3 → (((p4 ∧ p3) ∧ (p3 ∨ (p1 ∨ p2))) ∨ (((p5 ∨ (p4 → p1)) ∨ False) ∧ p3)))) ∧ p4) ∨ (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150660767919334950006113610742 : (((p4 ∨ ((p4 ∧ ((((p4 → p2) → p1) ∨ p2) ∧ ((p4 ∧ p3) ∨ ((p1 ∨ p3) → False)))) → p1)) ∧ p5) → ((p5 → False) ∨ (p4 → p4))) := by
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
theorem thm_5_vars_601936047783990826613648744271 : ((((p4 ∧ (False ∨ ((p5 ∧ (((p4 ∨ p3) ∨ (p3 → (p1 ∨ p1))) ∨ (True ∧ (p3 → p2)))) ∨ (((p3 ∨ p5) ∨ p5) → p5)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47539288989028661093393195115 : (((p5 ∨ (((((((p1 ∨ (p2 → (p2 → False))) → (p4 ∨ False)) ∧ p4) ∨ p2) ∨ ((p1 ∧ False) ∧ p4)) ∧ p5) ∨ True)) ∨ (p2 ∧ p5)) ∨ p1) := by
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
theorem thm_5_vars_645695563495958773332149350449 : ((((p5 ∨ (((True ∧ (p1 ∨ (p1 ∧ (p5 ∨ p3)))) ∧ ((p4 ∨ p3) → (p5 ∨ p5))) ∨ (((p5 ∧ False) ∨ True) ∨ (p3 ∨ p5)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133802423527505390333548418623 : ((((True ∨ (p4 → p5)) → (((False ∨ (((p1 → (p4 ∧ False)) ∧ (p3 → True)) ∧ p3)) ∨ (p2 ∨ False)) → p4)) ∧ p1) ∨ (p2 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790248325842677606945037434766 : (((p5 ∨ (p1 ∧ (((p1 ∧ (p2 ∧ ((p5 ∧ ((p4 ∨ ((p2 ∨ (p2 ∧ (p2 ∧ p5))) ∧ p4)) ∨ False)) ∨ p3))) ∨ p2) ∨ (p1 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614084396391077288017228879950 : (((((p1 ∨ ((p2 ∧ ((False ∨ True) ∧ (p2 → p5))) → ((((p1 ∨ p4) ∧ (True ∧ p4)) ∨ p4) ∨ p5))) ∨ ((p3 ∧ p5) ∧ p1)) ∨ p5) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264298997028155571321934967747 : (True ∧ ((((p1 ∧ (p1 ∨ False)) ∨ p1) → p4) → (((p2 ∧ (((p2 ∨ ((p2 ∧ p5) → p3)) ∨ (p1 → True)) ∧ (False ∧ False))) ∨ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304697074506782629227505641088 : (p1 ∨ (((((((((p4 → (False ∧ p3)) ∨ p5) ∧ True) ∧ p4) ∧ p1) → ((False ∨ (p5 → (True ∧ p3))) → p5)) → p3) → p1) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37200395563106084259585617717 : (((((p4 ∧ (p5 → (p1 ∨ (False ∧ p1)))) → (p2 ∨ ((p5 ∨ (True → (((p3 ∨ p5) ∨ False) ∧ (False → p2)))) ∧ p3))) ∧ p3) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688993176197011531545440526142 : ((((((p4 ∨ (p5 ∧ ((((True → (p3 ∨ p5)) → p1) → p5) → p3))) ∨ p1) ∨ p3) ∨ ((p5 ∨ ((p1 ∧ p5) → (False ∧ p4))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694734253988295550917535488813 : ((((p3 ∨ (False ∧ (((p1 ∨ p4) → p5) → (p2 → (p2 ∧ (p1 ∨ False)))))) ∨ ((p1 ∧ (((p2 ∧ p1) → (p4 ∨ p3)) ∧ False)) → False)) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313971302056329525700240094708 : (p3 ∨ (((((True → p2) → ((p1 ∨ True) ∨ ((p1 ∨ p2) ∨ (True ∧ p3)))) ∧ p1) ∨ ((False → p5) → (p1 ∧ (False ∨ True)))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209308341859930921386427913535 : ((True → (p4 ∨ (True → (p1 ∨ p5)))) → ((True ∧ p2) ∨ ((p5 ∨ False) ∨ ((((p3 ∧ (True ∧ p2)) → p2) → p2) ∨ (p1 → (False → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114895643956629859656464361671 : (((p4 ∨ ((p5 ∧ p1) ∨ ((p1 → ((p3 ∧ p1) ∧ (p2 ∨ False))) ∧ p3))) ∨ ((p3 ∧ (p1 ∧ True)) → (False → (p2 → p3)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201324753954347216178367465790 : ((p5 → ((True ∨ ((p2 → p2) → p2)) ∨ p3)) → (((((((p2 → p4) ∧ p1) → p2) ∨ ((p3 ∧ p5) ∧ p5)) ∧ p4) ∨ p1) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606129533292290066891518457505 : (((((((p1 ∨ (((p3 → (p5 ∧ p2)) ∧ p3) ∨ (p3 ∧ (((False → (p4 → (p1 → False))) → p5) → p2)))) ∧ False) ∧ p4) ∧ False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228093782528528373475010541289 : ((p4 ∧ (p1 ∨ p1)) ∨ (p2 ∨ (((p5 → (p5 → (p4 ∨ ((((True → p3) → p5) ∧ (p4 ∧ p5)) → True)))) ∨ (p5 → False)) ∨ (p5 ∧ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42862863294367108076420029901 : (((p2 → ((p3 ∧ ((p4 ∨ p5) ∨ p2)) ∨ (((p5 ∧ False) ∧ (False ∧ False)) ∨ (((False ∨ False) → (p3 → p2)) → (p3 → p2))))) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_486734444359651185850975888072 : ((((p3 ∨ (p5 → ((p2 ∨ p1) ∧ p1))) ∨ (p2 ∨ (((p5 ∨ ((((p3 ∨ True) ∨ (p3 ∨ p1)) ∨ (p2 ∨ False)) ∨ p1)) → False) → False))) ∧ True) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((((p3 ∨ True) ∨ (p3 ∨ p1)) ∨ (p2 ∨ False)) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171450359069415846542641771202 : (((p2 ∧ ((False → p3) → (((True ∧ ((p4 ∧ p5) ∨ False)) → True) → p3))) ∧ True) ∨ (True ∨ ((((True → True) → p5) ∧ p1) ∨ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251889233047967162016975872454 : ((p3 → p5) ∨ (True → (p3 ∨ (p4 → (((p3 ∨ ((((p5 ∨ (p3 ∧ p2)) ∨ ((p1 ∧ True) → False)) ∨ True) → p2)) ∧ False) ∨ (p5 → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240016858166127386797491727143 : ((p4 ∨ True) ∧ ((((p5 ∨ (False ∧ ((p4 → p2) ∨ False))) → (p4 ∨ ((True ∨ p5) ∧ p1))) ∧ (False → p4)) → ((p2 ∨ (p5 ∨ False)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134998492027918737301360012169 : (((p2 ∧ (((p4 ∨ p4) ∨ p3) ∨ (p1 ∨ (p2 → (p2 ∧ (((p5 → True) → (True ∨ True)) → p5)))))) ∧ (p5 ∨ False)) ∨ ((True → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313586283648620515151687191702 : (p3 ∨ ((((((p1 ∧ p5) ∧ (True ∨ False)) → p5) → ((p1 ∧ True) → True)) → (((((p2 → p1) → p3) → p5) → True) ∧ (False ∨ p4))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ p5) ∧ (True ∨ False)) → p5) → ((p1 ∧ True) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123743102236930391285886670725 : ((((p3 ∨ p3) → ((False → p5) ∧ ((p3 ∧ p2) ∧ (p1 ∧ (p3 → p3))))) ∧ ((False → ((True ∧ (p2 → True)) ∨ p5)) ∨ False)) → (p2 → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178065952771053546322892054309 : (((((p2 ∧ (p1 ∨ p4)) ∧ (p3 ∨ (p3 → (True ∧ True)))) ∨ False) → p1) ∨ (p1 → (((((p1 ∧ p5) ∧ (True ∨ p4)) ∧ p4) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213078867819828674657577227749 : ((((p2 ∧ True) ∧ p1) ∧ p4) ∨ ((((p1 ∧ (p5 ∧ (p5 ∧ False))) ∧ (p3 ∨ p3)) ∧ p4) ∨ ((((True → p5) ∧ p1) ∨ (p2 ∧ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644178106615839466419745382484 : ((((True ∨ (p1 → ((p3 → True) → ((((p5 → (True ∨ p1)) → p5) ∨ (False ∨ (p1 ∨ (p5 ∨ ((p5 ∧ p4) ∧ p1))))) ∧ p4)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156712471784482504036300872459 : ((((False ∨ (((False → p1) ∨ (False ∧ True)) ∧ (p2 → p5))) → (((p2 ∧ p1) → p1) → False)) ∧ False) ∨ ((False ∨ ((True ∧ p5) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61353352361648627606684275456 : ((p1 ∧ (((((p1 → False) ∨ False) → p3) → ((p3 ∧ (p5 ∧ (p2 → (((p4 → (p2 ∧ (p5 ∧ False))) → p4) → False)))) ∨ p4)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214568966282359968176497340660 : (((p2 ∨ False) ∧ (p3 ∨ p1)) ∨ (p2 ∨ (True ∨ (p4 → (((((p3 ∨ p1) → ((p5 ∧ False) → p5)) ∨ ((False ∨ p1) ∧ False)) ∧ p1) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244650993283642042324398082304 : ((False ∧ p5) ∨ (True ∧ ((p1 ∨ p2) ∨ (((p3 ∨ p4) ∨ True) ∨ ((p5 ∨ p4) ∨ ((p1 ∧ ((p5 ∧ ((p4 ∧ p4) → p3)) ∨ p3)) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_173783650490162231964250162553 : ((((p1 → False) ∨ ((True → (p2 ∨ ((p2 ∧ p3) ∧ (p3 ∧ p5)))) ∧ p2)) ∨ p3) → ((p5 ∧ (p1 ∨ ((p3 ∨ p4) → (p3 ∨ p1)))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
theorem thm_5_vars_50621025602233157646639048649 : ((((True → (((True ∨ True) ∧ (p5 → ((False ∧ (p3 ∧ p3)) → p3))) ∧ False)) ∧ ((True ∨ p1) ∧ p2)) → ((p4 ∨ p3) ∧ (False ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147395682052251478961916031703 : ((((False ∨ (((p3 ∨ p4) ∨ True) ∨ (p2 ∧ p1))) → ((p1 ∧ (((False → p5) → p1) ∧ p2)) ∨ p4)) ∨ p2) ∨ (p2 → ((True ∧ p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199978738397261259252214773879 : ((((p2 ∧ (p4 ∨ p2)) ∧ p1) → (p5 ∨ p2)) → ((((((p4 ∧ (p2 ∧ p4)) ∧ p4) ∨ (p1 ∨ p1)) ∨ p2) ∨ (p4 → (p1 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265758714755606074219919596027 : (True ∧ (p4 ∨ ((p4 ∨ (((p3 → p4) ∧ (p1 → ((True ∨ p4) ∨ (True ∧ (p2 → False))))) ∨ (p2 ∨ ((p1 → p1) ∧ (p5 ∧ p2))))) ∨ True))) := by
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
theorem thm_5_vars_134125847250847449455486146926 : ((((p3 ∧ (p5 → ((p2 ∨ p5) ∧ (p3 ∨ (p3 ∨ ((((p4 → False) ∨ p5) ∧ p2) ∨ False)))))) ∨ (p1 ∧ False)) ∨ p5) ∨ (True ∨ (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50841532246613431303175599880 : ((((p1 ∧ (((p1 → True) ∧ p1) ∨ (((((p5 → p1) ∨ p2) ∧ p4) ∧ p4) ∨ p2))) ∧ False) ∧ (((p1 ∨ (p5 ∨ p4)) ∨ p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264948114095841758945517794542 : (True ∧ ((False ∨ p1) → (((p3 → (((True → (p4 ∨ True)) → (p4 → (p2 ∧ True))) → p5)) ∨ (False ∨ (p5 → (p5 ∨ p4)))) ∨ (p2 ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642713827249229136019856599593 : ((((p1 ∧ (((False ∧ p2) ∨ p3) → (p5 ∨ (p3 ∨ (((p1 ∧ p4) → (p1 ∧ p3)) → ((p1 ∨ False) → (p2 ∨ (p1 → p5)))))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111554813946213716815527553832 : (((((False ∨ (p5 ∧ ((True → p3) → (p2 → ((p1 ∧ True) → (p4 ∨ p2)))))) ∧ ((True ∨ (False ∨ p2)) ∧ p1)) ∧ False) ∨ True) ∨ (p5 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216985263368409884894457756305 : (((p4 → (p1 ∨ p3)) ∧ p2) → (((p3 ∨ (p5 → ((((True ∧ (True → p1)) → p3) ∨ (p1 ∧ p5)) → p1))) ∨ p2) ∧ ((p3 → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_515321791062594002198437458411 : ((((True → p5) ∨ ((p1 ∧ (False ∨ ((p5 ∧ p3) ∧ (True ∧ (((True ∧ (p5 ∨ True)) ∧ (p5 ∨ (p3 ∧ p3))) ∧ (p3 ∧ False)))))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198330363292784396815708176526 : ((p2 ∧ ((p1 ∨ (False ∨ (p3 ∨ p2))) ∧ False)) ∨ (p1 ∨ (((((((p2 → p5) → p5) ∧ p4) ∨ p3) ∨ False) → (p2 ∧ (p1 ∧ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177961035182834046701357279384 : ((((p2 ∨ False) ∨ (True → (p1 ∨ ((p1 ∨ False) ∨ (p4 ∧ p2))))) ∨ True) ∨ ((((p4 ∨ ((p1 ∧ p4) ∨ (p1 ∨ p4))) ∨ p5) → p5) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226822963993949879507353045369 : (((p4 ∧ True) → p1) ∨ (p2 ∨ (True → ((p3 ∧ (((False ∨ (p2 ∧ p2)) ∨ (True → ((p4 → p5) ∧ True))) ∧ p1)) → (p5 → (p5 ∨ p4)))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40898388363165706707027438595 : (((((p2 ∨ True) ∧ ((True ∨ (False → (True ∨ p2))) → ((True ∨ (False ∨ (((False ∨ p2) ∧ p5) ∨ p3))) ∧ p3))) ∧ (p5 ∧ p4)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148842650982862990128768742971 : (((((p3 → p4) → False) → p5) ∧ (((p4 → p2) → False) ∨ ((True ∧ ((p2 ∧ p3) ∨ p4)) → (p2 → p5)))) ∨ (p3 → ((p1 ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118248088002461811778504346611 : ((p1 ∨ ((p3 ∨ (((p1 ∧ (((True ∨ (True ∨ p3)) → p5) ∨ True)) → p3) → (((p3 ∧ p3) → p2) → p4))) → (p2 → p5))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41666859349708873807392136082 : (((((True ∨ ((p4 ∧ p2) → p3)) ∧ False) ∨ (p2 ∧ (False ∨ (((p3 ∨ False) ∨ (((p4 ∨ p1) → p5) ∧ (True ∨ p2))) → False)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242570290405599816336158521584 : ((p3 → True) ∧ ((p2 ∧ (p2 ∧ (p2 ∨ (((p2 → p2) → p3) ∨ (False ∨ (p2 → p2)))))) ∨ (((False ∧ p4) ∧ (p3 ∨ (p1 → False))) → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137941959227935765318782988388 : ((p5 ∨ ((((p2 ∧ (False ∨ (True → (p1 ∧ ((p5 ∨ p3) ∨ (p2 → p4)))))) ∨ (False → (p3 → p3))) → p5) ∧ p3)) ∨ (False → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38059600882868252266948899103 : ((((((p1 → ((((p4 ∧ True) → True) ∨ p3) → ((p2 ∧ p1) ∨ p2))) → True) ∨ (((p3 → p2) ∧ False) → p1)) → (p4 ∨ p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300973168238567291140147160441 : (False ∨ ((True ∧ ((((p2 ∧ (p4 ∧ p3)) ∨ (True ∧ p5)) → True) ∧ False)) ∨ (((True → p3) ∨ (p5 → p5)) ∧ ((p5 ∨ p5) ∨ (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351207093978038426934738053410 : (p4 → ((((((False ∨ ((p2 → (p5 ∨ True)) → p5)) ∧ True) → (p5 ∨ (p3 ∧ (p5 ∨ p2)))) ∧ (p5 → True)) ∧ True) ∨ ((p3 → p3) ∨ p1))) := by
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
theorem thm_5_vars_42378537043098311785396985521 : (((p4 ∧ ((p3 → (((((p3 → (p1 → (p4 ∧ p1))) → p1) ∧ p5) → p3) ∧ ((p5 ∧ (p3 → (p5 ∨ False))) → True))) → p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55490373949220070170210304761 : (((((p4 ∨ False) ∨ False) → (p3 ∧ p1)) → (p5 → ((True ∧ (p4 → ((p1 ∧ (p3 ∨ p1)) ∨ (p3 → (p1 ∨ (p1 ∨ p4)))))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317615753930742136451507896488 : (p4 ∨ ((((p1 ∨ ((p1 ∧ (p4 ∨ (((((p1 → p2) ∧ (p3 ∨ (p1 → (p4 ∧ p3)))) ∧ p5) → p2) ∨ False))) ∨ p1)) ∧ p1) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137100971574288738269702775025 : ((True ∧ ((p5 ∧ ((((p5 ∧ (p1 ∨ p1)) ∧ (False → p1)) ∧ (True ∨ (False ∧ (p5 ∨ p5)))) ∧ True)) ∧ (p3 → p5))) ∨ ((p3 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654405858816244069620138723943 : ((((((False ∧ ((p4 ∧ p4) ∧ True)) ∧ (((p1 ∧ (False ∧ (True → True))) ∧ p4) → (p1 ∧ ((p1 ∧ False) ∨ p5)))) ∨ p1) ∨ (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159377406439522111514070010981 : (((((((False → True) ∨ p5) ∧ p5) ∨ (p4 → (False ∧ (((p4 → p4) ∨ False) → p1)))) ∨ False) ∧ p2) → ((p1 → ((True ∨ False) ∧ p3)) ∨ p2)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337354005138667572279274010247 : (p1 → (((p3 ∨ (p2 ∨ (((p3 → p2) ∨ ((((True ∨ True) ∨ p1) → (True → (p2 ∨ p1))) → p2)) ∨ p4))) → p3) ∨ (p5 → (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305001901228593950644626700898 : (p1 ∨ ((((((False → True) ∨ (p1 ∧ (True ∧ (p2 ∧ (False → p5))))) → p5) ∧ p2) ∧ (p4 ∧ (False ∨ (p1 ∨ p3)))) ∨ (True → (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229216079796321211625385966025 : ((True → (p4 → p5)) ∨ (p3 → (((((p5 ∨ (p1 ∨ (((p2 ∧ (False ∧ p2)) ∧ ((True ∧ False) ∧ p4)) → p5))) → p4) ∨ True) ∨ p2) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127874942333713515586400984698 : ((False → ((((((p2 → p5) → False) → (True → ((True → True) ∧ (p1 ∧ ((p5 → p2) → p4))))) ∧ p4) ∧ True) ∧ (True → p2))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



