variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133778727462583294212801625834 : ((((((p3 ∨ True) → p2) ∨ p4) → (p1 ∧ ((p1 ∨ False) ∧ (((p2 ∨ p1) ∧ ((p4 ∨ p2) ∨ p5)) ∧ p4)))) ∧ True) ∨ (False → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132707223158686010010399382992 : ((False ∨ (p2 ∨ ((p2 → True) ∧ (((p3 ∨ (p4 → ((p2 ∧ p2) ∧ p5))) → (p4 ∨ ((False ∧ p2) ∨ True))) ∨ p5)))) ∧ (p2 → (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64892897808719983278870048141 : ((p2 ∨ ((True ∧ (((p2 → (p2 ∧ (((((True ∨ True) → True) ∧ False) ∧ p2) ∨ p2))) ∧ (False → p4)) ∧ p2)) ∨ (False ∨ (p2 ∨ True)))) ∨ False) := by
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
theorem thm_5_vars_16571772533313565919009017821 : ((((((p2 ∧ True) ∨ ((((p4 ∨ True) ∧ p1) ∧ (p2 ∨ False)) → (p3 ∨ p3))) ∨ ((p4 → False) ∨ False)) ∧ p2) ∨ (p4 ∨ (p3 ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_57412233595426756851324424114 : (((p1 ∨ (p5 ∨ p3)) ∨ (True → ((True ∨ p2) ∧ ((((p1 ∨ (p1 ∨ p4)) ∨ p2) ∨ (((p5 ∧ (p5 ∨ p5)) ∨ p3) ∧ False)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149772836865985209689665493939 : ((False ∨ ((True ∧ ((((False → (False → False)) → (p5 ∨ ((p1 ∧ p4) ∧ p2))) ∨ p4) → (p4 ∨ p2))) ∨ p3)) ∨ (p3 → ((p5 ∧ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214762472171475790753293895434 : (((p5 ∧ p4) ∨ (p1 ∨ p1)) ∨ ((((((p2 ∧ False) → (p5 ∧ p3)) ∧ (p3 ∧ True)) → True) ∧ p1) ∨ ((False ∧ ((p3 ∧ p2) ∧ p4)) → p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171596529054008353810936481554 : ((((p5 ∨ ((p2 ∧ ((p3 → False) ∨ p4)) ∧ p1)) → ((p4 → p2) ∧ p4)) ∨ p3) ∨ (((True ∧ p5) ∨ p5) ∨ (True ∨ ((p5 → p2) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300407589974355398459318316530 : (False ∨ ((p1 ∨ ((((p5 ∧ (True ∧ p2)) ∨ p2) → (p1 → (p1 → p4))) → ((p3 ∨ (p1 → (p1 ∧ True))) ∧ p5))) ∨ (p5 → (p4 → p5)))) := by
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
theorem thm_5_vars_51465195871503191293498900864 : ((((((p2 ∨ (p4 → (True ∨ False))) → (False ∧ False)) → p2) → (p3 ∧ ((False ∧ p4) ∨ p2))) → (((p2 ∨ True) ∧ (p2 ∨ p2)) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ (p4 → (True ∨ False))) → (False ∧ False)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p2 ∨ (p4 → (True ∨ False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700761796453301844899350562570 : ((((((False ∧ (False ∧ (p4 ∧ p3))) ∨ (p5 ∨ True)) ∧ p1) ∧ (p1 ∨ (((((p3 ∨ (p4 → p3)) → (p1 ∧ p1)) ∨ p5) ∧ p2) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233808212933069326611197289268 : ((p3 ∨ (p2 → p3)) → ((p4 → ((((True → p1) ∧ p4) ∧ p3) ∧ p4)) ∨ (p4 ∨ (p4 → ((((p3 ∧ p5) ∧ False) ∨ False) → (p2 ∨ p4)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326239590743693031191635416697 : (p5 ∨ (p3 → (((p2 → (p1 → (p2 ∨ p4))) → ((((False → p1) → p1) ∧ (p4 ∧ p1)) ∨ False)) → (p5 ∨ (p2 ∨ ((p2 ∨ p1) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (p1 → (p2 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305897988211088129152461522322 : (p1 ∨ (((((False ∧ True) → p4) → p5) ∧ p2) → ((p4 → (((False ∨ p1) ∧ ((p1 ∨ p5) → p1)) ∧ ((p1 ∧ (p4 ∨ p5)) → True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_208588548669320981497132556368 : (((p1 → p4) → (True ∧ (p5 ∨ p2))) → ((p2 → (((p2 → ((p2 → (p3 → p2)) → p3)) ∨ (p2 ∨ (p2 ∨ (p1 ∨ True)))) ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255969426201790145269840398243 : ((True ∨ p3) → ((((((p1 ∧ ((p4 → p2) ∧ (p4 ∨ p2))) ∧ False) ∧ (True ∨ p3)) ∨ (True ∨ (p1 ∧ (p3 ∧ (p1 ∧ p5))))) ∨ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134135161183400416917115523275 : (((((((p5 → p4) → (False → p3)) → False) → ((p1 ∧ p1) ∨ (p2 ∨ ((p5 ∨ p3) ∧ False)))) → (p4 → p1)) ∨ True) ∨ ((False ∧ False) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54559005308530372055867401339 : (((p3 ∧ ((p2 ∨ p5) ∨ (True ∧ (p5 → False)))) ∨ ((False ∧ p3) ∧ (((p1 ∨ False) ∨ True) → ((p4 → (p2 → (False ∨ True))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345332264732590175560576343721 : (p3 → ((((False ∧ ((((True ∨ False) ∧ p3) ∧ True) ∧ p4)) ∨ (((((True → True) ∧ (False ∧ p3)) ∧ p1) ∨ (p4 → p3)) ∧ p2)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149633760464080112330853396569 : ((p4 ∧ ((p3 → (((False ∧ p2) ∨ (p5 ∧ (p5 → ((p5 ∨ (p2 → (True ∨ p2))) ∨ False)))) ∧ p2)) ∨ True)) ∨ (True ∨ (p2 → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350204276495127607072887462324 : (p4 → ((((p2 → p3) ∨ p5) → (((p4 ∨ (p5 → (p5 ∧ p1))) ∨ p3) ∧ ((p5 ∨ ((p3 ∧ (p5 ∧ p4)) ∧ True)) → (p3 → p2)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126092576403055096442333670756 : ((True ∧ ((p5 → ((False ∨ p4) → (False → ((p1 → (p5 → (((p2 → p5) → p3) → True))) → ((p1 ∧ p5) → p1))))) ∨ p3)) → (p3 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47589080292606629062304087233 : (((p2 → ((p4 ∧ (p3 → p5)) ∨ (((True → p4) ∧ (p4 ∧ (p3 ∨ True))) ∨ ((p4 → (p3 → (False → p3))) → p5)))) ∨ (p1 → p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226329479890617936439692459472 : (((p5 ∨ p2) ∨ p3) ∨ ((((p3 ∨ p1) ∧ (p3 → p3)) ∨ p2) ∨ (((((((p4 ∧ p5) ∧ True) → True) ∧ p3) ∨ p2) → False) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_4120800675951233723124494014 : (p3 ∨ ((p1 → False) → (p2 → (p4 → (True ∧ (True → ((((p5 ∨ False) ∧ False) ∨ p1) ∨ ((((p1 ∨ True) ∧ p3) ∧ p4) → True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320478687619567193385034337288 : (p4 ∨ ((p2 → p5) → ((((p5 ∨ p3) → p1) ∨ (p5 ∨ True)) ∨ (p3 ∨ (True → (False → (((True → p2) ∧ p2) ∧ ((p3 ∨ True) ∧ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327164199793712217761640827354 : (True → ((p5 ∧ ((p4 → p5) → ((p1 → (p3 ∧ (False → (((False ∧ ((p2 ∨ True) ∧ (False ∨ False))) ∧ p3) ∨ p3)))) → (p2 → p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257973611093623960447816315498 : ((p4 ∨ p1) → ((((p1 → p2) ∧ (((p5 ∧ (p1 → (False ∧ (False ∨ ((False → p3) ∨ (False → (p5 ∨ True))))))) → p1) ∨ p4)) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60240388466618755185513129750 : (((True → p5) → ((((False ∨ (p5 ∧ p3)) ∨ (True → (True ∨ (True ∧ (p3 → (p1 → (p3 → p5))))))) ∧ p1) → (False ∧ (p2 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137978668703233810658141937112 : ((p5 ∨ ((p5 ∨ ((p1 ∧ p4) ∧ p5)) ∨ ((p5 ∧ ((p4 ∨ p2) ∧ (((True ∨ (True ∨ True)) ∧ p4) ∨ p2))) → True))) ∨ (p4 ∧ (True ∧ p5))) := by
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
theorem thm_5_vars_173240067340778413763212591366 : ((True → (((True ∨ (p1 ∨ p4)) ∧ p3) ∨ ((p3 ∧ ((p1 ∨ p4) → p1)) ∨ p4))) ∨ ((p3 → p3) ∨ (((p5 ∧ p5) ∨ (p1 ∨ p1)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112475904967353911566512111644 : (((((p5 ∧ True) ∧ (((((p2 ∧ p4) → p3) ∨ True) ∨ (True ∨ ((p1 ∨ p1) ∧ ((p1 → p2) → p5)))) ∨ False)) ∨ p1) → p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1220436613909352489740283553 : ((True ∧ ((((p5 → p4) ∨ (p4 → (p3 ∨ p5))) → (((p2 ∨ False) → False) ∧ ((True → (True ∧ p3)) ∧ p2))) ∧ (p5 ∨ p3))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((p5 → p4) ∨ (p4 → (p3 ∨ p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : ((p5 → p4) ∨ (p4 → (p3 ∨ p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h13
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671062590256886218566626878322 : ((((False ∨ ((p3 ∧ ((p3 ∨ False) ∨ ((False ∨ ((p1 ∧ (p1 → False)) → (True ∨ False))) → p2))) ∨ (p1 ∧ False))) ∨ (p3 ∨ (True ∨ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339494991207627225522641630396 : (p1 → (False ∨ (((p4 ∨ False) ∧ ((p2 → (True ∧ (True → (p3 ∧ p3)))) → (((p5 → (True → (p2 ∧ p1))) → False) → p1))) → (p3 ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680930670976999139763364636793 : (((((p1 → p5) ∧ (p4 ∧ (p1 → (((False ∧ p5) ∨ ((False → (p2 ∧ (p3 → p2))) ∧ p3)) ∧ p3)))) → (p1 ∨ (p2 ∨ (p1 ∨ p4)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788208539833848256852979074461 : (((p5 ∨ ((True ∧ (((p4 ∨ ((p3 ∨ p5) ∨ p5)) ∨ False) ∧ ((((p4 ∧ p2) → p5) ∧ False) ∨ (((p1 ∧ p3) → p2) ∧ p5)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149151682015847498358338572580 : (((p1 ∨ True) ∧ (False ∨ ((((True → p1) ∧ ((((True → p5) → (p2 ∧ p3)) → True) ∧ p5)) → p2) ∨ p5))) ∨ ((False → (False ∨ p1)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66363240381174554075084309651 : ((p5 ∨ (False ∨ (p2 ∨ (((p4 ∧ True) → False) ∧ (((p3 → p2) ∨ ((p3 → False) ∧ p1)) ∨ (((p2 ∨ p5) ∨ (True → p1)) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337531103944388530091194113852 : (p1 → ((((p4 ∨ ((((((p1 → p2) ∧ p2) ∧ (True ∨ p3)) ∨ p2) ∨ p2) ∨ p3)) ∧ p5) → (p4 ∧ p1)) ∨ (False → ((p4 ∧ p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668223940896245593465656131228 : ((((p2 → ((p2 ∨ (p4 → ((p1 ∧ False) → p5))) → (((p3 ∨ p2) ∧ (p2 ∧ (p3 → p5))) ∨ (False → p2)))) ∧ ((p5 ∧ p1) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232916573816126927570353898196 : ((p3 ∧ (p5 ∧ True)) → ((p1 ∨ ((True ∨ (p2 → p4)) ∧ True)) → (p5 → (((((True ∨ (False ∨ p3)) ∧ (p3 ∧ p2)) ∨ False) → p1) ∨ p3)))) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156961879062603930809107203262 : ((((((p1 → (p5 → False)) ∨ (p5 ∧ p5)) ∧ ((p4 ∧ p5) → p4)) → ((p2 ∧ False) ∧ p4)) ∨ True) ∨ ((True ∧ p3) ∨ (p2 → (p5 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40767012790821285395401598161 : (((((p1 ∨ True) → (True ∨ (((((((False ∧ p2) → (((p4 → p2) → True) ∧ p2)) ∨ p5) ∨ p1) ∧ p3) → p4) → False))) → p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157868726053608217493429994035 : ((((False ∨ (p1 ∧ (p1 ∨ ((True ∧ p2) ∧ p4)))) ∧ p4) ∨ (((p5 ∨ True) ∨ p5) ∨ (p3 → p4))) ∨ ((True ∨ (True ∧ True)) ∧ (True ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_197304130320168905528126547149 : ((((False ∨ p3) ∧ ((p3 ∧ p1) → p2)) → p5) ∨ ((p5 → ((p1 ∨ p5) → (p2 ∨ ((p5 → (p4 ∨ (p2 → True))) ∧ True)))) ∨ (False ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156749205741166303432055136101 : ((((True ∨ (p2 ∨ p1)) ∨ ((p3 → ((p2 → p4) → ((p5 ∧ p4) ∧ False))) ∧ (False ∧ p4))) ∧ p3) ∨ ((p3 ∨ ((False ∨ p1) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134663231035706842834512369636 : ((((((False → (((p3 ∧ p4) ∨ p2) → p5)) → p5) ∧ p4) → (((p2 → (p4 ∨ False)) ∧ (p5 ∨ p4)) ∧ True)) → p1) ∨ (p3 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148109444629704228334207779850 : (((((p3 → p5) ∨ (((False ∨ True) ∧ True) → (p3 ∧ p1))) ∧ (p4 ∨ (True ∨ (p3 ∧ p4)))) → (p5 ∧ p3)) ∨ (p4 ∨ (p4 ∨ (False → p5)))) := by
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
theorem thm_5_vars_207288518882747915244203278511 : ((((p2 ∧ (p4 ∨ False)) → False) ∨ True) → ((((False ∧ p5) ∨ ((True ∧ True) → ((p4 → (False ∨ p2)) ∨ True))) ∨ p2) ∨ (p4 ∨ (p1 → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_984181068033835997733901196669 : (((p1 ∧ (p4 ∧ (p3 ∧ (False ∨ ((((((p3 ∧ ((p1 → True) ∨ p2)) → False) ∨ p1) ∨ p3) ∧ ((p2 ∨ (p5 ∨ p1)) ∨ p2)) → False))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (((((p3 ∧ ((p1 → True) ∨ p2)) → False) ∨ p1) ∨ p3) ∧ ((p2 ∨ (p5 ∨ p1)) ∨ p2)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249494677242246775320354820939 : ((p5 ∨ p1) ∨ (((p3 ∧ ((p4 → False) → False)) ∧ ((p1 → (False ∧ p2)) ∨ p4)) ∨ (False → (((((p1 ∧ p5) ∨ p5) ∨ True) ∧ p1) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693169868997164599538444464308 : ((((True ∨ (((((p4 → p2) → (p1 ∧ (True → p4))) → p2) → False) → p2)) ∧ (p4 ∨ (True ∧ ((((True ∨ p1) → p4) ∧ p5) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115997149714630433506339167150 : ((((p1 ∨ (p3 → False)) → False) → ((p5 → True) ∧ (p2 ∨ ((p4 ∨ False) ∨ ((((False ∧ (p1 ∨ p1)) → p1) ∨ p1) → p4))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234335217854264099883384960623 : ((p1 → (p5 ∧ p1)) → ((((True ∨ False) ∧ p5) ∨ p5) ∨ (((p2 → False) ∨ ((p1 → p2) → (True ∨ (p2 ∨ p3)))) ∨ ((True ∨ True) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197772747400917012981725272227 : (((True → (p2 ∧ p2)) ∧ ((p1 → p5) → p1)) ∨ ((p2 → p5) → (((p4 → p3) ∧ (p1 → p2)) ∨ (((p1 ∧ p1) ∧ (p3 ∨ False)) → p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51746934651075627065329180100 : ((((p1 ∨ (p5 ∨ False)) → (p3 ∧ ((p5 → (p5 ∧ True)) ∨ ((p3 → p3) → p1)))) ∧ ((((p3 → False) ∧ p5) ∨ (p1 ∨ False)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234677045896773724813279883067 : ((p4 → (p3 ∧ False)) → ((((p2 ∨ (p5 → ((((p2 → p2) ∧ (((p3 ∨ (p1 → True)) ∨ True) ∨ p4)) ∧ p1) ∧ True))) ∨ p2) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226387140431071318206407634269 : (((True → p5) ∨ p5) ∨ ((False ∧ (p1 ∧ (((p5 → (p5 ∧ (((p2 → p4) ∧ False) ∧ (p3 ∨ p1)))) → (True → p3)) → False))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112591942023044829485379052023 : (((((p4 → ((p3 ∨ (p2 ∧ True)) → p5)) ∧ (p1 → (p4 → ((True ∨ (p1 → True)) ∨ (True → p3))))) ∧ (p2 → p3)) → p5) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200045298107991208172031942161 : (((p1 ∨ (p5 → (p2 → True))) → (p1 ∨ p1)) → (p1 ∨ ((True → (((False ∨ (p3 ∨ (False ∧ p3))) → (p2 ∨ p4)) → p2)) ∧ (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (p5 → (p2 → True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150471380257795518462164879764 : (((((p2 ∨ (p1 ∨ p3)) ∨ (((p5 ∧ False) ∧ (True → (p1 ∨ (p5 ∧ p1)))) ∧ p3)) ∧ (p5 ∨ p3)) ∧ p4) → (p1 ∨ ((p4 ∧ p1) ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247303895788554322093476311946 : ((False ∨ False) ∨ ((((((p4 ∧ p4) ∨ p4) ∧ (True → False)) ∨ True) ∨ ((p3 ∨ ((p4 ∧ p1) → p4)) → p1)) ∨ (p1 ∨ ((False ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_208494128857999955712129888787 : (((False ∧ p3) → ((p2 ∨ p1) → p5)) → ((((p1 → p4) → (((p4 ∨ p5) ∧ True) ∨ p1)) ∧ (p2 → (True ∧ (p4 ∨ p5)))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184586130247643556669795192609 : (((p1 ∨ (((p5 ∨ p1) ∧ p4) ∨ (p2 → True))) → (True ∧ p5)) ∨ ((False → (p1 → (p2 ∨ (p1 ∧ p3)))) ∨ ((p2 ∨ p5) ∧ (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232031597591523091452040448781 : (((p3 ∨ p1) → p3) → (p4 ∨ ((p5 ∧ False) ∨ ((((False ∨ True) → p2) ∧ (p3 → (p1 ∨ ((p2 ∨ (p5 ∨ p1)) → (p1 → p3))))) → p2)))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123643068251355493735510911481 : ((((True → (((p1 ∨ ((True ∧ (p2 ∧ True)) → p5)) → True) ∧ (p5 ∨ True))) → p5) → ((False → ((p1 ∧ p4) → p5)) ∧ False)) → (p5 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True → (((p1 ∨ ((True ∧ (p2 ∧ True)) → p5)) → True) ∧ (p5 ∨ True))) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2202002584118287488286112132 : ((p2 ∨ ((False → True) ∧ (p5 ∨ ((((p5 → (p3 ∧ False)) ∧ p1) → p3) → p5)))) ∨ ((p4 → ((p4 ∧ (True → p1)) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_645253394987782024091641155904 : ((((p3 ∨ (p1 ∨ ((p5 ∧ (((p5 ∨ p5) ∨ ((p5 ∧ p4) ∨ (p4 ∧ (p2 → False)))) → (True → p2))) → ((False ∧ p4) ∨ p5)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351729829831097705567800890936 : (p4 → (((((p3 ∧ False) → False) → (False ∧ (True ∧ p3))) ∨ ((True ∧ p2) → p3)) ∨ (((((p4 ∧ p2) ∨ (p3 → p1)) ∧ p3) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225122591848626106141342827040 : (((p2 ∧ p5) ∧ True) ∨ (((p3 ∧ ((False ∨ ((False ∨ p5) ∨ (p1 ∧ p2))) ∨ False)) ∨ (p5 ∧ ((((p3 → True) → p2) → p3) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148125045732170449431408477943 : ((((p2 ∧ (True ∧ p5)) ∨ (((p4 ∧ True) ∧ (p1 → False)) → ((True → p5) ∧ (True ∧ p5)))) → (p1 ∧ p5)) ∨ (p3 → ((p3 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136546140558595837582918273874 : ((((p4 ∨ False) ∧ p1) ∨ (((p2 ∨ (p3 ∨ (p2 → True))) → (p1 ∧ ((((p2 ∧ p2) ∨ p5) ∧ p1) → True))) → p5)) ∨ ((p4 ∧ True) → p4)) := by
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
theorem thm_5_vars_219741521143980179596245398146 : ((p1 → (p2 → (p1 → p5))) → (((((p4 → p2) ∨ p4) ∧ True) → (((p2 → (p1 ∧ (((p2 → p2) ∨ p4) ∨ False))) ∨ p2) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142581257391649128618022583742 : ((False ∨ ((p4 ∨ (True → (((p5 → (p1 ∧ p3)) ∨ (p4 ∧ ((p2 ∨ False) → p5))) ∧ ((False → False) → p5)))) ∨ False)) → ((p3 ∧ False) ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756898930676871370603754775306 : (((p1 ∧ ((((p1 ∨ (p2 → p3)) ∧ p2) → p3) ∧ ((((p5 → p1) → p3) ∨ ((p4 ∨ (p1 ∧ p4)) ∧ ((p1 ∨ p1) ∨ p5))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198023509720753531737497972982 : (((p5 → True) ∧ (((p2 ∧ p2) ∨ False) ∨ p5)) ∨ (p3 ∨ ((p1 ∧ p3) → ((p2 → ((True ∧ (p3 ∨ ((p3 ∧ True) → p1))) ∨ False)) → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148687801942680471245051987177 : ((((False → p2) → ((p4 → p5) ∨ (p1 ∨ p1))) ∨ ((p2 ∨ p1) ∨ (((p4 ∨ False) ∨ p5) ∧ (p3 ∧ True)))) ∨ ((p5 ∧ False) → (True ∨ p5))) := by
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
theorem thm_5_vars_152220556601347282832877630907 : ((((p2 → False) ∨ ((True ∧ True) ∧ p1)) ∧ ((False → False) ∧ ((True → (False ∨ p5)) → (p1 ∨ (False ∧ False))))) → (((p3 → p2) ∨ True) ∨ p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257865577229698512499522607967 : ((p4 ∨ True) → ((p1 → (((((p3 → p2) ∧ (p2 → ((p3 ∨ p4) ∧ p3))) ∧ p3) ∧ (p4 ∨ (True ∧ False))) ∧ (p2 → p3))) ∨ (False → p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242594951016862283560571609710 : ((p3 → True) ∧ (p3 ∨ ((True ∨ (p3 ∨ (False ∧ p2))) → (((p5 ∧ p1) ∧ p1) ∨ ((((False → False) ∨ p4) ∨ (p1 → p5)) ∨ (p4 ∨ True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305618243702480533384042543036 : (p1 ∨ (((p3 ∨ (False → ((True ∧ p1) ∧ p1))) ∨ ((p2 ∧ p4) → p1)) → (p2 ∨ (((((p5 ∧ (p3 → p1)) ∨ p1) ∧ False) ∨ True) ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337138394743166586679410793191 : (p1 → ((p4 ∨ ((((p5 ∨ ((p5 ∧ (p2 ∨ (True → p3))) ∨ True)) → (p4 ∨ p5)) → p1) → (p3 ∧ (p3 ∧ (p4 ∧ p5))))) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310325510783018713126151152428 : (p2 ∨ ((((p2 → (p4 ∨ p5)) ∨ (p1 → (p3 → p2))) → p3) → ((((True → (p2 ∧ ((p3 ∧ p5) → p3))) ∨ (p2 → p5)) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_677461249761078899958213500191 : (((((((p4 ∧ (((p1 ∨ p2) → (True ∧ p5)) → p2)) ∧ p1) → (((p2 ∨ p5) → p2) → False)) ∨ p2) ∨ ((True → True) ∨ (p2 ∧ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349272772667129877271759357731 : (p3 → (p2 → ((((((p4 ∧ (((((p4 → (p4 ∨ p2)) ∨ p4) → (p1 ∨ True)) ∨ p2) → p5)) → p2) → (p3 ∧ p4)) ∧ p5) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641928986719740618326590400539 : (((((p3 → p3) → (((((p4 ∨ p1) ∧ True) → p3) ∨ (p5 ∨ p4)) ∧ (p2 ∨ (((True ∧ p1) ∨ (False ∧ (p1 → p1))) ∧ p2)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149952559453221628628659834481 : ((p4 ∨ ((((((((p1 ∨ False) → p1) → (False ∧ ((p4 ∨ p4) ∨ p3))) → True) ∧ p3) ∨ False) ∨ p4) ∧ p3)) ∨ (p4 → ((True ∨ p3) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156252729761244238229486208718 : ((p3 ∨ (p1 → ((((((p4 ∨ p4) ∨ False) ∧ True) ∧ p3) ∨ p1) ∧ ((False ∨ p2) → (False ∨ p1))))) ∧ (((p1 ∧ False) ∧ (p5 ∨ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125197768755272502675627507 : (((((p3 ∨ p3) → p5) ∨ ((True ∧ ((p2 → (((p1 → ((p1 ∨ p4) ∨ False)) ∨ p4) → p3)) → p3)) ∧ (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153399836343397678346251494464 : ((p3 ∨ (((p5 ∨ ((p4 ∨ False) ∧ (p5 → True))) ∨ p4) ∧ (p1 ∨ ((p5 ∨ False) ∧ (p5 ∧ (p4 ∨ p3)))))) → (((p2 ∨ p2) ∧ True) ∨ True)) := by
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
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h8 =>
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
            -- Conjunctions on the left can always be decomposed.
            let h13 := h11.left
            let h14 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h17 =>
            -- False on the left can always be used.
            apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h26 =>
              -- Conjunctions on the left can always be decomposed.
              let h27 := h25.left
              let h28 := h25.right
              -- Disjunctions on the left can always be decomposed.
              cases h28
              case inl h29 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h30 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h31 =>
              -- False on the left can always be used.
              apply False.elim h31
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h37.left
          let h40 := h37.right
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h42 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h43 =>
          -- False on the left can always be used.
          apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671050718703091341763533943600 : ((((False ∨ (((True ∧ False) ∨ (p1 ∧ (p2 ∧ (((True ∨ (((p3 ∧ p3) → p2) → p1)) ∧ p5) ∨ False)))) ∧ p1)) ∨ (p2 → (True ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150927086835134931804965219553 : ((((p5 ∧ p3) → (p2 → ((((p5 ∨ p2) ∧ p1) → p4) ∧ ((True → ((p3 ∧ p2) ∧ p5)) → p1)))) ∨ p1) → (((p2 → p1) ∨ True) ∨ p3)) := by
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
theorem thm_5_vars_220742306011022876986218925864 : (((p3 → p3) ∧ True) ∧ (((((True → (p5 → (p3 → True))) → p5) ∨ p2) ∨ ((True ∧ (p3 → (True → True))) ∧ (False → p3))) ∧ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167780263860958853657743438971 : ((((True ∨ (False ∧ p1)) ∨ (((True → (p1 ∧ p3)) → p4) ∨ p3)) → (p3 ∧ (False ∧ False))) → (((p4 ∨ (p4 → (True ∨ p3))) ∨ p3) → p1)) := by
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : ((True ∨ (False ∧ p1)) ∨ (((True → (p1 ∧ p3)) → p4) ∨ p3)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : ((True ∨ (False ∧ p1)) ∨ (((True → (p1 ∧ p3)) → p4) ∨ p3)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : ((True ∨ (False ∧ p1)) ∨ (((True → (p1 ∧ p3)) → p4) ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346600517069850985677480298568 : (p3 → (((p1 → (p3 ∧ (p2 ∧ ((False → p2) ∨ (p4 → (p2 ∨ (((p3 → p5) ∧ True) ∧ (p3 → True)))))))) → p1) ∨ ((False ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48851289214608708252898141263 : (((p2 ∨ ((True ∧ p1) ∧ ((p3 ∨ (False → (p2 → (((p1 ∨ p1) ∨ ((p2 ∨ p3) → p5)) ∧ True)))) → p3))) ∧ (p4 → (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150234116995293912747724529019 : ((p3 → ((((p1 → (p5 → (p4 ∧ p1))) ∨ (p1 ∨ (p4 → (p4 → p2)))) ∧ (p2 ∧ (p2 → p1))) ∧ False)) ∨ (p1 ∨ (False → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654509602861575779938269208433 : (((((p1 ∧ (p3 ∧ ((False ∨ (((p3 ∧ p1) ∧ False) ∨ (p3 → (True ∨ False)))) ∧ ((True ∨ p2) ∨ (p3 ∨ p1))))) ∨ False) ∨ (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54734743478512841705731536157 : ((((p1 → (p1 → p5)) ∨ (False ∨ (p2 → p3))) → ((p1 ∨ (((p5 ∨ p1) ∧ False) ∨ True)) ∨ ((((p4 ∨ p4) ∧ p4) → True) ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



