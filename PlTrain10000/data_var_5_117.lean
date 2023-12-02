variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337128394118683471530887731846 : (p1 → ((p5 ∧ ((p5 ∨ ((p1 ∧ ((p2 → p5) ∧ (((False → (((p4 → False) ∧ p4) ∧ False)) ∨ True) → p2))) ∧ p5)) ∧ p2)) ∨ (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691492175878972282287231143322 : (((((False ∨ True) → ((p5 → ((p3 → (False ∧ p3)) → ((p5 → p4) ∨ True))) ∧ p2)) → (p4 → ((((p5 → True) → p3) → p1) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668018823575578234664554244910 : ((((p4 ∨ (p1 ∨ (((p5 ∧ ((p2 ∨ (p2 ∨ (False ∨ (p2 ∨ (p4 ∧ False))))) ∨ p3)) → p3) ∧ (p3 → p1)))) ∧ ((p5 ∨ p2) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354081571211818300820462838638 : (p4 → (p5 → ((True ∧ (False ∧ (p2 ∨ ((p4 ∧ ((p2 → ((False → (p3 ∨ (False ∨ False))) ∧ ((p3 ∨ True) → False))) → False)) ∧ True)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822289499792815494231132010516 : (((((((True ∨ p2) ∨ (p5 ∧ (p2 ∧ p1))) → (p3 ∨ p1)) ∧ ((((p2 → False) ∨ (p3 ∧ p4)) → True) → ((p2 ∨ p5) ∧ False))) ∧ p5) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 → False) ∨ (p3 ∧ p4)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750348639757198286210821367169 : (((True ∧ (((p2 ∧ (p1 → (p5 ∨ p4))) ∨ (((((((p4 ∨ p1) → p2) ∨ p1) ∨ False) → (p2 ∨ False)) → False) ∧ p5)) → (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303939455058157754895219414093 : (p1 ∨ (((((p1 ∨ (True ∨ True)) → p5) ∨ p3) ∨ (p2 ∧ (((((True ∨ p3) ∧ ((p2 → (p4 ∨ p3)) ∨ p5)) ∨ p3) ∧ p2) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307192318355668813392621350794 : (p1 ∨ (p1 ∨ (((p5 → (p4 ∨ ((p3 → (p2 ∨ ((p3 → (True ∧ p4)) ∧ (p2 → (p4 ∨ False))))) ∨ True))) ∨ (p1 → p2)) ∨ (p1 → p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592655758195607196495490947582 : (((((p1 → ((((p5 → ((p5 ∧ (p1 ∧ p3)) ∨ ((p1 ∨ ((p5 ∨ p4) → p3)) → p4))) ∨ p3) → p4) ∨ p4)) → (p2 ∧ p5)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65100882397320365025620061331 : ((p2 ∨ (p3 ∨ ((p4 ∧ (((((p2 ∨ False) ∨ (p1 ∨ (((p5 → (False ∧ p3)) ∧ p1) ∧ p4))) → False) → p3) → (p5 ∧ p3))) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_305595110617364100221612433085 : (p1 ∨ (((p2 → p5) ∨ (p5 ∧ ((False ∧ ((p3 ∨ p4) → True)) ∨ p1))) ∨ ((p5 → (p4 ∨ (False ∧ p3))) ∨ (((p1 ∧ p3) ∨ False) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137092628512352912025081184982 : ((True ∧ ((p4 ∨ (False ∧ (((p2 → p4) ∧ p4) → (((False → (p1 → p4)) ∧ p2) ∧ ((p3 ∧ True) ∧ p5))))) ∨ p2)) ∨ (True ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471947718007348649584544999455 : (((((((p4 ∨ (p5 ∧ True)) ∧ p4) ∧ p3) → ((p1 ∨ False) ∨ p5)) ∨ (True ∨ (((((p5 → (p4 → True)) ∧ p3) → True) ∧ p4) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135433931624973429470413052075 : (((True → ((p1 ∨ (((False ∨ p4) ∨ p2) → p3)) → (p3 → ((p5 ∧ p1) → (p5 ∧ False))))) ∨ ((True → False) → False)) ∨ ((p1 ∧ p3) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_652373686258095887349598224597 : ((((p4 ∧ (((p5 → False) → True) ∧ (((((True → False) ∧ (p5 ∨ p1)) ∨ p3) ∨ ((p4 ∧ p4) ∧ (p5 → p5))) ∨ p1))) ∧ (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672843105961389142508145622793 : (((((((p2 ∧ (p3 ∧ (((p4 ∨ (p3 ∨ True)) → p4) ∨ (p1 → p2)))) ∧ True) ∧ True) ∨ (p3 ∨ (False → p1))) → ((p3 ∧ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313352993492668794673973969410 : (p3 ∨ ((p2 → ((((((True ∨ True) ∨ (p5 ∧ p3)) ∧ (p1 → (p5 ∧ p1))) ∨ ((True ∧ True) → (False ∧ (p4 ∧ p5)))) → p3) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172395409989934241458936564939 : ((((True ∨ True) → ((p3 ∧ True) ∨ False)) → ((p3 ∨ p4) ∧ ((p5 ∨ p4) ∨ p3))) ∨ ((((((p2 ∧ p2) ∧ False) → True) → p3) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124315174242213482728886082670 : ((((False ∧ False) ∨ (p1 → ((True → p4) → p4))) ∧ ((((p5 → (p4 ∨ True)) ∨ p4) ∧ (p5 ∨ (p1 ∧ (True → p4)))) → False)) → (p4 ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233411499594927336228079841391 : ((False ∨ (p2 ∨ True)) → ((p4 ∧ p5) ∨ (p5 → ((((((p3 ∨ p5) ∧ p4) → p2) ∨ (False → ((False → (True ∧ p1)) ∨ p1))) → p3) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41502624431235286793689438392 : (((((p5 ∧ p3) → (True → (((True → (True → p5)) ∧ p2) ∧ p1))) → (True → (p2 ∧ (((p4 → (p2 ∧ False)) ∧ p3) ∧ p4)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715922292297289451115043269 : ((((((p2 ∨ p2) ∨ p2) → p2) → (p3 ∧ p4)) → (((True → ((True → p2) → (True ∧ ((p1 → p5) → False)))) ∨ True) ∨ p3)) ∨ p1) := by
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
theorem thm_5_vars_64365085240437501074580178331 : ((p1 ∨ (((p4 ∧ (p1 → ((p3 → ((p5 → False) ∧ True)) → p3))) ∨ ((((p3 ∨ p4) ∨ (True ∧ (p2 → p4))) → True) → p2)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50740589923770678474628619893 : (((p1 ∧ (((((p3 ∨ p1) ∧ p1) ∨ p2) ∧ p4) → (p4 ∧ ((p4 → False) ∨ ((p1 ∧ True) ∨ False))))) → (p4 → ((p4 → p2) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_649000713012941973919161251815 : ((((((p1 ∨ (p2 ∧ (True ∨ (p3 → ((False ∨ p5) ∧ (False → ((((p2 ∨ p1) → True) ∨ False) ∧ p1))))))) → p2) → p2) ∧ (p3 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323653256691679550796117235079 : (p5 ∨ ((((p1 → False) ∧ ((((True ∨ (p4 → (p1 ∧ p5))) ∨ (p5 ∨ p4)) ∧ (p1 → p5)) → p4)) ∨ True) ∨ ((True ∧ p3) ∨ (p5 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214611265900470809238954718003 : (((True → True) ∧ (False ∨ p3)) ∨ ((((False ∨ (p2 ∨ p5)) ∧ p3) → ((False ∨ ((((p2 ∧ (False ∧ p4)) ∨ True) ∨ p5) → p2)) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112317894211041747865476461418 : (((p3 → ((p1 ∨ ((True ∧ (p1 ∨ ((p1 ∧ p4) → p3))) → ((((p3 → (p4 ∨ p4)) ∨ p3) ∨ p5) ∧ p3))) ∨ p2)) ∨ p3) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260188705612569848799066325260 : ((p2 → p2) → ((((False → True) → p4) ∨ p3) ∨ ((p1 → (p4 ∨ (((False → True) → p2) → ((p4 → p5) ∨ p5)))) → (True ∨ (True ∧ p1))))) := by
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
theorem thm_5_vars_639357533907000417917079596232 : ((((((False ∨ True) → (p1 ∧ p4)) → (((True → ((False ∧ (p3 ∧ True)) → p3)) ∨ p1) ∨ (True ∨ ((p1 → (p5 → p3)) → True)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124851957627974607560146123288 : ((((p2 → p3) → (p4 ∧ p4)) ∨ ((p5 → ((p1 → (p5 → ((p3 → True) → p2))) ∧ True)) → ((p1 ∨ p3) ∧ (True ∧ p1)))) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689703832571053195439169032533 : (((((p5 → (p3 ∨ (p2 ∨ p1))) → ((((False ∨ (p5 ∧ p5)) ∨ p4) → p5) ∧ True)) ∨ ((False → (p3 ∧ (p3 → (p3 ∨ p4)))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207979887138635164363082234844 : ((((p3 → p2) ∧ p1) ∨ (True → p3)) → (((False ∧ p1) ∧ (((False ∨ False) ∧ True) ∨ ((((p5 → p4) → p3) ∧ p5) → (p1 ∨ p4)))) ∨ True)) := by
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
theorem thm_5_vars_158288260947550685652398413072 : ((((p2 → p4) ∧ p1) → ((p1 → (p3 ∧ (p1 ∧ ((p3 → p2) ∨ ((p2 ∨ False) → False))))) → p5)) ∨ ((p3 → False) → ((p4 ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149925763962659798170766340610 : ((p3 ∨ (((p5 ∧ p3) ∧ ((p5 → p4) ∧ (((p3 → p5) → False) → p5))) ∨ ((True ∧ (p5 → p3)) ∨ True))) ∨ ((p4 ∧ (p5 → p3)) ∨ p5)) := by
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
theorem thm_5_vars_713496318687284309050882120217 : ((((p4 → ((False → p2) ∧ (True ∧ p2))) ∨ (((p4 ∨ (p5 → p4)) → ((((False ∨ False) ∨ (p4 ∧ p2)) ∧ p2) → p3)) ∧ (p3 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_380601140126345766033761065613 : ((((((p1 ∨ ((((p3 ∧ p2) → False) → p3) ∨ p3)) ∨ (((True ∨ p1) ∨ ((p2 ∧ ((True ∧ p4) ∨ p3)) ∨ p2)) ∨ p1)) ∧ True) ∨ p1) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192672067575811957843647242995 : ((((p5 ∧ (p5 → (True ∧ (False ∨ False)))) → False) → p3) → (((p3 ∨ ((((p4 → p5) → False) ∨ True) ∨ p4)) ∧ p4) ∨ (False ∨ (p3 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (p5 → (True ∧ (False ∨ False)))) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55408648442424501511436943325 : ((((((p5 ∨ p5) ∧ p4) → p1) ∨ False) → (p4 → (p2 ∧ (((((p3 ∧ p2) ∨ p3) → ((p3 ∧ p4) ∨ p1)) ∨ p5) → (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716564862768986743505971572287 : (((((p1 → p2) ∨ (p5 → p5)) ∧ ((((((p5 ∧ (p4 → False)) ∧ p4) → p4) → ((p3 ∨ p2) ∧ (False → True))) ∧ True) → (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94140526196703312599322111680 : ((p2 ∧ (((p1 ∨ (p5 → False)) ∧ (p3 → ((p5 ∧ (p4 → (False ∧ ((p5 ∨ p1) ∨ True)))) ∧ (((True → p2) → p2) ∨ p5)))) ∧ p5)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157488977196743964070695259255 : (((((p3 ∧ p3) ∧ (False ∨ (p3 ∧ p2))) ∧ (((p4 → p3) ∨ (p1 → p5)) ∨ p5)) ∨ (p4 → False)) ∨ (((p5 ∨ p1) → (p5 → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674967343541963445353849108710 : ((((((((p3 ∨ (False ∨ p2)) ∧ True) → p3) ∨ ((False ∧ p5) ∨ ((p2 → (p1 → p3)) ∧ p4))) ∧ p4) ∧ ((p1 ∧ (p3 → p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199714304350916937071648179675 : (((p4 ∧ ((p2 ∧ (False ∨ p5)) ∨ p5)) → p3) → ((p3 → ((False ∧ p2) ∧ (True → p4))) ∨ (True ∨ (p1 ∨ ((p1 ∨ (p3 ∧ p1)) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598642429009545752901841134468 : (((((p3 ∨ (p2 → p5)) → ((p2 ∨ (p4 ∨ True)) → ((p4 ∨ (p4 ∧ (p4 → ((p5 ∧ (p1 ∧ p2)) → p4)))) ∧ (p1 ∧ p1)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302983961006844240626864407190 : (False ∨ (p1 → ((((p5 ∨ (p5 ∨ ((p3 ∧ False) ∨ p5))) ∨ p4) ∨ (False ∨ ((((True ∨ p4) ∨ True) → (p2 ∧ (p5 ∨ True))) → p1))) ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185060740979456970006829149137 : (((p1 ∧ p4) ∨ (((p4 → p1) → p2) ∧ (p2 → (p4 → p1)))) ∨ (((p4 → False) ∨ ((p5 ∧ (p2 ∧ False)) ∧ p4)) ∨ (False → (p5 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41281749996630275861442246862 : (((((p3 → (((p3 ∧ p1) → p3) → (((p5 ∨ True) → p2) ∧ ((p1 ∧ False) ∧ p4)))) → False) → (((p2 → False) → True) → False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40343730210930973044542538790 : (((((p5 ∧ (p5 ∧ (p2 ∨ (p2 ∧ (((p3 ∧ p1) ∨ p3) → (((p3 ∧ p4) ∧ (p2 → True)) ∧ (p4 → False))))))) ∨ p2) ∨ True) ∨ p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59244125560645847455797326079 : (((p2 ∨ p3) ∨ (((p3 ∧ ((False → ((p3 ∨ p4) → ((p4 ∧ (True ∧ p3)) → (p4 ∨ (p1 → False))))) ∨ p3)) ∨ (False → p2)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343122211530830557293689444699 : (p2 → ((p4 → (p1 ∨ p2)) ∧ (p2 → ((((((p3 ∧ (p1 ∧ p4)) ∨ (p1 ∧ p1)) → p1) → p5) ∨ p1) ∨ (((p2 ∨ p4) → p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311819188312986995717204222306 : (p2 ∨ (p1 ∨ ((((p4 ∧ ((p4 ∨ (p2 ∧ (True ∨ False))) → (p5 → True))) ∨ (p3 → (True ∧ False))) → (True ∧ p3)) ∨ (False → (p4 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_186935513913927699419127674624 : (((p5 ∨ (p4 ∧ p2)) ∧ (True ∧ (((p1 → p1) ∧ True) ∨ p2))) → (((True ∨ p1) → p5) ∨ ((True ∨ p2) → ((p3 ∧ (p4 ∧ p2)) ∨ p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206336385312346934163433374833 : ((p2 ∨ (((p2 ∨ p4) ∨ p2) ∧ p4)) ∨ (p4 ∨ (((p2 ∧ False) → (((p5 ∧ p3) ∧ True) ∧ ((p4 ∨ p1) → p5))) ∨ ((p1 → False) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300603185266787178937215052207 : (False ∨ ((((False ∨ p5) ∧ (p1 → p3)) ∧ ((((p4 ∨ ((False → False) ∨ p5)) ∧ (True ∨ p5)) ∨ False) ∨ p4)) → ((p3 ∧ False) ∨ (p1 ∨ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h7
            case inr h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h18
          case inr h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h19
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h21
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614484015283932972287749673117 : (((((((((p1 → p3) ∨ (p2 ∨ ((p5 → (False → (p3 ∧ p4))) → p1))) → p2) → p3) → p2) ∧ (p4 ∧ (p3 ∧ (p1 ∧ p2)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350221390259482579597126380768 : (p4 → (((p2 ∧ p1) ∨ ((p2 ∧ p4) → (p1 ∨ (((False ∧ ((((p5 ∨ False) → (p3 → p5)) → p1) ∧ False)) ∨ p4) ∨ (p1 ∨ p4))))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699028273676544267412712413161 : ((((p1 ∨ ((p3 ∨ p5) → ((p3 ∨ (p2 ∨ (p4 ∨ True))) ∧ p1))) ∨ ((((p1 ∧ (p5 ∨ p4)) ∧ (False ∧ (p5 → p1))) → p3) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260464390706860263005260065951 : ((p3 → False) → (((((p5 ∧ p5) → ((p2 ∨ (((False ∨ (p5 ∨ False)) → ((p5 ∧ False) → p5)) ∧ True)) ∧ False)) ∧ p2) ∨ (p2 ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785816076249768841001267484550 : (((p4 ∨ ((p1 ∨ (((True ∨ p2) ∨ ((p2 ∨ (((p5 → (p2 ∧ (p5 → False))) → p2) ∧ (False ∨ False))) → False)) ∧ (p5 → p1))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707506124986261819302753968425 : (((((False ∨ (False ∨ p4)) ∨ ((p2 ∨ p1) ∧ p4)) ∨ (p5 → ((p3 ∨ (((p1 ∧ p4) → p3) ∨ ((p4 ∨ True) → (p4 → False)))) → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305999708427485057731797727203 : (p1 ∨ (((p1 ∧ False) ∧ (p5 ∧ False)) ∨ (((p5 ∨ (((True → True) ∨ (False → p2)) ∧ False)) ∨ (True ∨ p2)) ∨ ((p1 ∨ (p2 ∧ p1)) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185902026777145842513079960163 : (((((p3 → False) → ((p4 → p4) ∨ p2)) → (True ∧ True)) ∧ p5) → (((((p1 ∨ (p2 ∧ ((False ∧ p5) → True))) → p2) ∨ p5) → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 ∨ (p2 ∧ ((False ∧ p5) → True))) → p2) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190421387039958852735559361614 : (((p2 ∨ ((((p1 ∧ p4) ∨ p4) → p3) → p5)) ∨ True) ∨ ((((False ∧ p2) → ((p3 ∨ ((p5 → p1) → p3)) → (True ∧ p1))) ∨ p5) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58339306599780118997780350991 : (((False ∨ p3) ∧ ((((((p1 ∧ (p5 ∧ (p5 ∨ (True → p4)))) ∧ p4) ∨ (((False → True) → p2) → True)) → p1) ∧ p2) ∨ (False ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234070438510243459312968807143 : ((True → (False ∧ False)) → (p3 → ((((p4 ∨ p1) ∨ (p3 ∧ p4)) ∨ ((((p2 ∨ (True → p4)) ∨ p1) ∧ True) ∨ ((p5 → False) ∨ p2))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314237532644702746594262834912 : (p3 ∨ ((((p5 ∨ p3) ∨ (((((True ∨ p2) ∧ p2) ∧ True) ∧ p4) ∨ (((p3 ∨ p2) ∨ (p3 → True)) ∧ True))) → p2) ∨ (p3 ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_861284686193867139314461210972 : (((((((p1 ∨ ((((p2 ∨ (p4 → False)) → p1) ∧ False) ∨ (p5 ∨ False))) ∧ (p3 → p1)) ∨ (p2 → False)) ∨ (True ∨ (p5 ∨ p1))) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ ((((p2 ∨ (p4 → False)) → p1) ∧ False) ∨ (p5 ∨ False))) ∧ (p3 → p1)) ∨ (p2 → False)) ∨ (True ∨ (p5 ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686500012180151619109093928067 : (((((p5 → (False → p4)) ∨ (p5 → ((p1 ∨ True) ∨ ((True ∧ p5) ∨ ((p1 → p4) → p2))))) → ((False ∧ (False ∨ False)) ∨ (False → p3))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_788401070613036398815205116117 : (((p5 ∨ (((p3 → ((p3 ∧ True) → (False ∧ ((((p3 → p4) → (p1 ∨ p1)) ∧ True) → p2)))) ∨ ((False ∧ p1) ∧ (p3 ∨ True))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808215689080366722575390057339 : (((p4 → (p4 ∧ ((p5 ∨ ((p2 ∧ (p3 ∨ p4)) → (True ∧ (False ∧ ((True → (p3 ∧ (p2 ∨ (p5 ∧ False)))) ∧ (p5 ∧ p2)))))) ∨ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140203505391945842959116891390 : ((((p4 ∧ p4) ∧ (p5 → ((p5 ∨ (p5 → (True ∧ True))) → (p2 → (p3 ∧ ((True ∧ p2) ∧ p1)))))) → (p4 ∨ p1)) → ((p3 ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357080750949459545377956838403 : (p5 → (((p3 → p3) ∨ p5) → (((p5 → (p1 ∨ (p2 ∧ p3))) ∨ p5) ∧ ((((True ∧ ((p1 ∨ False) ∨ (True ∨ True))) → False) → True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204475318436023085968865117836 : (((((False ∨ p5) ∧ p4) ∨ p5) ∨ False) ∨ (((False ∧ (False ∧ p4)) → p4) ∧ ((p4 → p4) ∨ ((p5 ∧ (p3 ∨ p1)) → ((p2 → p3) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345513478541195403526661998004 : (p3 → ((((True ∧ (p1 ∧ ((p3 → p5) ∨ p3))) ∨ (True ∨ (p1 → (p2 ∨ p3)))) → ((p4 → p1) ∧ (((p2 ∧ False) ∨ True) ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675915008323277274231944125085 : (((((True → ((False ∨ (p3 ∧ (True ∧ (True → True)))) ∨ p2)) ∧ (True ∧ ((p1 → p2) → (p3 → p3)))) ∧ ((p3 ∨ p4) ∧ (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157175721331377488666028589277 : (((((p1 ∨ ((p1 ∧ p4) ∨ ((p2 ∨ p4) ∨ (True ∨ True)))) ∨ ((p2 → True) → True)) → p1) → p3) ∨ ((True ∨ (p3 ∧ (False → p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203566148991807411358662698891 : ((p1 ∨ ((p1 ∧ False) → (p1 ∧ p4))) ∧ (((((p3 → p4) ∨ False) ∧ (p5 ∨ (False ∨ p1))) ∧ False) ∨ ((True → (p5 ∨ (False → p1))) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215896429869003012968070624061 : ((p3 ∨ ((p5 ∨ p5) ∨ p4)) ∨ (True → (((p4 ∧ False) ∨ ((((True ∨ (p1 ∨ True)) → p3) ∧ ((True ∧ True) ∧ p4)) ∨ False)) → (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : (True ∨ (p1 ∨ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767143939063698527109382909564 : (((p4 ∧ (p5 → (((p3 ∧ (p3 ∨ (p5 → (((False → True) → p3) ∧ (p1 → False))))) ∨ (p3 ∨ (p4 → (p5 ∧ (False → True))))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176116042280649158692761123108 : ((((p2 ∧ p5) ∨ (False ∧ ((p2 → (True → p5)) → (True ∧ p3)))) → True) ∧ ((False → False) → (((False → (p5 → p3)) → (p1 ∨ p4)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656624696310962997846166908501 : (((((((True → p5) ∨ ((p4 ∧ p3) ∨ p4)) ∨ False) → ((p2 ∧ p5) ∨ (p5 ∧ ((p1 → False) → (p2 ∨ (p4 ∧ True)))))) ∨ (True ∨ p3)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_66570565754665050803846340821 : ((True → ((p5 ∨ (p2 ∨ (((((p3 → ((((p2 ∧ p1) → p4) ∧ True) ∨ (p5 ∧ p3))) ∨ p3) → p4) ∧ p2) ∨ p3))) ∨ (p4 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599565116240425401009102868198 : (((((p4 ∨ p1) ∨ (((p2 ∨ p1) ∨ ((p2 ∧ (False → (p2 ∧ p2))) → ((False ∧ (((p1 ∧ p2) ∨ p5) → p1)) ∧ p2))) ∧ True)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1513963338739449357177576502 : ((((False ∧ ((p3 → p4) ∧ False)) ∨ (p4 → (p3 ∧ p3))) ∨ ((True ∧ p3) → (True ∧ (((p2 ∧ p5) → p4) → p3)))) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693808646466278302346219352212 : ((((((((p3 ∧ ((p3 ∧ p2) ∨ False)) → False) ∨ p5) → (True ∨ p1)) → p4) ∨ ((((False ∧ p1) → (p5 ∧ True)) ∨ (False → p4)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348521084970145903318470318673 : (p3 → (p3 ∧ (True ∧ ((((p5 → True) → ((p2 ∧ False) ∨ ((p4 → p1) → ((p4 ∨ (p3 ∧ p4)) ∨ p5)))) ∧ ((True ∨ p4) → True)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690366888621767434421736019243 : ((((p4 → ((p5 ∨ (p1 → False)) ∨ ((True ∨ p5) ∧ ((p1 → (p3 → p4)) → False)))) ∨ (True ∨ ((p2 ∨ ((False ∨ p3) → p1)) → p3))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_60897225788361308303700550815 : ((True ∧ (p4 → (((p2 → p3) ∨ p5) ∧ (((((p3 ∨ p3) ∧ (p3 → ((p3 ∧ p3) → ((p2 → p1) ∨ p4)))) ∨ p5) ∧ p4) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157232607905202069850980241242 : ((((p5 ∨ (p2 → ((p1 ∨ True) ∨ ((False ∧ True) ∨ p3)))) ∨ ((False ∨ p4) ∧ (p2 ∨ False))) → p3) ∨ (((False → p5) → p5) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258775658381597143704910349498 : ((True → False) → ((((p1 ∧ (p2 ∧ p4)) ∧ ((p1 ∧ p4) ∧ ((p2 ∧ False) ∨ ((False ∧ p4) → p3)))) ∨ ((p3 ∨ p4) ∨ p1)) ∨ (p5 ∧ False))) := by
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
theorem thm_5_vars_169856989851553240184037124217 : ((((((True ∨ ((p5 → True) ∧ p4)) ∨ (p2 ∨ True)) ∨ p3) → p4) ∨ (True ∨ False)) ∧ (p4 ∨ (p1 ∨ ((((p2 ∨ p1) → False) ∧ p5) → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807378844716177803976599628068 : (((p4 → (((p4 ∧ (((p3 ∨ True) → p3) ∧ p4)) ∧ (p3 ∧ p1)) ∨ (((p5 ∨ (p2 → (p2 → (p3 ∧ (False ∨ True))))) ∨ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727983814611712957200389350871 : ((((p3 ∨ (False ∨ p1)) ∨ ((p2 ∨ ((p4 ∨ False) ∨ p2)) ∧ (p3 → ((p1 ∨ (False → p5)) ∨ (((p5 ∨ p4) ∨ (True → p3)) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200094879544202418897449359061 : ((((False ∨ p2) → p5) ∧ ((p2 ∧ p1) → p3)) → (p2 ∨ (p5 ∨ (False ∨ (((p2 ∧ (p4 ∧ (False ∨ p2))) ∧ p5) → (False → (p5 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264540513816836680597162829764 : (True ∧ (((True → p3) ∧ p1) ∨ ((p4 ∨ (p2 ∧ ((True → (p3 ∧ (p2 → (p1 ∧ (p2 → p3))))) ∧ p5))) ∨ ((False ∨ True) ∨ (p3 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704125949058519344085034451509 : ((((((p1 → (p5 ∧ (p5 ∨ p2))) → p5) ∧ (p3 ∨ p4)) → (p4 ∧ ((p4 ∧ ((p5 ∨ ((p3 → p2) ∨ (p5 ∨ False))) → p3)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204140544135173449370578690166 : ((((p1 → (p3 ∨ p2)) ∧ p3) ∧ False) ∨ ((((p1 ∧ ((p3 ∧ (True ∧ p1)) ∧ (p4 ∨ True))) ∨ p3) → ((p2 → p1) ∨ p3)) ∨ (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190240692516833987929847439624 : (((((True ∧ ((p2 ∨ p1) ∨ p1)) → p2) ∧ p2) ∨ p4) ∨ (((p5 → (p5 → p5)) → p4) → ((p1 → p4) ∨ (((p3 ∨ p2) → False) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p5 → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221756314459651616888103648450 : (((p1 ∧ p1) → p1) ∧ ((p4 ∧ ((p2 ∧ False) → True)) → (((p1 → ((False → p4) ∧ (((p4 ∧ p3) ∧ (False ∨ p2)) ∨ p2))) ∨ False) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



