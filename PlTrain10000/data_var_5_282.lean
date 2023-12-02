variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161583119904965807676041569039 : ((True ∨ ((((p5 ∨ p4) ∧ p3) ∨ p1) ∨ ((p3 ∨ p2) ∨ (p3 ∧ (p3 → ((p5 ∨ True) ∧ p1)))))) → ((p1 → False) ∨ (False → (p1 ∨ p2)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166199432930723352354523541662 : ((p1 ∧ ((p2 → p4) ∧ (p5 ∧ ((p3 → ((p3 ∧ (False ∧ True)) ∨ (p2 → p2))) → False)))) ∨ ((True → (True ∧ True)) ∧ ((p5 ∧ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48087673985401965740522176305 : ((((((True → p4) ∧ p2) → (p5 ∨ True)) → (p2 ∨ (False ∨ (((False ∧ (p2 ∧ p3)) → p1) → ((p4 ∧ p2) → p3))))) → (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150848343122096060070002060880 : (((((((True → True) → (p2 ∧ (p5 → p2))) ∧ p2) ∨ p2) ∧ (((p5 ∧ p3) ∨ p5) → (False → p3))) ∨ p1) → ((p2 ∧ p1) ∨ (p2 → p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707936293855058883947052637371 : ((((p5 ∧ (p2 → ((p2 ∧ p1) ∨ (p3 ∧ p2)))) ∨ ((True ∧ ((True → (p3 ∨ (p5 → p3))) → ((p3 → p1) ∨ (p2 ∧ p2)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299186160978767373651933730872 : (False ∨ ((((False ∧ False) ∨ ((p1 ∧ ((p1 → (p2 ∧ (False → (True → (((p5 → p1) ∨ p1) → p5))))) ∨ p2)) ∨ (p5 ∨ p3))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155539603949405127377422796120 : ((((p5 ∨ p3) ∧ True) → (p5 ∨ (p2 ∨ ((p1 → p1) → ((p1 ∨ ((p4 ∨ False) ∨ True)) ∨ p3))))) ∧ (((False ∨ (p4 → True)) ∧ True) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664952391155626136146811238487 : ((((p3 → ((p2 ∧ p4) ∧ ((p5 → (p1 ∨ ((p1 ∧ ((p2 ∧ p2) ∨ (p1 ∨ p3))) → p1))) ∨ (p4 ∨ (p1 ∧ p4))))) → (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258643509624637993471864068911 : ((p5 ∨ p5) → (((False → ((p1 ∨ p4) ∧ (p5 ∧ ((False → (p3 → True)) → p5)))) → (((p4 ∨ True) ∨ (p3 ∧ (p2 ∨ False))) ∧ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
theorem thm_5_vars_348866877319221342894309880089 : (p3 → (p2 ∨ ((p2 ∧ ((False ∧ (((p1 ∧ True) ∧ p4) → (p3 → ((False ∨ (False ∨ False)) ∨ p1)))) ∨ p5)) ∨ ((True → (p2 ∧ p1)) → True)))) := by
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
theorem thm_5_vars_185390585416095576636249148358 : ((p5 ∧ (p2 ∨ ((((True ∨ p5) → (p3 ∨ p4)) → p3) ∧ p3))) ∨ (False → (False ∨ ((False → ((p2 ∧ p2) ∧ ((p1 → p5) → p1))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111426410208610241459467249258 : (((p4 ∨ (((((p5 ∨ ((p4 ∧ True) ∧ p3)) ∨ (p3 ∨ p5)) → (((p1 → p5) ∧ p2) ∧ p5)) ∨ p5) ∧ (p2 ∧ p1))) ∧ True) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590978220955393506246272431919 : (((((p2 → ((((p5 → p5) ∧ (p1 ∨ True)) ∨ (p5 → (((p1 ∧ (True → True)) ∨ p2) ∨ False))) ∨ (False ∨ (False ∨ p2)))) → p1) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630408121864718831682928903380 : (((((p4 ∧ ((True ∨ p3) ∧ (True ∨ ((p2 ∧ p5) → (False ∨ (((True ∨ p3) ∨ p2) → (((True ∧ p3) → p3) ∧ p2))))))) ∨ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46922160812217442853481625436 : (((((p3 ∧ ((True ∨ p1) ∨ False)) → (((p4 ∨ False) → ((((True ∧ (p1 → False)) ∨ p5) ∨ p5) ∨ p1)) → p1)) ∨ p1) ∨ (p5 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136828881623589398844787356151 : (((False ∧ p2) ∨ (p1 ∨ ((((((True → False) ∨ (p5 ∧ (False → p5))) ∧ (p4 ∨ p2)) → p4) ∧ p5) ∨ (True ∧ True)))) ∨ ((p1 ∨ False) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_184109386664528030160351612652 : ((((False ∨ p5) ∨ ((((False → p1) → p3) → p5) → False)) ∨ p5) ∨ (p1 → (False → ((False → True) → (((p2 → False) ∧ (p3 ∨ False)) ∧ p5))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350897636318641603823480816021 : (p4 → ((p2 → ((False → (True ∨ p5)) → ((p4 → p5) → (p5 ∨ (True → ((False ∧ ((p4 ∧ p2) → p4)) ∨ (p1 ∧ p1))))))) ∧ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345371881190348414351998296803 : (p3 → (((((p4 → (p1 ∧ p2)) ∧ ((p4 → False) ∧ p1)) → (((False ∨ (p2 → p4)) ∧ (p1 ∨ p1)) → (p1 → (p4 ∧ True)))) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302726155865522615697697890230 : (False ∨ (p3 ∨ (p5 ∨ (((False → ((((p1 → ((p2 → (((p5 → p4) ∧ (p1 ∧ p1)) ∧ True)) ∨ p5)) ∧ p2) ∨ p2) ∧ False)) → p1) ∨ True)))) := by
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
theorem thm_5_vars_319906870537854659494961410299 : (p4 ∨ (((p5 ∧ (p3 ∨ True)) ∨ False) → (True ∧ ((((p4 ∨ False) ∨ p1) ∨ ((True → ((p3 ∧ p3) ∨ (p5 ∧ p5))) ∧ (False → True))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646444882470018851003430577078 : ((((p1 → ((True ∨ ((p4 → (((p5 ∧ p5) ∧ (p1 → p2)) → p1)) → (p3 ∨ ((p4 ∨ (p1 ∧ (p1 → p5))) ∧ p1)))) ∨ p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307184025474301861276576099047 : (p1 ∨ (p1 ∨ ((p5 ∨ (((((p1 ∧ False) ∨ (p2 → p1)) ∧ ((p2 → p5) ∧ p2)) ∨ p1) ∨ (False → (True → ((p1 ∨ p4) → True))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191012653881033393412282339697 : (((p3 ∨ ((p3 ∨ p3) ∨ p2)) ∨ ((p5 ∧ p1) ∨ p5)) ∨ (True ∧ ((p4 ∨ (False ∨ p4)) → ((p4 ∧ ((p1 → p4) ∨ p2)) → (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724496539758886066105614670108 : ((((False ∨ (p3 ∧ True)) ∧ (True → ((True ∧ p3) ∧ (p4 → ((((True ∧ (p2 ∧ p1)) → False) ∧ ((p2 ∨ True) → (False → True))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87440684545952610883353386580 : (((True → (False ∨ (p5 ∧ (False ∧ p3)))) ∧ ((p3 → (False ∧ p2)) → (p5 → ((((((p5 ∨ p1) → p3) ∨ p1) → p4) ∧ p4) ∨ p1)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134074025336795538109215641129 : (((((((p1 ∧ (p2 ∧ ((p5 ∨ p3) → False))) ∨ ((True ∨ p1) ∧ (p4 → p4))) → p1) ∨ (True → p1)) → p1) ∨ p5) ∨ (p2 ∨ (p2 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p1 ∧ (p2 ∧ ((p5 ∨ p3) → False))) ∨ ((True ∨ p1) ∧ (p4 → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147605373561727864793721641635 : (((((p3 ∧ (p2 → p4)) → ((((p1 ∧ True) → p1) ∨ p5) → (((p1 ∧ p2) → p3) ∧ p4))) ∨ p5) → p1) ∨ ((False ∧ (p2 → p1)) → p4)) := by
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
theorem thm_5_vars_147016726510069289897598251401 : ((((((p3 → p1) ∧ ((p1 → p2) → True)) ∧ (p2 → (((False ∨ p2) ∧ True) ∨ p1))) → (p1 → p3)) ∧ p5) ∨ (((False ∨ p4) ∧ p3) → p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52006365871435029939761169693 : (((p2 ∧ (((True → (p4 ∧ True)) → (True ∧ p3)) ∨ (p4 ∧ ((p2 → False) ∧ p1)))) ∨ (p5 ∨ (False ∨ (p5 ∨ ((p1 → p1) ∨ False))))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113667614269460797905468382003 : (((((p1 ∧ (((p4 → p5) → ((p5 → ((p2 ∧ p5) ∧ p1)) ∧ (p2 → p3))) → p1)) ∨ (p3 ∧ p2)) ∨ p5) → (False ∨ p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116636032535101266984355529484 : (((p1 → p5) ∧ (p5 ∧ (p1 ∧ (((p5 ∧ p1) → False) ∧ (p3 ∨ ((p3 ∧ p1) ∨ ((p2 ∧ (True → (p3 ∨ p1))) → p4))))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354670391979995953154287812867 : (p5 → (((p2 ∨ (p2 ∧ ((p3 ∨ (False → (((p5 → p5) → (True → True)) ∨ ((p1 ∨ ((p1 ∧ p5) ∨ p1)) ∨ p5)))) ∧ p2))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45657997856473420649883614949 : (((p4 ∨ (p5 → ((p4 ∧ (p4 ∧ (((p4 ∧ ((p1 ∧ p1) ∧ p1)) → (p1 ∨ p1)) ∧ False))) → ((p4 → (p4 → p5)) ∨ p2)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950041800512901498116717396807 : (((((True ∨ p1) → False) ∧ (p5 ∨ (((p5 → ((p5 → p4) → (p1 ∨ p4))) ∨ False) ∧ ((p4 → ((p4 ∨ (p4 → False)) ∨ p1)) ∨ False)))) → p1) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753491431392340926368782286889 : (((False ∧ ((((((((True ∨ p5) ∨ (p3 ∧ True)) → (True ∧ True)) ∨ p5) → (True → p5)) ∨ False) ∨ p3) ∧ (p3 ∧ ((p3 ∨ p4) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40934000447508116754075388367 : ((((((p5 ∨ ((p3 ∨ (True ∧ (p4 ∨ (((p3 ∨ ((True ∨ True) ∨ False)) → p1) → p3)))) ∧ False)) ∨ p2) ∨ True) ∨ (True → True)) ∨ p3) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615360610402152057915218729213 : (((((((p4 ∨ (True → p4)) ∨ p3) ∧ (((True ∨ (p2 ∨ False)) → p1) ∧ (p4 ∨ p2))) ∨ (p3 → (((False → p1) ∨ False) → False))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_168725305334094447834849779350 : ((True ∨ (True → (p2 → (p4 ∧ ((((p4 ∧ p3) ∧ ((False ∧ p3) ∧ p3)) ∨ p3) ∧ p2))))) → (((False ∨ (p5 → p2)) → p2) ∨ (p3 → True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197500044529045625118286372430 : (((True ∨ (p3 → (p2 → p4))) ∧ (p5 ∨ p2)) ∨ (p5 ∨ ((p3 ∨ (True → (p4 ∨ ((False ∧ p3) ∨ p1)))) ∨ (p2 → (p4 → (p3 ∨ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114402783870796350754133305736 : ((((((True ∧ p4) ∧ (p4 ∧ False)) ∨ True) ∧ ((p3 ∨ (p1 ∨ ((p3 → False) ∧ p2))) ∨ p1)) ∨ (p1 ∨ ((False ∧ p5) ∨ True))) ∨ (p3 ∨ p4)) := by
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
theorem thm_5_vars_644297471966314355874639774400 : ((((False ∨ ((((p2 ∨ ((p2 ∨ p1) ∧ ((p5 ∧ ((p5 → (p2 → p1)) ∨ p5)) → p5))) → p3) ∨ True) ∨ (p4 ∧ (False ∨ p3)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185357281879757558462666600039 : ((p4 ∧ (p1 ∧ (p5 ∧ (p3 ∨ (p2 → ((p2 ∧ p4) ∧ p1)))))) ∨ ((((False ∧ p3) ∧ True) → ((p4 ∨ (p1 ∨ True)) → (p2 ∨ p1))) ∨ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199705616637383374175191440860 : (((p2 ∧ ((p3 → (False ∨ p1)) ∨ p4)) → p1) → ((((p4 ∧ True) → (p2 ∧ (((p3 ∨ p3) ∨ p4) ∧ True))) ∨ p2) → (p4 → (False ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∧ ((p3 → (False ∨ p1)) ∨ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (p2 ∧ ((p3 → (False ∨ p1)) ∨ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60949476353505474681980795601 : ((False ∧ ((((((p4 ∨ p1) ∨ (((p1 ∨ p5) ∨ True) ∨ ((p1 → p3) ∧ (True ∨ p5)))) ∨ p5) ∧ ((p2 ∧ p2) ∨ p3)) ∨ False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53494443603347843046775750548 : (((True ∨ (True → (((True → (p4 ∧ p1)) → p5) ∧ (p3 → p2)))) → ((p2 ∨ p4) ∧ ((p4 → (p4 ∧ p3)) ∨ (p4 ∨ (p3 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181654409072528359004297559312 : ((p3 → (p3 ∧ ((((((p2 ∨ p2) → p3) ∧ p1) → p5) ∨ False) → p5))) → (((p5 → (p1 ∧ p1)) ∧ True) → ((p1 ∧ p5) ∨ (p5 → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249259917266080814190192837476 : ((p4 ∨ p4) ∨ ((p2 ∧ (False ∨ False)) ∨ ((p5 ∧ ((False ∨ (p2 → p3)) ∨ (p1 → p3))) → (p4 → ((p1 ∧ (p3 → p2)) ∨ (p1 → True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55407348416360210170049066203 : (((((p4 ∨ (p2 ∨ p3)) ∨ p3) ∨ p2) → ((((((p1 → p5) → p5) ∨ p5) ∧ p5) ∧ ((p4 ∧ False) → p5)) → (p4 → (True ∧ p5)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h14 =>
            -- One of the premise coincides with the conclusion.
            exact h7
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h23 =>
            -- One of the premise coincides with the conclusion.
            exact h7
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695013068761116905271150925855 : ((((((False → (p5 → p5)) ∨ (((p1 → (True ∨ True)) ∨ p3) ∧ p3)) ∧ p2) → (((True → p2) → (True ∧ (p1 → True))) ∧ (p5 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234248291355985850188513402604 : ((False → (p3 ∨ p5)) → (((((p5 ∨ True) ∧ ((((p3 ∨ (p2 → True)) ∨ p5) → p2) ∨ p3)) ∨ p4) ∨ (p5 ∨ True)) ∧ ((p4 → p4) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244196474317173366163721965941 : ((True ∧ p5) ∨ (((p5 → p2) ∧ (((True ∧ p4) ∨ (p1 ∨ (p5 → p2))) → ((p4 ∧ (p3 ∧ ((p4 ∧ p2) → p4))) ∧ (p1 → p5)))) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ p4) ∨ (p1 ∨ (p5 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114621246010017464615212761219 : ((((((((True ∨ True) → False) ∨ (p3 → (p2 ∨ p1))) → False) → (True → p4)) ∧ False) ∨ ((((p2 ∧ p4) ∨ p2) ∨ p3) → True)) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624754841130183007136721161060 : ((((p5 ∨ (((((p1 ∧ (p4 → False)) ∧ False) → False) ∧ (((True → p5) ∧ ((p2 ∧ (True → p5)) → (p2 → p4))) ∨ True)) ∧ False)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_664779956611941751057294052452 : ((((p1 → ((p3 ∧ (((p1 ∧ ((False → False) → p3)) ∨ (((p2 → p5) ∧ p5) ∨ False)) ∧ p4)) → (p1 ∧ (False → p1)))) → (p3 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339857721353956748940979423619 : (p1 → (True → ((((False ∧ False) ∧ p2) ∨ (p3 → (((p3 ∨ (False ∨ (p2 → True))) ∧ True) ∧ (p5 ∧ (p4 → (p2 ∨ p2)))))) ∨ (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355532080794200174230587773895 : (p5 → ((((True ∨ ((p4 → p5) → (p5 → p2))) → ((p3 ∨ False) → (False ∧ (p1 ∧ (((p3 → True) → True) ∨ True))))) ∧ False) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137372716073736113045676009249 : ((p3 ∧ (((p2 ∨ (((((p3 ∨ p1) → (False ∨ True)) → p5) ∧ p2) ∧ p3)) → True) ∧ (((p2 ∨ p4) ∨ p4) ∧ False))) ∨ ((False → p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677233198220837888601267087498 : ((((((True → ((p3 → ((((False ∧ p4) → p1) ∨ p1) ∧ False)) ∨ p4)) ∨ (p3 ∨ (p5 ∧ False))) ∧ p1) ∨ (False ∧ ((p1 ∨ p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612745137020836598904862136736 : (((((((p4 → False) → (p3 ∨ p1)) ∧ (((p3 → (p4 → p3)) ∨ (((p3 ∧ False) ∨ False) ∨ False)) ∨ (p1 ∧ False))) ∨ (p2 ∨ p5)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_46506675054960935278494460983 : ((((p2 ∧ p3) ∧ ((False ∨ (((((p3 ∧ (((p3 ∨ p3) → p3) ∨ p5)) ∧ p2) → (p3 → p4)) ∧ p1) ∨ p3)) → p5)) ∧ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218881627850286243523534252959 : ((p2 ∧ (p2 → (p5 ∨ p4))) → (((p2 ∧ p4) ∨ True) ∧ ((((p1 → (p1 ∨ p5)) → ((p2 ∧ (True ∨ (True ∨ p2))) ∧ p4)) → p1) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147619129956822220084147884767 : ((((((p5 ∧ p3) ∧ (((p1 ∨ p2) ∧ p2) ∧ (p5 ∨ ((True ∧ p4) → (p2 → p5))))) ∧ p3) → p1) → p5) ∨ (((False ∧ p2) ∧ p2) → p5)) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177721030698388398760205346680 : ((((((p4 ∧ True) ∧ p3) ∧ True) ∧ ((p4 ∧ False) → (True → p2))) ∧ True) ∨ ((p5 ∨ (p3 ∧ (p4 ∧ (p5 ∧ p1)))) ∨ ((p2 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219615012179213701057483295299 : ((False → ((False ∧ p1) ∧ p2)) → ((p2 ∧ p1) → (((p5 ∨ p1) ∧ (((p1 ∨ True) ∨ True) ∨ (p1 ∧ p5))) ∨ ((p5 ∨ True) ∨ (p1 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341682976067705329996356961239 : (p2 → ((((((p1 → (p2 ∨ True)) → (p1 ∨ p3)) → ((False ∧ (p2 → (True ∨ p5))) ∧ False)) ∧ (p5 ∧ (p2 ∨ True))) → False) ∨ (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609665094006280945788182322561 : (((((p1 ∨ (((((p3 ∨ (p3 → (((p1 → p1) ∨ False) → p3))) ∨ p4) ∨ p5) ∧ (((p5 → p4) ∧ p2) → p3)) ∧ p5)) ∨ p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54925019825002065587778207103 : (((((p5 ∧ p3) → (p1 ∧ p1)) → p2) ∧ ((True ∨ (p4 → False)) → ((p5 ∧ p3) ∧ (((p4 ∧ p3) → ((p5 → False) ∧ p2)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58643780839855357065472576332 : (((p1 → p1) ∧ ((p3 ∨ ((p5 ∨ p1) ∧ (p2 ∨ ((p1 → (p3 → (p2 → p4))) ∧ p1)))) ∨ (((p3 ∨ p4) ∨ p4) ∨ (True ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_323279432969779816953881113230 : (p5 ∨ ((p3 → (p5 ∨ ((p1 ∨ p5) ∨ ((p4 ∨ ((p1 ∨ p5) → ((((p1 ∧ p1) ∧ p5) ∨ (p3 ∨ p1)) ∨ p1))) ∨ p4)))) ∨ (False ∧ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184520104340683374634469779646 : (((p2 ∨ (((False → (p1 → p4)) → p3) ∨ p5)) ∨ (p3 ∨ p3)) ∨ (p3 ∨ ((((((p4 ∧ p1) ∨ False) → p4) ∨ (True ∧ p5)) ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319659901192641945335642275818 : (p4 ∨ (((((p5 → False) → True) ∧ (p4 → p4)) ∧ p5) → ((((p1 → ((p5 ∨ p3) → True)) ∨ (p2 → p4)) → p2) ∨ (p3 ∨ (True ∨ False))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150735588816545745544902120520 : (((((((p5 ∨ p1) ∨ p4) → ((((p5 ∧ p4) ∧ p3) → ((False ∨ p1) ∧ False)) → p5)) ∨ p1) ∨ p1) ∨ False) → (p4 ∨ (p3 → (p4 ∨ True)))) := by
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94776440263463204697047247191 : ((p3 ∧ ((p5 → (p4 ∧ ((p5 ∨ p5) ∧ p2))) ∧ ((p5 → ((p1 → p5) ∨ p1)) → ((False ∨ p5) ∧ (False ∧ ((p3 → p5) → p1)))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p5 → ((p1 → p5) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149596205324532418872522334985 : ((p3 ∧ ((p5 ∨ (((p3 ∧ p4) ∨ ((((p2 ∧ p5) ∨ False) → p3) ∧ p5)) ∧ p5)) ∧ (True → (True ∧ p2)))) ∨ ((p1 ∧ (True → p3)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184628612023604308351000206759 : (((p1 ∧ (((p4 → False) ∨ p5) ∧ False)) ∧ ((p2 → p5) ∧ False)) ∨ (p1 ∨ (True ∧ (((p1 ∨ True) ∨ ((True ∨ p3) → (True ∨ False))) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156668740361664396506478036646 : (((((((p2 → p2) ∨ ((p4 → True) ∨ (False ∧ (True ∨ p3)))) ∧ p2) → p4) ∧ (True ∨ p4)) ∧ p1) ∨ (p5 → (p5 → ((True ∨ p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114847873185216754177892519788 : (((((p4 → False) ∨ (((p4 ∧ (p3 ∧ p2)) ∨ (p1 ∨ p4)) ∧ p2)) ∨ p4) ∨ ((False ∨ ((p3 ∨ p2) ∧ (False ∨ p3))) ∨ True)) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166887411146337370566425626886 : ((((((False ∨ False) ∨ (((True ∧ p1) → p5) ∨ False)) → p5) ∨ ((False → p2) ∧ p4)) ∧ p5) → ((p4 ∨ ((False → p5) ∧ True)) ∧ (p2 ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667207654246758627561658852571 : (((((p1 ∧ p2) ∧ ((p4 → ((False ∨ (p1 ∧ p5)) → p4)) → (p4 ∧ ((p3 → ((p2 ∨ p3) ∨ p1)) → True)))) ∧ (False → (True ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154178159241186323909714612027 : ((((p3 ∨ ((p3 → (p5 ∧ ((p2 → ((True ∧ p3) ∨ (True ∨ False))) ∧ p5))) ∧ True)) → p2) ∨ True) ∧ (((True → True) ∨ p3) ∨ (p4 ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52538062092716252648985939284 : ((((p2 ∨ (((True ∨ ((p5 ∨ p4) → (p4 ∨ False))) ∨ p5) → p5)) ∨ p3) ∨ ((((p2 → (p4 ∨ (p3 → p2))) ∧ p4) ∨ p4) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688844618603307822080701610369 : ((((((((p2 ∨ ((p2 → p3) → True)) ∧ (p5 ∨ p5)) ∨ (p3 ∧ p4)) → p2) ∧ p4) ∨ (((p5 ∧ p5) → ((p5 → p3) ∨ p2)) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_147213773671697908787737132882 : (((p2 → (False ∨ (((p4 → ((p5 ∧ ((p1 ∧ False) → (p3 ∧ p1))) → False)) ∧ (False ∨ False)) → p5))) ∧ p5) ∨ (p2 ∨ (p5 ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_198566695234975293835035074130 : ((p1 ∨ (((p1 ∨ p4) ∨ p5) ∨ (p1 ∨ True))) ∨ ((False → ((False ∧ p4) ∨ (False → (((p1 ∧ p1) → ((p1 ∧ True) ∨ p4)) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165281198706089360596623806152 : (((((p1 ∧ p1) ∧ ((p4 → (p5 → p5)) ∨ (p1 → True))) → (p5 → p1)) → (p1 ∧ p3)) ∨ (True ∨ (p5 → ((True → True) ∧ (False ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356883878913154311960424456437 : (p5 → ((((p2 → p2) → p3) ∧ p1) → (((((((((p5 ∨ p2) ∨ False) ∨ True) → (p4 → True)) → False) ∨ False) ∨ (p2 ∨ p4)) ∨ p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677227603402157261390316089038 : ((((((((False ∧ True) → ((p4 → (p1 ∨ p5)) ∨ p1)) → (p5 ∨ p2)) ∧ ((p1 ∧ False) ∧ p1)) ∧ True) ∨ ((p5 → p5) ∨ (p4 ∧ True))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231964702606126861295556453667 : (((p1 ∨ p3) → p4) → (((p5 ∧ p2) ∨ p1) ∨ ((True → (False ∧ p1)) → ((p2 ∧ ((p5 ∨ p2) ∨ (p5 ∧ True))) ∧ (p3 ∧ (p5 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h15
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702428495557158760913460210413 : ((((((p1 → p2) → (p5 ∨ ((False ∧ False) ∧ p2))) ∨ p4) ∨ ((p5 → p4) → ((p5 ∧ p2) → (p2 ∨ (False ∧ ((False → p2) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44821920743887413375637025106 : ((((False → (p3 ∧ p2)) ∧ ((((True → p1) ∧ p2) ∨ True) → ((p1 ∧ False) ∨ ((p3 → ((p2 → False) ∨ (p5 ∧ p2))) ∧ p5)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308967027542989031797715943603 : (p2 ∨ (((p1 ∧ ((True → ((False ∧ False) ∨ p1)) → (p2 ∧ p3))) ∧ ((((p2 ∨ True) → p4) → (p1 → (p5 → p1))) ∨ (p3 → p3))) → p3)) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True → ((False ∧ False) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : (True → ((False ∧ False) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h12
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159279716012352468815965604352 : ((p4 → ((p2 ∨ (p3 → (((False → True) ∧ (True ∧ p2)) ∨ (p3 → p1)))) → (p1 ∨ (True → p5)))) ∨ ((p5 → p1) → ((p2 ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304795852261340942374067979900 : (p1 ∨ ((((p5 ∨ (p2 ∧ ((p2 → (p5 ∨ p4)) ∨ (p3 → False)))) ∧ ((p4 → p5) → ((False ∨ (False ∨ False)) ∨ False))) ∧ p5) → (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    have h7 : (p4 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h20 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h22 := h5 h20
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- False on the left can always be used.
            apply False.elim h26
          case inr h27 =>
            -- False on the left can always be used.
            apply False.elim h27
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h30 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h32 := h5 h30
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- False on the left can always be used.
            apply False.elim h36
          case inr h37 =>
            -- False on the left can always be used.
            apply False.elim h37
      case inr h38 =>
        -- False on the left can always be used.
        apply False.elim h38
  -- Conjunctions on the left can always be decomposed.
  let h39 := h1.left
  let h40 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h41 := h39.left
  let h42 := h39.right
  -- Disjunctions on the left can always be decomposed.
  cases h41
  case inl h43 =>
    -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
    have h44 : (p4 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h45
      -- One of the premise coincides with the conclusion.
      exact h40
    -- We have shown the premise of h42, we can now drive its conclusion.
    let h46 := h42 h44
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- False on the left can always be used.
        apply False.elim h48
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- False on the left can always be used.
          apply False.elim h51
    case inr h52 =>
      -- False on the left can always be used.
      apply False.elim h52
  case inr h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h53.left
    let h55 := h53.right
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h56 =>
      -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
      have h57 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h58
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h42, we can now drive its conclusion.
      let h59 := h42 h57
      -- Disjunctions on the left can always be decomposed.
      cases h59
      case inl h60 =>
        -- Disjunctions on the left can always be decomposed.
        cases h60
        case inl h61 =>
          -- False on the left can always be used.
          apply False.elim h61
        case inr h62 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h63 =>
            -- False on the left can always be used.
            apply False.elim h63
          case inr h64 =>
            -- False on the left can always be used.
            apply False.elim h64
      case inr h65 =>
        -- False on the left can always be used.
        apply False.elim h65
    case inr h66 =>
      -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
      have h67 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h68
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h42, we can now drive its conclusion.
      let h69 := h42 h67
      -- Disjunctions on the left can always be decomposed.
      cases h69
      case inl h70 =>
        -- Disjunctions on the left can always be decomposed.
        cases h70
        case inl h71 =>
          -- False on the left can always be used.
          apply False.elim h71
        case inr h72 =>
          -- Disjunctions on the left can always be decomposed.
          cases h72
          case inl h73 =>
            -- False on the left can always be used.
            apply False.elim h73
          case inr h74 =>
            -- False on the left can always be used.
            apply False.elim h74
      case inr h75 =>
        -- False on the left can always be used.
        apply False.elim h75



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792689414783632386276116038164 : (((True → (((p1 → (True ∨ True)) → p3) ∧ (((((p2 → (False ∨ False)) ∨ ((p5 → p5) ∨ (p5 → (p3 ∧ False)))) ∨ False) ∧ p4) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55153197400621101330166172142 : (((((p3 ∧ False) ∨ (p1 ∨ p4)) ∨ p2) ∨ ((((((p4 → p3) ∨ (p4 → p1)) ∧ ((p5 ∧ p2) ∨ True)) ∧ True) ∧ (p3 → p5)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64093963011228992674304803800 : ((False ∨ (((p4 ∧ (((p2 ∧ p4) → p3) → (True ∧ p2))) ∨ p2) ∧ (p5 ∨ (((((True → True) ∨ p1) ∨ p2) → p1) → (p4 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251010276814051857584500661121 : ((p1 → p5) ∨ ((p2 ∧ (((p1 ∨ False) ∨ (((p2 ∨ p4) → p1) ∨ (True ∧ p5))) ∨ (p2 → p2))) ∨ (False → ((p5 ∧ True) ∧ (True → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37360276441788462990301034112 : (((((((p4 ∧ (False ∨ ((p1 ∨ p4) ∧ p4))) ∧ p2) ∨ (((False → (p5 ∨ (True ∨ (p1 → p1)))) ∨ False) → p5)) ∨ p3) ∨ True) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184295882290149444145373065204 : ((((p1 ∧ (True ∨ p4)) ∧ (((p5 ∨ p3) ∨ True) → False)) → p5) ∨ (((False → ((p1 ∨ p4) ∨ (True ∧ False))) → (p4 ∧ p5)) → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p1 ∨ p4) ∨ (True ∧ False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



