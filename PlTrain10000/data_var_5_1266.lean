variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245603554920762878904315716511 : ((p3 ∧ False) ∨ (((False ∨ (p4 → p2)) → (((p3 ∧ (False ∨ (p5 → p2))) → (p1 ∨ (False ∨ p1))) ∨ p4)) ∨ ((p5 → p5) ∨ (p2 ∨ p3)))) := by
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
theorem thm_5_vars_171872604576910030389097473019 : (((p3 ∧ ((((True ∨ p1) ∨ p1) ∨ (True → True)) ∧ (p4 → (p4 → p4)))) → p1) ∨ (p3 → (((p5 → p1) ∨ (p3 ∨ (p1 → p1))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149311715415574663328213406941 : (((p2 ∧ True) → ((True ∧ (p2 → p2)) ∧ (p1 ∨ ((p2 ∧ (((p5 ∨ p4) ∨ p3) → (p5 ∨ p5))) → p3)))) ∨ ((p1 ∨ False) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197840450491897500554272070113 : (((p2 ∨ (p3 ∧ p1)) ∨ ((False ∧ p5) ∨ p5)) ∨ ((p2 → (((False ∧ p5) ∧ p5) ∧ (True ∨ ((False → p1) ∨ (p2 ∧ p1))))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46050997856459627292566532284 : ((((((p2 → (p4 → (((p5 ∨ (((p3 ∨ (False ∨ p4)) ∧ p4) ∨ (p3 ∨ p1))) ∨ True) ∨ p2))) ∧ p5) ∧ p3) ∨ True) ∧ (False → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603809774719100066550156539781 : ((((p4 ∨ (((p1 → p1) → p5) → ((((((p5 ∨ p3) ∧ ((p3 ∨ p2) ∨ p3)) ∨ (True ∨ p4)) ∧ p1) ∧ False) ∨ (p1 ∨ p4)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59520580385668233610240620647 : (((p2 → p3) ∨ ((((p4 ∧ ((True ∧ p5) → p2)) ∧ (p3 ∧ p4)) ∨ (p5 ∨ ((p5 ∨ True) ∧ (True ∨ p1)))) ∨ ((True ∧ p4) ∨ p1))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788149694499206123178023941235 : (((p5 ∨ ((((p3 → ((True ∧ (p1 ∧ p2)) ∨ p4)) ∨ p2) ∧ (((p1 ∧ p1) ∧ ((p5 ∨ False) → False)) ∧ ((False → p2) ∨ p4))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133685975601461747127465086420 : (((((p2 ∨ ((p2 ∨ p3) → (((p3 → (p5 ∧ p2)) ∨ (p4 ∧ p2)) → p3))) ∧ True) ∨ ((p3 ∨ p2) ∧ p3)) ∧ True) ∨ (True ∨ (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805406366612595796132756480200 : (((p3 → (p1 ∨ (((((p3 → ((p4 ∧ ((p4 → (p1 ∧ p2)) → p5)) → p2)) → p2) → p5) ∨ p5) ∧ (False ∧ ((p3 ∨ p3) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316729388133833724132389378935 : (p3 ∨ (True → (((((p5 → (p3 → ((False ∧ p5) ∧ ((((p2 ∨ (p1 ∧ p2)) ∨ False) ∧ p4) → True)))) → p4) ∧ (p2 ∨ True)) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_190207093635162117841010273146 : (((p5 ∨ (p4 ∨ ((p5 ∨ False) ∧ (p4 ∨ p1)))) ∧ p2) ∨ (((p2 ∨ p5) ∨ True) → (p2 → ((p3 ∨ (True ∧ (False → (True ∧ p1)))) ∨ p3)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40279030272336882314148863552 : ((((p1 → ((((p3 ∧ (False ∧ p2)) ∨ p2) ∧ (((p2 ∨ True) ∨ ((p2 ∨ ((p3 ∧ p3) ∧ p5)) ∧ p2)) ∧ True)) ∧ True)) ∧ False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116792209570562328149083987642 : (((p2 ∨ False) ∨ (((((p4 ∨ p2) ∧ (((p2 ∧ (p1 ∧ (p5 → (p3 ∧ (p1 ∨ p3))))) → p4) ∨ False)) ∨ True) ∧ p1) ∧ p5)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111177259805406357999375039904 : ((((p1 ∨ (p1 ∨ (p4 ∨ p1))) ∨ ((((p1 ∨ (False → ((p3 ∨ p4) ∧ False))) ∨ p5) ∧ (False ∨ (False ∨ p3))) → True)) ∧ p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44471187249531705222935019547 : ((((((p5 ∨ True) ∨ ((p2 ∨ (True → False)) → p3)) ∧ (p1 ∧ False)) → ((True → False) → ((False ∨ p3) ∨ ((p5 ∨ p5) ∨ p2)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47004729214080096399868390676 : (((((False → p2) ∧ (((p1 ∧ (p1 ∨ (p2 → (p1 ∧ (p1 ∨ p3))))) → (p3 → (p5 → p4))) ∨ (p2 ∧ p4))) → p1) ∨ (True ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165384872153726515878782786138 : (((((p1 ∧ True) ∧ p4) ∨ ((True → p1) ∧ ((True ∧ p4) ∧ p3))) ∨ ((p2 ∧ True) → p2)) ∨ (False ∧ ((p2 → (True → p3)) → (p5 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_136401840300221946743229315110 : (((p5 ∨ ((p2 ∧ True) ∧ p4)) ∨ (p4 → ((True → (((((p1 → p4) ∧ p1) → False) ∨ True) ∨ (p4 ∨ p4))) ∧ p4))) ∨ (p3 ∧ (p2 ∧ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346913040454492940961389654928 : (p3 → (((((p5 ∨ False) ∨ p3) ∨ p5) → (((p4 ∧ (True ∧ False)) ∨ p4) ∨ ((p3 → p5) → p1))) ∨ ((((False → p4) ∧ p1) ∧ True) → p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174538095135879925446997993342 : ((((p5 ∨ p1) → (p4 ∧ (p1 ∧ p2))) → ((((True → p1) → False) → p5) → p5)) → (((p3 ∨ True) → (p4 → (p2 → (p1 → p4)))) ∧ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807449813679723698039955520233 : (((p4 → (((p4 → p3) ∨ (p3 → ((p2 ∧ p5) ∧ True))) ∨ (p5 → (((False ∨ (p1 → p5)) ∧ (False ∧ p1)) ∨ (p5 ∧ (p4 ∨ p3)))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746193929762364040638027754162 : ((((p1 ∨ p3) → ((p1 ∨ (((((p4 → True) → False) → False) → p1) ∨ p2)) ∧ ((p4 → (False → (p3 ∨ (False → (p3 → p2))))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685784335625333600803710604244 : ((((((((p1 → p4) ∧ True) → (((p2 → (p2 → True)) ∨ p2) ∨ (p5 → False))) → p1) → p4) → (((p5 → p3) ∧ p5) ∨ (False ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67637930942537424586939455953 : ((p1 → (False ∨ (p1 ∧ (((p5 ∨ p2) ∧ (((p5 → ((True → p1) ∧ ((True ∧ p3) ∧ (p3 ∧ p2)))) ∧ (p5 → False)) → p3)) ∨ p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160394797519532087497226511785 : (((p5 → ((False ∧ ((p2 ∨ p3) ∨ ((p1 ∧ False) ∨ (True → p5)))) ∨ p4)) ∧ (False ∨ (p3 ∧ p2))) → ((p1 ∨ (p2 → False)) ∨ (p4 ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159735245011122060534854546199 : (((((p5 → ((False → p2) ∨ True)) → p5) ∨ ((((p3 ∧ False) → p3) → (p4 ∨ p3)) ∧ p5)) ∨ False) → ((p3 ∧ ((p4 ∨ True) → False)) → False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : (p4 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134543304033460082901561883429 : (((((((False → ((p5 → p2) ∧ (p4 ∨ True))) ∧ p2) → p1) ∨ ((p1 ∨ ((p5 ∧ True) ∨ p2)) ∨ p3)) → p5) → p5) ∨ (False → (False ∧ p1))) := by
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
theorem thm_5_vars_317940635520418878781541973700 : (p4 ∨ ((p2 ∨ (True ∧ (((p4 → ((p1 → p3) ∧ ((True ∨ p1) ∧ (p1 ∧ (p1 → p1))))) → (False ∨ p1)) → (p3 → (p1 ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150069035607622332435332796123 : ((True → ((p1 ∨ (((p3 ∨ (p4 → True)) → p4) → False)) ∨ (p5 ∨ (False → ((p3 ∧ p5) ∧ (True ∨ p3)))))) ∨ (((False ∧ p4) ∧ p4) ∧ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699658036780370122037165301754 : ((((((p2 ∨ p3) → (p1 → (((True → p3) ∨ p1) ∨ False))) → p4) → (p5 → ((((p5 ∨ p3) → ((p2 ∨ False) ∧ p1)) → p2) ∧ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52574980230505627808119429377 : ((((p2 → (p1 ∧ ((p5 → (p5 ∧ p4)) ∨ (p5 → p4)))) ∨ (False ∨ p1)) ∨ ((((p5 ∨ p2) ∨ (p3 ∨ (p2 ∧ False))) → p4) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312969899989208283571354046554 : (p3 ∨ (((((p4 ∧ ((p3 → p5) ∨ (p2 ∧ p5))) ∨ (p5 → p4)) ∨ (p4 ∨ ((p5 ∧ (p3 ∧ p5)) ∨ (True → (p3 → p4))))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167684190939886093734272285958 : (((((p1 ∧ p4) → (False ∨ (((False ∨ p4) ∧ p3) → p3))) ∨ p2) ∧ ((p3 → True) → False)) → ((p4 ∧ (p2 ∧ ((p4 ∧ False) ∧ True))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309321432319476668694384285956 : (p2 ∨ ((((((p4 ∨ p5) ∨ p3) ∧ (p1 ∧ (((p5 → (((True ∧ p2) → p2) ∧ p2)) ∧ p5) ∨ p5))) → (p3 ∧ False)) → p3) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115157242007203749894097857996 : (((p3 → ((True ∧ p5) ∧ (p5 ∨ (p1 ∧ ((p4 ∨ p2) ∨ True))))) → (((p1 → (p3 ∧ ((p1 ∧ p1) → p2))) → False) → p3)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799532249115249604986629785397 : (((p1 → (p3 ∨ ((p1 ∨ ((((p2 → p3) → False) → p5) ∨ ((p1 ∨ ((p5 → p3) ∧ (False → p2))) ∨ False))) ∧ (p5 ∨ (p5 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733480559607089624588996145583 : ((((p4 ∧ p2) ∧ (((((p2 ∨ True) → True) ∧ p5) ∨ (True ∧ (p3 → p2))) → (((p2 → (True ∧ (p2 → p4))) ∨ p1) ∧ (p2 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299652271507518625931941919905 : (False ∨ (((((p4 ∨ (p5 → (p3 → p4))) ∧ p3) ∨ (True ∨ (True ∨ ((p4 → True) ∧ ((p3 → p5) ∧ (p3 → False)))))) → (True ∧ p5)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ (p5 → (p3 → p4))) ∧ p3) ∨ (True ∨ (True ∨ ((p4 → True) ∧ ((p3 → p5) ∧ (p3 → False)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120520678418087306704454790942 : ((((False → ((((False → ((p5 → p4) → p5)) → p5) ∧ (p2 → (False ∨ ((p2 → (p2 → p2)) → False)))) ∧ p1)) ∧ p1) ∨ p1) → (p4 ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302766923026406874152982885307 : (False ∨ (p4 ∨ ((p5 ∧ (p5 ∨ (p3 → (True ∧ True)))) → ((p2 → True) → (((p4 ∨ (p5 ∧ (p2 → p2))) → ((p2 ∧ p1) → False)) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731916847151410716365085555109 : ((((p5 → (True ∨ p5)) → (((p2 ∨ p3) ∨ (p5 → p2)) ∧ ((p3 → False) → (p5 ∧ (p5 ∨ (p3 → (p4 ∧ (p5 ∨ (p5 ∨ p1))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64146358870278495585340203828 : ((False ∨ ((p5 ∧ (True ∧ p2)) ∨ (((p2 ∨ p3) ∨ p3) ∨ (((((True ∨ ((p3 ∨ False) ∨ p4)) ∧ p1) ∨ p5) ∨ (False → True)) ∨ False)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49792416871145311758611779276 : (((p5 ∨ ((p5 → ((((p5 ∨ ((((False → p3) ∨ p5) ∧ (p2 ∨ p4)) ∨ p2)) → p1) → p2) ∨ p2)) ∧ p4)) → ((p3 ∧ False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61972276476741717348125409805 : ((p2 ∧ (((p3 ∨ ((p3 ∧ p3) ∧ p4)) ∨ (True ∧ (p2 → p5))) ∨ (((((p5 ∧ p4) ∧ True) → p4) ∨ (False ∧ (p1 ∧ True))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214495967062684631850390741949 : (((p2 ∧ p3) ∧ (p2 ∧ p4)) ∨ (((((p2 ∨ True) ∧ (p2 → False)) ∨ True) ∨ (((p1 ∧ (True ∨ False)) → p1) ∧ (p5 → p4))) ∨ (p5 ∨ p1))) := by
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
theorem thm_5_vars_147283609224577531198800361176 : ((((p4 ∧ ((False ∧ p1) ∨ ((((True → (((True ∧ p2) → p1) → True)) ∧ p3) ∧ True) ∧ p4))) ∨ False) ∨ p2) ∨ (False → (False ∨ (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747521249644534208483836031899 : ((((True → p2) → (((((p5 ∧ (((p1 → p4) ∧ p5) ∧ p3)) ∧ (((p4 → (True ∨ p5)) → p4) → p3)) ∧ p1) ∨ (False ∨ p5)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148689453787018343434957905285 : (((p1 ∧ (p3 ∧ ((p3 → False) ∨ (p3 ∧ p2)))) ∨ ((p4 ∨ (p4 → (((p3 ∨ p1) ∧ p5) ∨ p4))) ∨ p4)) ∨ ((p2 → (p5 → p1)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_68815113622490230885279885579 : ((p4 → (((True → p4) → p1) ∧ (p3 ∧ (((p4 → (((p1 ∨ p3) ∨ (p1 → True)) → p2)) ∧ (p3 → p2)) ∨ (p1 ∧ (p2 ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225056489782239058566229112418 : (((p1 ∧ False) ∧ False) ∨ (p1 ∨ (False ∨ ((False ∧ ((((p5 ∧ p2) ∧ p1) → True) → p4)) → (True ∧ (p4 ∧ ((p3 → True) ∧ (False ∨ p2)))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44937411967196760480164727052 : ((((p5 ∧ True) ∧ ((((p3 ∨ p5) ∧ (True → (p2 ∧ p1))) ∧ (((p3 ∨ p4) → p3) ∧ p4)) → ((False → False) ∧ (p3 ∨ p5)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923632148235874829832209549490 : (((((((p5 → False) ∧ False) ∧ p1) ∨ (p1 ∨ ((p3 ∨ p3) ∧ p5))) ∧ ((p5 → (False ∨ True)) → ((p4 ∧ ((p4 ∧ False) ∨ p4)) ∧ p2))) → p2) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p5 → (False ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h11
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : (p5 → (False ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h21 := h3 h19
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h24 : (p5 → (False ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h25
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h26 := h3 h24
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227025045050641226732275689491 : (((p2 ∨ False) → p1) ∨ (((p3 → (((p2 → ((p3 → p1) ∨ (p1 → False))) ∧ (p2 ∨ False)) ∨ p2)) ∨ False) → ((p3 → (p1 ∨ False)) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336380454294291676504415372005 : (p1 → ((False ∧ (((p1 → True) → ((((p5 → ((p1 → p1) → (p3 ∧ p5))) ∨ p1) ∨ p2) ∨ p5)) ∧ ((False ∧ p5) ∨ (p4 ∨ p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234941476728869729830767975212 : ((True ∧ True) ∧ (p1 ∨ ((p4 ∨ p4) ∨ ((p1 ∧ ((p1 → (((p3 ∧ p5) → (False ∧ (False ∧ ((p3 ∨ False) ∨ p5)))) ∨ False)) ∧ True)) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745187990960470033771263699356 : ((((p4 ∧ p5) → (p1 → (((True → (((False → p3) → False) ∨ False)) ∧ ((True ∧ (p2 → (False ∧ True))) ∧ p3)) ∨ ((p4 ∧ p2) ∨ p4)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198348437679101319222743320220 : ((p2 ∧ ((p4 ∨ p5) ∨ (p1 ∨ (p3 ∧ False)))) ∨ ((False ∧ (((((p5 ∨ p2) ∧ (p1 ∨ (p1 → False))) → p1) → p5) ∨ (p3 → p4))) → p1)) := by
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
theorem thm_5_vars_788025378162517427457636310262 : (((p5 ∨ ((((p2 ∧ True) ∨ (((True ∧ True) ∨ ((p5 ∨ (p5 → (False ∧ (((p1 → True) ∧ p1) ∧ p1)))) ∧ p2)) → p4)) ∧ p4) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182849912096579677663989688889 : ((((p3 ∧ p4) ∧ p4) ∨ (p3 ∨ ((p1 ∧ False) ∨ (p2 ∨ True)))) ∧ (((False ∨ (False ∨ (p3 ∨ p4))) ∨ (((p2 → p2) → False) ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135795383612157212596643703318 : ((((p1 ∧ p4) ∨ (((p5 ∧ (((False → True) → False) ∨ p5)) ∨ p1) → False)) → ((True → p2) → ((p4 → p5) ∨ True))) ∨ (p3 ∧ (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200132901151862027659637960687 : (((p2 → (p3 ∧ p2)) ∧ (p4 ∧ (p1 ∨ p5))) → ((p2 ∧ (p2 → (((((False ∨ (p5 → False)) ∧ p3) ∨ (p2 → p4)) ∨ True) ∨ False))) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62580501387359306617227681048 : ((p3 ∧ (p1 → (((p5 ∨ (p3 → True)) → (p5 ∨ False)) ∨ (((p2 → (((p4 ∧ p1) ∨ p5) ∨ ((p5 ∧ True) → p1))) ∨ p2) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117717447310211824943107664252 : ((p3 ∧ (p2 ∨ ((p2 ∨ p4) ∧ (((p3 ∨ p1) ∧ (True ∨ ((p4 ∧ p5) → p3))) ∧ (((False ∨ p3) → True) ∧ (True ∨ True)))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137651150857010053810444417580 : ((False ∨ (((False ∧ p5) ∨ p4) → (True ∧ (((p1 ∨ p4) → (False ∧ p2)) ∧ ((p1 → ((p5 → p1) → p2)) ∨ p3))))) ∨ ((True ∨ p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_521546938883364075869023273122 : ((((p1 → p2) → ((((((p1 → (p3 ∨ False)) → p4) ∧ p5) ∨ (((p1 ∨ p4) → (p2 ∧ p1)) → True)) → (p3 ∧ p4)) ∨ (False → p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739538728965854064361162921929 : ((((p5 ∧ p2) ∨ (((p5 ∧ (((p1 → p2) ∧ (p5 ∨ p3)) ∧ ((p5 ∨ p1) ∧ (p2 ∧ p5)))) ∨ p2) ∨ ((True ∨ True) ∨ (p3 ∨ False)))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10183382504326799905260087608 : (((p1 ∨ (((p4 → (True ∨ ((True ∧ (True ∧ p5)) ∨ p3))) → p5) ∨ (((p1 ∨ (((p2 ∧ p5) → p2) ∨ p1)) → p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648801291917004886036769527107 : (((((p5 ∨ (((True ∨ (p5 ∧ p3)) → (False ∨ (p3 → p4))) ∧ ((p3 → ((p5 ∧ (p5 → False)) ∨ p5)) → p2))) ∨ p2) ∧ (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864222988326473056125824903 : ((p4 ∨ ((((False ∧ (False ∧ p3)) ∨ p3) ∨ False) ∨ ((True ∨ ((((p2 → True) → (p4 → (p3 ∧ p3))) ∧ p5) ∧ p4)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303891550166433327824281209716 : (p1 ∨ (((((p2 ∨ True) → (p3 ∨ (p5 → (((p1 → p4) ∨ p3) ∧ (p4 → p3))))) ∨ True) ∨ (((True → (False ∨ p2)) ∧ p1) ∧ p2)) ∨ p5)) := by
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
theorem thm_5_vars_238341348019140068930412471624 : ((False ∨ True) ∧ (False ∨ (((p2 ∨ ((((p5 → p1) → p1) ∧ (p2 → False)) ∧ p4)) → (p3 ∧ p1)) ∨ (((p2 → p3) → p2) → (False → p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192461317719145191106261710810 : ((((((p1 ∧ p4) ∨ p4) ∨ p3) ∨ (True ∨ p4)) ∨ False) → ((p1 → (p5 ∨ ((p4 ∧ p1) → p4))) ∨ (p3 ∨ (((p5 ∨ p3) ∧ p5) → p5)))) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h11 =>
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h12 =>
            -- One of the premise coincides with the conclusion.
            exact h10
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h17 =>
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h16
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h31 =>
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h32 =>
          -- One of the premise coincides with the conclusion.
          exact h30
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178570806097072582065579502046 : (((False ∧ (p2 → ((p5 → p1) → p2))) ∧ ((True ∧ (True ∧ p5)) ∨ p4)) ∨ ((((p2 ∨ (p3 ∨ p5)) ∨ True) ∧ (p4 → p4)) ∨ (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_118168986770389298764441182198 : ((False ∨ ((True → p4) ∨ ((p2 → (p3 → p5)) → (((((p3 ∨ p5) → (((p2 ∧ True) ∧ p2) ∨ p1)) ∨ True) ∨ p4) ∨ p3)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138643970575015146110880042038 : ((((p3 ∨ ((True ∧ ((p2 ∧ (True ∨ (p1 ∨ p5))) ∧ (p5 ∨ (p4 → False)))) ∨ False)) ∧ (p2 → (p3 → p5))) ∧ p5) → ((p3 ∧ p2) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16844664149314636277246066484 : (((((p2 ∧ p5) → p4) → ((True → (((p4 → (p2 → p4)) → False) ∧ p1)) ∨ (p5 ∨ (p3 → (p4 ∨ p1))))) ∨ (False → (p5 ∧ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119393700396783984178749466211 : ((p4 → (((True ∧ (p2 ∨ False)) ∨ (((p3 → (True → ((((True ∨ p1) ∧ True) ∧ p4) → True))) → p3) ∨ (False ∧ True))) ∧ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660960339703711870495287148835 : (((((p4 → (True → ((False ∧ (((p1 ∨ ((p2 → p2) ∨ p2)) ∧ p2) → (((p5 → False) → p2) ∧ p4))) ∧ p1))) → p1) → (p2 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300410358812673049249433756425 : (False ∨ ((p4 ∨ (((p4 → p4) → p4) ∧ (((p4 → True) ∧ (p3 → p5)) → (True ∧ ((p2 ∧ True) → (p2 → True)))))) ∨ (p4 ∨ (False → p2)))) := by
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
theorem thm_5_vars_230967048398316865504497167056 : (((p4 ∧ p1) ∨ p1) → ((p3 ∧ p5) ∨ (((p1 → p4) ∧ p3) → ((p2 ∧ (((False ∧ ((False ∨ p1) ∨ p5)) ∨ p4) → False)) → (p5 ∧ p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : ((False ∧ ((False ∨ p1) ∨ p5)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h6.left
    let h14 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h5.left
    let h16 := h5.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : ((False ∧ ((False ∨ p1) ∨ p5)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h20.left
    let h25 := h20.right
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h26 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h27 := h24 h26
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h28 : ((False ∧ ((False ∨ p1) ∨ p5)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h29 := h23 h28
    -- False on the left can always be used.
    apply False.elim h29
    -- Conjunctions on the left can always be decomposed.
    let h30 := h21.left
    let h31 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h20.left
    let h33 := h20.right
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h34 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h35 := h32 h34
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h36 : ((False ∧ ((False ∨ p1) ∨ p5)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h35
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h37 := h31 h36
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305509476293131893579703681542 : (p1 ∨ ((p3 ∧ (((True ∨ True) ∧ ((((p5 ∧ True) ∨ False) ∧ True) ∨ p1)) ∨ False)) ∨ (p2 ∨ ((p4 → p3) ∨ (((p3 ∧ p4) ∧ p5) → p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217898573099197094345656816926 : (((p3 → (p5 ∧ p5)) → True) → (((p5 ∧ (((p2 → (((p4 ∧ p2) ∨ p3) → ((p2 ∨ p2) → p2))) → p4) → p3)) ∧ (p4 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178867695000276209348362208393 : (((p4 → (p5 ∨ p1)) → (p5 ∧ (((True ∨ False) ∨ p4) ∧ (p5 ∨ True)))) ∨ ((((p5 ∧ p1) ∨ p2) → (p1 ∧ p2)) → (False ∨ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261255990275902839519195792234 : ((p5 → True) → (((p5 ∨ p1) ∨ (((((p4 → p5) ∨ p1) ∨ (p4 ∧ (p5 ∨ ((False ∨ True) ∨ True)))) ∧ p5) ∨ ((p2 ∨ p1) ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341669578722445378867214762637 : (p2 → (((((p1 → p4) ∧ ((((True → (p4 → p3)) → (((p5 → p1) → (p4 ∨ p4)) → p5)) ∧ p3) ∨ p4)) ∨ p2) ∨ False) ∨ (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355782512020743990236444456654 : (p5 → (((p1 → (((p4 ∧ (p3 ∨ False)) ∨ p4) ∨ ((False ∨ (p1 → p5)) ∨ ((True ∨ p3) → False)))) ∧ (False → False)) ∧ ((p5 ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46583604584876463779120689796 : (((False ∧ ((((False ∨ False) ∧ (p2 ∨ (True ∨ ((False ∧ p3) ∧ p2)))) ∨ (p1 → (p2 ∨ p2))) ∨ (True → (False ∧ p1)))) ∧ (p2 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233075937639016715806171297153 : ((p4 ∧ (p5 ∨ p1)) → (p2 → (((p1 ∧ (p1 → ((p3 → (p5 → ((p4 → (p2 ∨ ((p5 ∧ True) ∨ p1))) → False))) ∨ p2))) ∨ p5) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186697133359680717697271899155 : (((((p1 ∧ (False ∧ True)) ∨ True) ∨ p1) ∨ ((p1 → p3) ∧ p2)) → ((((((p4 ∨ p5) ∨ p2) ∨ True) ∧ p4) ∨ True) ∨ (p1 ∨ (p2 → p2)))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_986146851519808288529993707052 : (((p2 ∧ ((((p1 ∨ (((p3 ∨ p4) → p1) ∧ p2)) ∨ False) ∧ ((p5 → False) ∧ p5)) ∧ ((p3 ∧ p1) ∨ (p3 ∧ ((p1 ∨ p2) ∧ True))))) → False) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h15 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h16 := h10 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h23 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h24 := h10 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h26 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h27 := h10 h26
          -- False on the left can always be used.
          apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h7.left
      let h32 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h36 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h37 := h31 h36
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h43 =>
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h44 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h45 := h31 h44
          -- False on the left can always be used.
          apply False.elim h45
        case inr h46 =>
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h47 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h48 := h31 h47
          -- False on the left can always be used.
          apply False.elim h48
  case inr h49 =>
    -- False on the left can always be used.
    apply False.elim h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342490780360767414428412331041 : (p2 → (((p4 ∨ p3) ∨ ((p3 ∨ p5) → ((p4 ∨ p5) ∨ ((p3 ∨ p3) ∧ p5)))) ∨ ((p3 ∧ ((False → (False ∨ False)) ∨ (True ∨ False))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642580410569497892650930678865 : ((((p1 ∧ (((p5 → (p1 ∧ ((p5 ∨ p3) ∨ p2))) ∨ (((((True ∧ p2) ∧ p3) → False) ∨ (p5 ∨ False)) ∧ (True ∧ p3))) ∨ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787347107578857865251762899013 : (((p4 ∨ (p3 ∧ ((((((p3 ∧ p1) → (p2 → (True ∨ (((p2 → (False ∧ (p2 ∨ p5))) → p3) ∧ p5)))) ∨ p2) ∧ p3) → True) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315149513090407493991887542416 : (p3 ∨ ((((p5 → p4) ∨ (p5 ∨ p4)) ∨ True) → (((True → p5) ∧ (True ∧ p1)) ∨ ((p5 → p4) → ((p4 ∨ ((False ∧ p5) → p4)) ∨ p1))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51968299933046134556497495514 : (((((p2 → p4) ∨ p3) ∨ ((False ∨ (p4 ∧ ((p4 → p5) ∨ (p4 ∨ p2)))) ∨ p2)) ∨ (((True ∨ p4) ∧ True) → ((p4 ∧ p1) ∨ True))) ∨ p2) := by
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
  cases h2
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
theorem thm_5_vars_62665933807003911562140599595 : ((p4 ∧ (((p2 ∨ ((True ∨ p5) ∧ (False ∨ (p4 ∨ True)))) → ((p2 ∧ ((True → False) → (False → (p2 ∧ (p1 → p3))))) ∧ True)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820040405842337543564169189 : ((p3 ∧ ((p2 → False) ∨ (True → ((p1 ∧ (((((p5 ∧ p2) ∨ p5) ∧ (p5 ∨ (p3 ∧ (p3 → False)))) → p4) ∨ p4)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46877811023098625789133933959 : (((((((p4 ∧ ((((p4 → p1) ∨ p5) ∧ (False → (True ∧ p5))) → (p1 ∨ (p4 ∨ False)))) → p5) ∨ p1) ∧ p3) ∨ p4) ∨ (True ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623982030107915542156704869993 : ((((p2 ∨ (((p4 → (False → p1)) ∨ (p2 ∨ (((p1 ∨ ((True ∨ (p3 → True)) → (True ∧ p5))) → p4) ∧ (p3 ∨ p4)))) → False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



