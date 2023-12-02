variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56813180744040206442726907116 : ((((p4 ∨ p5) → False) ∧ (p3 ∨ (((p4 ∧ ((True ∧ p2) → p3)) → (False → ((p1 → p3) ∨ p4))) ∧ (True ∧ ((p4 → p5) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670384591233635869206236388509 : (((((p3 → (p5 → p2)) ∨ ((p1 ∧ (((p1 ∨ (p4 → (p5 → p1))) → (p1 → (False ∧ False))) → p4)) → p5)) ∨ ((p1 ∧ False) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768984786445563067258125090998 : (((p5 ∧ (((False → p3) → p4) ∧ ((True ∧ False) ∨ ((p2 ∨ (((p5 ∧ p1) ∨ ((False ∧ p1) ∨ (True ∧ p5))) → p5)) ∧ (p4 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240444581432342174019284938734 : ((p5 ∨ True) ∧ ((((p5 ∧ True) ∧ ((p4 → True) ∨ (p4 ∨ (p3 → p5)))) → (False ∧ False)) ∨ (((True ∧ p3) ∧ (p4 ∧ (p4 → p5))) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h3.left
  let h7 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633479243912312741589373122269 : ((((((((p5 ∨ (p4 ∧ False)) → ((p4 ∨ p1) ∨ ((p5 → True) ∧ True))) ∨ (False → True)) ∨ ((p2 ∧ p2) ∧ p3)) ∨ (p5 → p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115112507712812846849791281028 : (((((((p4 ∧ p2) ∧ True) → False) → (p4 ∨ (p3 ∨ False))) → True) → (((False → p1) → (p2 ∧ p1)) ∨ ((p5 → True) ∨ p1))) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50777795095254358741372252672 : (((p2 ∨ (p4 ∨ ((True ∨ p3) ∨ (p1 → (((True ∨ (p3 → p2)) ∨ (False ∨ True)) → (True ∧ p4)))))) → (((True → True) ∨ p5) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142280198151785363132068009399 : ((p2 ∧ (((p5 ∨ p3) ∨ p4) → (((p5 → True) ∨ False) → ((True ∧ (((p2 → p4) → p1) ∧ (p3 → p5))) → p3)))) → (True ∧ (p1 → p1))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65040566461402090793185777539 : ((p2 ∨ (True ∧ (((p3 → (False ∨ (p2 ∨ ((p5 ∨ p2) ∨ (p1 → p3))))) → (p3 ∨ p4)) ∧ ((p5 ∧ ((p3 → True) → p1)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238100136273529499984917097620 : ((True ∨ p2) ∧ (p2 ∨ ((((False → p2) → False) ∧ p4) ∨ (((False ∧ (((True → (p4 → p3)) → False) ∧ p2)) ∧ (p1 → (p3 ∧ p2))) → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301156125639121627881600279436 : (False ∨ ((False ∧ (((p1 ∧ p4) ∨ (p2 ∨ False)) ∨ p3)) ∨ (((p2 → p2) ∧ p5) ∨ (True ∨ ((p5 ∧ (p3 ∨ ((p4 → p4) ∧ p3))) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606416754086397159424948961273 : (((((((False ∨ p5) ∨ (p1 ∨ ((p1 ∧ True) ∨ (((p1 ∨ p3) ∧ (((False ∧ p3) ∧ (p2 → p1)) ∧ p2)) ∧ False)))) ∨ p2) ∧ p2) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_136466997924507920158744550918 : ((((p3 ∧ p4) ∧ p2) ∧ (True ∧ (False ∧ (p1 → ((p4 ∧ ((p4 ∨ (p5 ∨ p3)) → p1)) ∧ ((p1 ∨ True) → True)))))) ∨ ((p4 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256953914006008117700353005248 : ((p1 ∨ p5) → (((p1 ∨ ((p5 ∧ False) → ((p3 ∨ False) → (p3 ∨ p1)))) ∧ ((p3 ∧ ((p1 ∧ p3) ∨ True)) ∨ (p4 ∨ p5))) ∨ (p1 ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41715147812178970794306683839 : ((((((True ∧ p3) ∧ p4) ∧ p5) ∧ ((p2 ∧ ((p1 ∧ (p2 ∧ (p3 ∧ p2))) ∨ (p1 ∨ ((p5 ∧ (p3 → p1)) → p1)))) → p3)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111963765585533814661798914113 : ((((p3 ∧ (False ∨ (((p3 ∨ True) ∧ p4) ∨ p5))) → ((False ∨ (((True ∧ (p2 ∧ False)) → p2) → p5)) ∨ (p1 ∨ p3))) ∨ False) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316541500507350451081943024831 : (p3 ∨ (p3 ∨ (((((p4 ∨ ((p2 ∧ False) ∧ p3)) ∧ ((p5 ∧ (((True ∧ p5) → (p1 ∨ p3)) ∨ (p3 ∧ p3))) ∧ p1)) ∨ p2) ∨ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774071240258343412984862977259 : (((False ∨ ((((((p1 → (p5 ∨ (p1 → p3))) ∧ p2) → p1) → False) → ((p4 ∨ p1) → (p4 ∨ ((p4 ∧ p5) ∨ p2)))) ∨ (p4 → p2))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (((p1 → (p5 ∨ (p1 → p3))) ∧ p2) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h5
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39082546049960616024560557217 : ((((p3 ∨ p1) ∨ ((((True ∨ False) → False) → p4) → ((p3 ∧ (((True → True) → p3) ∧ (((p5 ∧ p2) ∧ p2) ∨ p5))) ∨ p2))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112161792791821634734831761698 : (((p3 ∧ (((((p2 ∧ (((False ∧ p4) ∨ p1) ∨ ((p5 → (p3 ∨ p5)) → p2))) ∧ (p4 ∨ p1)) ∨ p5) ∨ True) ∧ p5)) ∨ p3) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301267778344493731869771860113 : (False ∨ ((p3 ∨ (p1 → (False ∨ (p3 ∧ p1)))) ∨ (((False ∧ (((False ∧ p4) ∧ (p3 ∧ ((p3 ∧ p3) ∧ False))) → p3)) ∧ p1) ∨ (False → p2)))) := by
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
theorem thm_5_vars_61236111272921274232775040347 : ((False ∧ (p3 ∧ ((p2 ∨ ((((p5 → ((p3 ∧ True) → p5)) → (True ∧ True)) ∨ (True ∨ p1)) → ((p1 ∧ (p2 → p1)) ∨ p1))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774349350958914590353034791705 : (((False ∨ ((p5 → (p3 ∧ (((True → (((p1 ∨ p4) ∧ p3) → (p2 ∨ (p4 ∧ False)))) → p2) ∨ True))) ∧ (((p3 → True) ∨ False) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53467293750393460713888192048 : ((((p2 ∨ False) → ((((p2 ∧ (p4 ∧ False)) ∨ p3) ∨ p4) ∨ p2)) → (((((p5 ∧ p2) → False) → p5) ∨ (p4 → p4)) ∨ (False → p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356015005338322563383310403212 : (p5 → (((p1 ∧ (((p3 ∨ ((p5 ∨ ((p1 ∧ (p3 ∨ p3)) → False)) ∧ (p1 → p2))) → p3) → p4)) ∨ p1) ∨ (p1 ∨ (p1 ∨ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336348027968693197174124374569 : (p1 → (((p1 → p1) ∧ (((p5 → (p3 ∨ ((p2 ∧ p4) ∨ p3))) ∧ ((True ∧ (p5 ∨ p4)) → (False ∧ p5))) → ((p5 → p2) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328422922401839442134321126710 : (True → (((p3 ∧ (p2 → p2)) → (((False ∨ (p2 ∨ p3)) → (p4 ∨ p4)) ∧ (p4 → (p2 ∧ True)))) ∨ (p5 ∨ (True → (p3 → (False → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256174873790039111289469032530 : ((False ∨ True) → (((((p4 ∨ p4) ∨ p2) ∨ (p3 → (True ∧ True))) ∧ (p3 ∨ False)) ∨ ((False → ((p3 ∧ p5) ∧ p4)) ∨ (p1 ∨ (p4 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166903834704001297577362622216 : ((((p3 ∨ (p5 ∧ (p2 → (p5 ∧ (p4 ∧ True))))) → (p4 → (p5 ∧ (p3 ∧ False)))) ∧ p1) → (p2 → ((p5 ∧ (True → (p4 ∨ p4))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135322547381087671563516376266 : ((((True ∧ ((p1 → p2) ∨ ((p5 ∨ (p1 ∧ (False ∨ p4))) ∨ p3))) → (p5 ∧ (p2 ∨ True))) ∧ (False → (True ∨ False))) ∨ (p3 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255479582753754790351292556593 : ((p5 ∧ p2) → (((p3 ∧ ((((((p1 ∨ False) ∧ (False → p1)) ∨ p4) ∨ (p5 → p4)) ∨ p3) ∨ p2)) ∨ ((p2 ∨ (False ∨ p4)) → p5)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351774628967186303203361176474 : (p4 → ((False → ((p1 ∧ ((((False ∧ p1) → p5) ∨ (False ∨ p4)) ∨ False)) ∧ p5)) → (((p5 ∨ p1) ∨ False) ∨ ((True → False) ∨ (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145613415415011209453953135686 : (((True ∧ (p2 → p1)) → ((p5 ∧ (p3 → (p3 ∨ p3))) → (p1 ∨ (p4 → (((p3 → p2) ∨ True) ∨ p1))))) ∧ (p1 → (p1 ∨ (True ∧ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199948811665370573471601604257 : (((False ∨ ((True → p5) ∨ False)) ∨ (p3 ∧ p4)) → ((False ∧ (p4 ∨ (((p1 ∧ (p5 ∨ (p3 ∧ p3))) → True) → (True → p4)))) ∨ (True ∨ False))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- False on the left can always be used.
        apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150310110247756862775021049281 : ((p4 → ((p1 ∧ p5) ∨ (p3 ∧ (((False ∧ ((p2 → ((p5 ∨ p2) → p5)) ∧ (p1 ∨ p4))) → True) → p3)))) ∨ (((True → False) → p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156926957354155254819594041023 : ((((False → ((p4 → p3) ∨ ((((p3 ∨ ((p5 ∨ p5) → True)) ∨ p4) → p5) → p5))) → p2) ∨ True) ∨ (((p4 ∨ (p3 ∧ p5)) ∨ True) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151230510573295258154084983540 : (((((p4 → p3) → p1) → (p5 → (p5 ∧ ((((False ∧ (p3 ∨ p4)) ∨ (p3 ∧ p3)) → False) → False)))) → p3) → ((p3 ∨ (p2 ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_343401616012827627625799757653 : (p2 → ((p3 ∧ p4) ∨ (((p1 ∨ (True → p5)) → (p3 ∧ ((((p4 ∨ p1) → p4) → (p1 ∨ (False ∨ p5))) ∨ (True ∨ (True → p4))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164820904858774297513402577798 : ((((p4 → False) ∨ (((p3 ∧ True) ∧ (p4 ∨ p5)) ∨ ((False ∨ (p1 → p2)) ∧ p1))) ∨ True) ∨ ((p5 → (p2 ∨ (p2 ∨ (True ∧ p1)))) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52426926268808340254256605543 : ((((p3 ∨ p1) ∨ (((p4 ∧ (p2 ∧ (p5 ∧ p1))) ∨ p4) ∨ (True ∨ p2))) ∧ (True ∧ (((p3 → p3) → False) ∨ (p2 ∧ (False → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41832328627041628902161798128 : ((((False ∧ (p3 → p3)) ∧ (((((((p5 ∧ p2) → True) ∨ (p3 → (p5 → False))) ∨ False) ∨ p3) ∧ p4) ∧ ((p4 ∧ True) ∧ p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354926664056588200500630769803 : (p5 → ((p3 ∨ ((((((True → (False → p2)) ∨ p1) ∨ (p3 → (p4 ∨ ((((p1 ∧ p3) → p1) ∧ p2) ∧ p2)))) ∨ p1) → p2) ∧ p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788525720886828102243102225020 : (((p5 ∨ ((p3 ∨ (p2 ∨ (p5 → (p1 ∨ ((((p2 → (p1 ∨ p3)) → True) → ((p3 → (p4 ∨ True)) ∧ (p1 → False))) ∨ True))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308516713314355095769939778373 : (p2 ∨ (((p2 ∧ ((p5 ∧ ((p1 → ((((True ∨ p2) ∧ p5) → False) ∧ False)) ∧ p2)) → p1)) ∨ ((p2 → (p1 ∨ p2)) ∧ (p3 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803996331832383612054399879199 : (((p3 → (((p2 ∨ ((((p1 → (p3 → False)) ∧ ((p3 ∧ (p1 → False)) ∧ False)) ∨ p2) ∧ (p1 → p2))) ∨ p2) ∨ ((p4 ∨ p3) ∧ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779109746201854170532230833171 : (((p2 ∨ (((((p2 ∨ (((True ∧ (((p2 ∨ (False ∨ (p2 ∨ p1))) → (False ∨ False)) → p2)) ∧ True) ∧ True)) → p1) ∨ p2) ∨ p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248259117482396381354919488837 : ((p2 ∨ p2) ∨ ((((p4 ∨ ((False → p1) ∨ p1)) ∨ p5) → ((((p4 → (p3 ∨ p1)) ∨ p2) ∧ p4) → (False ∨ ((p5 ∧ p2) → True)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199075752587491348129546281558 : (((((p5 ∨ p3) ∧ (p2 ∨ p1)) → p3) ∧ p2) → ((p5 ∨ ((p3 ∨ ((True ∧ p5) ∨ (((p5 ∧ True) ∧ p3) → p4))) → (p4 ∧ True))) ∨ p2)) := by
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
theorem thm_5_vars_135848081048696575677448209480 : (((False → (((p2 ∨ p2) ∨ ((p1 ∨ p5) → p1)) ∧ (p2 → False))) ∧ (False ∨ (p2 ∨ (p2 ∧ (False ∧ (p3 → p5)))))) ∨ ((True ∨ p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67801686542674278968548362357 : ((p2 → (((((p4 → (True ∧ False)) → False) ∧ ((p1 ∨ ((p2 ∧ p2) ∨ p4)) ∧ (p2 ∨ p1))) ∧ ((p1 ∨ False) → (p4 ∧ False))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716568098670458968119426124843 : (((((p2 → True) ∨ (p1 ∧ p1)) ∧ ((((False ∧ p5) ∨ p5) ∨ (p2 ∧ (p5 ∨ p3))) ∨ (True ∨ (((p4 ∧ p2) → p2) ∨ (p5 ∧ False))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136368710993900992720002156252 : ((((p3 ∨ (p4 ∧ True)) ∨ p4) ∨ ((p2 ∨ True) ∧ (p4 ∨ ((p2 ∧ ((False ∧ ((p2 → p3) → p3)) → p2)) ∨ True)))) ∨ (p3 ∧ (p4 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649275586247124639186283399794 : (((((p3 ∧ ((((p4 ∧ True) → ((((p4 ∧ p4) → p3) ∧ p2) ∧ p5)) ∨ p1) → (p5 → ((p2 → p5) → p4)))) → p1) ∧ (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172795698012134140050806370955 : (((p3 → True) → (((p3 → (p1 → p3)) ∨ p1) → (((False → p4) ∨ True) ∧ p3))) ∨ (((p2 ∧ ((p1 → p5) ∨ (False ∨ False))) ∧ True) → p2)) := by
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
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742814496564659464855311578288 : ((((p3 → p1) ∨ ((p1 → (False ∧ p2)) → ((((p1 → (((p1 ∧ False) ∨ p3) → p4)) → (p4 ∨ (p1 → False))) ∨ p2) → (p1 → p3)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700726190655123167406811807826 : (((((((p3 ∨ p4) ∧ ((p3 → p5) → p4)) ∨ p1) ∧ False) ∧ (p3 ∨ (p1 ∧ (True ∨ (p3 → (True → (True → (p5 ∨ (True ∧ p3))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157690364819388682332119378023 : (((p2 → (((((True → (False ∧ p2)) → p4) ∧ p4) ∨ p1) ∨ (p1 ∨ p3))) ∨ ((p4 ∧ p1) ∧ p2)) ∨ (((p4 ∧ p4) ∧ (p4 ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67463044015800435792975788887 : ((p1 → (((True ∧ (p2 ∧ p3)) ∧ (((p5 ∧ (False ∧ (p4 → p4))) → True) ∨ (p1 ∨ (False → p5)))) → (p3 ∧ ((True → p5) → p5)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h20 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h22 := h13 h21
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h26 := h13 h25
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h29 := h13 h28
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703836639014741679269075830759 : (((((((True → (p1 → (False → p4))) → p4) → p2) ∨ p4) → (((p3 ∨ p5) ∧ p2) ∨ (((p3 → (False → p4)) → (p5 ∧ p4)) → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_116310069824229587290675346147 : (((p3 → (False ∨ p2)) ∨ ((((False ∨ (p2 ∨ (p1 → p2))) ∨ (p4 ∨ p2)) → p3) ∨ ((p2 ∧ (p3 ∧ False)) → (True → p3)))) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312994712450074144280494485978 : (p3 ∨ ((((((((p5 → False) ∧ p2) → (False ∨ p3)) ∨ (((p4 ∧ True) ∨ (True → p2)) → False)) ∨ ((True ∨ True) → True)) ∨ p4) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57329936116478763771397915621 : (((p1 ∧ (p2 ∧ p5)) ∨ (((p5 ∨ (False → True)) → ((True ∧ p2) → ((((((p3 ∧ p3) → False) → p2) ∨ p4) ∨ p1) ∨ p4))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114536411572512328616247234785 : (((p1 → (((p1 → p4) → (((p1 ∨ ((p4 ∧ p1) ∨ (True ∨ p4))) ∧ p1) ∧ True)) ∧ False)) → ((p1 ∧ (p5 → p5)) ∨ p1)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143393671973598187806832573500 : ((p5 → ((p4 → (p1 ∧ (p2 → (p3 ∧ (((p5 → False) ∨ p1) ∧ p5))))) ∨ (p1 → ((p3 ∧ (True ∨ False)) ∧ False)))) → (p1 ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167329693555455315715611061868 : ((((p3 → (p4 ∨ (((p1 ∨ p3) → False) → ((p1 ∨ False) → p4)))) ∨ (True ∧ p4)) → p5) → (p2 ∨ ((p2 ∧ ((p4 ∨ p3) → p2)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 → (p4 ∨ (((p1 ∨ p3) → False) → ((p1 ∨ False) → p4)))) ∨ (True ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (p1 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343604057805193684166301747678 : (p2 → ((p4 → p4) → ((p2 ∧ ((((((((True → False) → p5) ∧ (p3 ∧ p4)) → (True ∧ (False ∨ False))) ∨ False) ∨ False) → False) ∨ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114667771307831975383694691546 : ((((p1 ∧ p2) ∨ ((p5 → (True ∨ (p4 → (p2 ∧ p4)))) ∧ ((p3 → False) ∧ p3))) ∨ ((True ∧ (False → True)) ∧ (p3 → p5))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303167277036630936192524793108 : (False ∨ (p4 → ((True ∧ ((((True ∨ (True ∧ (True ∨ False))) ∧ p3) ∨ (((((p1 → (p4 → p3)) ∧ p5) ∧ p1) ∧ p2) ∧ p4)) ∨ p4)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38472133549536671123143801888 : ((((((True ∨ False) ∨ (((p2 → p2) ∧ False) ∧ (p1 ∧ p4))) ∧ False) ∧ (((((p4 → (False ∨ False)) ∨ True) → False) ∧ p5) ∧ p1)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972035741872790104797960765162 : ((((True ∨ False) → (((False ∨ (True ∧ ((True ∨ (((p2 ∨ (True → (p2 ∨ False))) → p1) → (p1 ∨ p1))) → p4))) ∧ (p4 ∨ True)) ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656591441190893104518977013330 : (((((((True ∨ p1) → False) ∧ ((False ∧ p1) ∨ p4)) ∨ (p1 ∧ ((((True ∧ (False → p2)) → False) → p2) → (p5 ∧ p3)))) ∨ (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703413415379308705575374811325 : ((((p2 ∨ (p1 ∨ (p4 ∨ ((p4 ∧ p5) ∨ (p2 ∧ p4))))) ∨ (((p1 → (True → p5)) → (p4 ∧ (p5 ∧ p3))) → ((True ∧ True) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225412633411561994380281235204 : (((p3 ∨ False) ∧ p3) ∨ (((((p1 ∧ False) ∨ (True → p1)) ∧ ((False ∨ p5) ∨ ((True ∧ (p3 ∨ (p1 → (True → p3)))) ∨ p4))) ∨ p1) → p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h12 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h13 := h8 h12
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h19 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h20 := h8 h19
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h22 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h23 := h8 h22
            -- One of the premise coincides with the conclusion.
            exact h23
        case inr h24 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h25 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h26 := h8 h25
          -- One of the premise coincides with the conclusion.
          exact h26
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694423008271104946909055776460 : (((((p3 ∨ p4) ∨ (((False → ((p3 ∧ (p2 ∨ True)) ∧ True)) → p1) ∨ p1)) ∨ ((p1 ∨ ((p3 ∨ p4) ∨ (True → (False → False)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304775378101578485348154945524 : (p1 ∨ ((p3 ∨ (((((True ∧ ((True ∨ (p4 → True)) ∧ p1)) ∨ ((p4 → p4) ∨ p5)) ∧ p5) ∨ p5) ∧ ((p2 ∧ p5) ∧ p1))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755915513310563416145848447809 : (((p1 ∧ ((((p5 ∨ False) → ((True ∨ p1) ∧ ((((p3 ∧ (p4 → p4)) ∧ (False → p2)) → p2) → (p2 ∨ p3)))) ∨ (p3 → False)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160767615593271593133135798009 : ((((p5 ∨ (True → p4)) → (p1 ∧ p1)) ∧ ((p4 → p1) ∧ ((((p1 ∧ p3) → p1) ∨ p5) → p5))) → ((p5 → p2) ∨ ((False ∨ p1) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 ∧ p3) → p1) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : (p5 ∨ (True → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184904543849194787501879186436 : ((((p2 ∧ False) ∨ p5) ∨ (((p1 ∨ p2) ∧ (p3 → p2)) → p3)) ∨ (((False ∧ p5) ∨ (False ∨ ((p3 ∨ (p3 ∧ p4)) ∧ (p4 ∧ p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60251798999085285845826568121 : (((False → False) → (((p5 ∧ ((False → (False → (p4 ∧ (p5 ∨ (p4 ∧ False))))) → p1)) → (False ∧ p2)) ∨ (True → ((p2 ∧ p3) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158567951796697353315238725220 : ((True ∧ ((((p4 ∧ p1) ∧ ((False ∧ (True → p3)) ∨ p5)) ∧ (p2 ∧ p1)) ∧ ((p3 → p5) ∨ p4))) ∨ (False ∨ (((p2 ∧ p2) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232968008667791757217628979077 : ((p3 ∧ (False → False)) → (((True → p2) ∨ (p4 ∨ p1)) → ((p2 ∧ ((p1 → p2) ∧ (((p2 → p2) ∧ (p5 → True)) → p1))) → (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h12 : ((p2 → p2) ∧ (p5 → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h12
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h20 : ((p2 → p2) ∧ (p5 → True)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h23 := h8 h20
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h1.left
      let h26 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308688491945648696044544352076 : (p2 ∨ ((p1 ∨ ((p5 ∧ p5) ∧ ((p4 ∨ ((False ∧ p2) → p2)) ∨ (p1 → ((p3 ∧ (((p2 ∨ p3) ∧ (p4 → p2)) ∧ p3)) ∧ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256821715841353817537550346179 : ((p1 ∨ p3) → ((((((p1 ∨ ((p5 → p4) ∨ p3)) ∧ True) ∨ p3) ∨ p2) → (((True ∧ (p4 ∧ True)) ∨ (False ∧ (False ∧ p3))) → p2)) ∨ True)) := by
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
theorem thm_5_vars_184596738151434483068738123571 : (((p4 → (((True → p3) ∧ p3) ∨ (p2 ∧ False))) → (p4 ∨ False)) ∨ (((p2 ∨ p1) → p1) ∨ (((True ∨ p4) ∨ True) ∨ ((False ∨ p3) → p4)))) := by
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
theorem thm_5_vars_47140460842554213298639998621 : ((((True ∧ ((p5 ∨ p2) ∧ ((True ∨ (p5 ∨ p2)) ∨ ((False ∧ (p5 ∧ p4)) ∨ p3)))) ∧ (((True ∨ p4) → True) → False)) ∨ (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166492464478174726301689495504 : ((p3 ∨ ((p1 → p3) ∨ (p1 → (True ∧ ((True ∧ ((p3 ∨ False) → True)) ∧ (p3 → p2)))))) ∨ (p4 ∨ ((p1 ∨ p1) ∨ (False → (p1 ∧ False))))) := by
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
theorem thm_5_vars_356459191209415610261548590841 : (p5 → (((((True ∧ (p1 ∧ p4)) ∧ (p3 → (p4 ∧ p5))) ∨ p5) ∧ p2) → ((((p4 → p3) → True) → ((True → p3) ∨ p4)) ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310407085467782078082643111090 : (p2 ∨ ((p2 ∨ ((p2 ∨ p2) → ((p3 ∨ p3) ∨ False))) ∨ (((p4 ∨ (((True ∨ p1) → False) ∨ p2)) ∨ p4) → (((p1 ∧ p2) → p3) → True)))) := by
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
theorem thm_5_vars_114639555502516585602065138812 : ((((p1 ∨ ((p1 → ((p3 ∧ p3) ∨ p2)) ∧ (((p3 ∨ p5) ∨ p5) ∨ p2))) → p5) ∨ ((p1 → ((p3 → True) ∨ p1)) ∧ True)) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244637601475910036036508818549 : ((False ∧ p5) ∨ (((p2 ∧ (p4 ∨ p3)) ∧ ((p2 ∧ p4) → (p2 ∧ False))) ∨ ((p5 ∧ ((p1 ∧ p2) ∨ (p5 → True))) → ((True → True) ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51197591806973382757144868730 : (((((False ∨ (p2 → False)) ∧ (p1 ∧ ((p1 ∧ p2) ∨ p5))) ∧ (False → ((p2 ∨ p5) ∨ p5))) ∨ (False → (p1 ∨ (True ∧ (p3 ∨ p2))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697576341561367444093383505046 : ((((False ∨ (p5 ∧ (p3 ∨ ((p1 ∨ (False ∨ False)) ∧ (p4 → p2))))) ∧ (((((((p2 → True) ∨ p2) ∨ False) ∧ True) ∧ p5) → p1) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52442391296161811529748370207 : (((p1 ∧ (((p4 ∨ (False ∨ (((p2 → p1) ∧ p2) → p1))) ∧ False) ∧ p3)) ∧ (p5 ∧ (True → (p3 ∧ ((True ∧ (True → False)) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304061440709449607418062545184 : (p1 ∨ ((False ∨ (p1 → (((p2 ∨ (((True ∧ ((p4 ∧ p5) → (True ∨ p4))) → (p3 → p1)) → (p5 ∨ p3))) ∨ p3) ∨ (p1 ∨ p3)))) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228189660225464722533532103884 : ((p5 ∧ (p4 ∧ p2)) ∨ (((p3 ∨ (p4 → (p5 → ((p1 ∧ ((((True ∨ (False → p3)) → p2) ∧ p3) → p1)) ∨ (p4 ∧ p4))))) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p4 → (p5 → ((p1 ∧ ((((True ∨ (False → p3)) → p2) ∧ p3) → p1)) ∨ (p4 ∧ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135654390731149436259617472740 : (((((p2 ∧ p3) → p2) ∧ (((p4 ∨ (True ∨ (p4 → p2))) ∨ False) ∨ (False ∨ p3))) → (((p5 ∨ p5) ∨ p1) ∨ p4)) ∨ ((p2 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38280747004730721400300026307 : (((((False → (((p1 → False) → (p4 → p1)) → False)) ∧ ((p1 → p5) ∨ ((p2 ∨ p4) ∧ False))) ∨ (p1 → ((p1 → p1) → p2))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354863078823914418354934421151 : (p5 → (((p2 → p5) → ((p1 ∧ ((p4 ∨ (False ∨ ((p2 ∨ p2) ∨ (False ∨ p2)))) ∧ (p5 → ((p1 → p3) → True)))) ∨ (True ∨ p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48441374572431486154993521954 : (((p4 → (p2 → (((p2 → (p1 ∨ p5)) ∧ (p3 ∨ ((((p3 ∧ p2) ∧ (p5 → p5)) → p5) ∨ (False ∧ p1)))) ∧ p1))) → (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115066632918451897015090174798 : ((((p5 ∨ (p1 ∨ (p3 ∨ p1))) → ((p2 ∨ (p5 ∧ True)) ∧ True)) ∨ (True ∧ (p2 → (False ∧ ((True ∧ (p1 ∨ False)) → False))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



