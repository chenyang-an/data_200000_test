variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345411481004621810853606604209 : (p3 → (((((True ∨ (True ∧ (p4 ∧ True))) ∨ p5) ∧ ((((((p2 ∧ False) ∨ True) ∧ p3) → p2) ∧ (p5 → p3)) → (p4 → p3))) → p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681641907042900842883310021696 : ((((p3 → (((p4 ∨ (True → ((True → p3) ∧ (p1 ∨ (True ∨ p1))))) ∧ p1) ∨ (p1 ∧ (p1 → False)))) → (((p5 ∨ p4) → p5) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734646638211553799184421619952 : ((((p1 ∨ p4) ∧ (((((p1 ∨ (True ∨ ((True ∧ p1) ∧ False))) → p1) ∧ (p4 ∧ (p4 ∧ p4))) ∧ (p4 ∨ (p1 → (True ∧ p1)))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115869156761489480056951270543 : (((p5 → (p1 ∨ (False → False))) ∧ (p5 → (p1 → (((False ∧ p3) ∧ ((p3 ∧ p2) ∨ p5)) ∨ (True ∧ (True ∨ (True ∧ True))))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45121062517449869961850227234 : ((((True → True) → ((((True ∨ p4) ∨ (((p4 ∧ False) ∨ False) ∨ ((p5 ∨ (p3 → p1)) ∨ p1))) ∨ p1) ∧ (p4 ∨ (p1 → True)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808371159847423725359272170313 : (((p4 → (p1 ∨ (((p4 → (((p3 ∨ False) ∨ (((p3 ∨ p5) → p5) ∧ (p2 → (False ∨ p3)))) ∧ (p1 → p5))) → (p3 ∨ p1)) ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_117036643403830627127674152266 : (((p3 ∨ p1) → (((p4 ∨ False) ∧ (True ∧ ((((p5 ∧ p3) → (p2 ∨ p5)) → (True ∧ (p3 → p1))) ∨ (p4 → p3)))) → False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148744585819747836561512502652 : (((((p2 → p4) ∧ True) → (p5 → p1)) ∧ (False ∧ ((p5 → True) ∧ (((False → (p4 ∧ p5)) → p1) ∧ True)))) ∨ (((p2 ∧ p4) ∨ p4) → p4)) := by
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
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457092965220320924461498772562 : (((((((((False ∧ p4) ∧ p3) ∧ ((False → False) ∨ p4)) ∧ False) ∧ (p3 → (p1 ∨ True))) ∧ True) ∨ (True ∨ ((p1 ∧ (p2 ∨ p3)) ∨ p5))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_178001909069817120760779758592 : (((p2 ∨ ((((False → False) ∧ (p3 → False)) → (p1 ∧ True)) → p3)) ∨ True) ∨ ((True → (((True ∨ (p1 ∨ True)) ∨ (True ∧ p3)) ∨ p5)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628621484278971844701172639297 : (((((p3 ∨ ((False ∨ ((p5 ∨ ((p4 ∨ ((p2 → (p1 ∨ ((p3 → True) → (False → p4)))) → p3)) ∧ p2)) ∧ p4)) ∨ p5)) ∧ p2) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112555639107355830202504770019 : (((((p3 ∨ False) ∨ (((((p1 ∨ p4) ∧ (p3 ∨ p5)) ∨ True) ∨ ((False → False) ∧ ((False ∨ p4) ∨ p1))) ∨ p2)) → p2) → p5) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133826907072022376039289815119 : ((((p1 → p2) ∨ ((((((p1 ∨ p1) ∧ p4) → p5) → (p5 ∧ False)) ∨ True) ∧ (((False ∧ p1) → p2) ∧ p3))) ∧ False) ∨ (p3 → (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618059390218771546542240938397 : ((((((p3 ∧ True) ∧ (p2 ∨ p5)) ∧ (((True ∧ (p2 → (p4 ∧ p2))) ∧ ((p2 → (p1 ∨ p3)) ∧ ((True ∧ p2) ∧ p5))) ∨ p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_179211747139255050701730861734 : ((p4 ∧ ((((p1 → True) ∧ (p3 → p3)) → ((p5 ∧ p1) → p5)) → p5)) ∨ ((p2 → ((p3 ∧ p2) → ((p2 ∧ p4) ∨ True))) ∨ (p4 → p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305303841136444106634285176485 : (p1 ∨ (((((p5 ∧ p2) ∨ p4) ∧ (False → False)) ∨ (p4 ∧ (p5 ∨ ((p1 → False) → (p1 ∨ p4))))) ∨ ((p4 ∧ False) → (True → (p3 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114512625190143591371790660236 : ((((p2 → p2) ∨ (True ∧ ((p2 → (p4 → (True ∧ (p4 ∨ (p1 → p5))))) → (p5 → True)))) → (((True → p5) ∧ p1) ∨ p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54446034533584856439265692977 : ((((((p1 ∨ p5) ∨ (p1 ∧ False)) ∨ p2) → p3) ∨ (p1 ∨ ((((True → ((p2 ∨ p1) ∨ p3)) ∨ p3) ∨ (False ∨ (p2 → True))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178923810024918967595084757789 : (((p3 → False) ∧ (p5 ∨ (((p5 → (p3 ∧ False)) → p5) ∨ (p4 → True)))) ∨ (((((False ∧ p3) ∧ p5) ∧ (p4 → p4)) ∧ True) → (p1 ∨ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231734966226214301829966876814 : (((p2 ∧ p4) → p5) → ((p1 → (p4 ∨ False)) ∨ (True → ((p5 ∨ False) → ((p3 ∨ False) → ((p1 ∨ p5) → (p2 → (p4 ∨ (p2 ∨ p1))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678162720206100095666078957613 : ((((((p1 ∧ ((p5 → (p2 ∧ ((p4 ∨ p3) → p5))) ∨ False)) → p2) → ((p3 ∨ p5) ∧ (p1 ∧ p1))) ∨ (True ∨ ((p5 ∧ p3) ∧ p1))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_136239314912409895778155071109 : ((((True ∧ p1) → ((p3 → p5) → p4)) ∨ (True ∧ (((((p3 → p1) → ((False ∧ p1) ∨ p3)) ∧ p1) → False) → p5))) ∨ ((p5 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196930647170003434468715002485 : ((((p1 ∨ ((p4 ∨ p4) ∧ False)) ∧ p5) ∨ True) ∨ (p5 ∧ ((((p1 ∨ (p3 ∧ p5)) ∨ True) ∧ p5) → (((p4 ∧ p3) → (False → False)) ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136510139163461859246723652716 : (((p3 ∧ (p2 → p2)) ∧ (False ∨ ((p5 ∧ p3) ∨ (((p3 ∧ p5) ∨ (p3 → (True → (p5 → (p1 ∧ True))))) ∧ p1)))) ∨ ((p4 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586978017012295613512551170049 : (((((p3 ∨ (False ∨ (p2 ∨ (p4 ∨ (True ∧ ((p1 ∧ ((p3 ∨ (p3 → (p5 → (p2 ∨ p4)))) → (p5 ∧ p5))) → p5)))))) ∧ True) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124715596060871947827928832428 : ((((p4 → (p4 → p1)) ∧ p4) ∧ ((((p5 ∧ p3) ∨ (True ∧ (False ∧ (True → ((p4 → p4) ∨ p4))))) → p5) ∨ (False → p4))) → (p1 ∨ p2)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804661727815692661524120013251 : (((p3 → ((True ∧ (True ∧ (p4 → p5))) → (((p3 → p4) ∨ (((p1 ∨ p5) → ((p5 ∨ p2) ∧ (p3 ∧ p3))) ∧ (p4 ∧ p2))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134126872394129906994063638378 : ((((p2 ∨ (p3 → (((True ∨ p5) → (((p5 → p2) → p3) → False)) ∨ (p1 ∧ (p3 ∨ p4))))) ∨ (p1 → p3)) ∨ p2) ∨ (True ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56306185162318430751562308494 : (((((p5 → p4) → p1) ∧ p3) → ((((p4 ∨ True) → (p1 → (p5 → p1))) ∨ (p2 ∧ p3)) ∧ ((True ∧ (True ∧ (p4 ∨ p5))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590332314331056120592211517277 : (((((((p1 ∨ p5) → p5) ∨ (True ∨ ((True → ((False ∨ p4) ∨ (p2 ∧ (True ∨ p2)))) ∨ (((p5 ∨ p1) ∧ p4) ∧ False)))) → p2) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213992546207401522924349148491 : (((p5 → (p4 → p1)) ∨ False) ∨ ((p2 → p2) ∧ (((p3 ∨ (p1 → False)) → ((p5 ∨ (p1 ∨ (((p5 → p4) ∧ False) → p4))) → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356342255638975530979991908726 : (p5 → ((((True → p2) → ((p1 ∨ ((p2 ∧ p1) ∧ (True → p3))) ∨ False)) ∧ True) ∨ ((((p4 ∨ (p2 → p2)) → p2) → (p4 ∨ p5)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171772289798378410970922616261 : ((((p3 ∨ (((p5 ∨ p5) ∧ ((False ∧ p5) ∨ (p5 → p5))) ∧ False)) → p1) → False) ∨ (p3 ∨ (p2 → (p5 ∨ ((p3 ∨ True) ∨ (p3 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184175794044309450328623580226 : (((p2 → ((p3 ∧ (((p4 ∧ p4) ∧ p4) ∧ p2)) ∨ p5)) ∨ True) ∨ ((p1 ∨ (False ∨ (((False ∧ p2) → p1) ∨ (p4 ∧ p5)))) ∧ (p3 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191257485265888237294400164016 : (((p4 ∧ True) ∧ (p3 ∧ ((False ∧ True) ∨ (p1 ∧ False)))) ∨ (((p5 → p1) ∨ (p4 ∧ (p3 ∨ (((p2 ∨ True) ∧ (p2 ∨ p3)) → p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51558442198347865663346870540 : (((True ∨ (((((p1 → p5) ∨ False) → p4) → (p2 ∨ ((True → p5) ∨ True))) ∨ (p2 ∨ p1))) → (p2 → (True ∧ ((p2 → False) ∨ p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226704114084408642015020430268 : (((p1 ∧ True) → False) ∨ (True → (((p2 → p4) → ((False ∨ p3) ∧ False)) ∨ ((p5 → (((p1 ∧ p2) → p3) ∧ ((False ∧ p2) ∧ p4))) ∨ True)))) := by
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
theorem thm_5_vars_193930286313798309865199154076 : ((p1 ∨ (False → ((p3 ∨ (p3 ∧ p5)) ∨ (p3 ∧ p3)))) → ((p1 ∧ (p4 ∧ p2)) ∨ ((((p5 ∧ (p3 ∧ p3)) ∧ p4) → True) ∨ (False → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322437602707095937283810958774 : (p5 ∨ (((p2 ∨ ((True ∨ (p2 ∨ True)) ∧ p3)) → (False ∨ (False → (False → ((True ∧ (((False ∧ True) → False) ∨ p5)) ∨ (p1 ∧ p3)))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46694002984140276315206889891 : (((p3 ∨ (((p5 ∧ ((p3 ∧ (True → p5)) ∨ p1)) ∧ (p3 ∧ (((False ∨ p2) ∨ p5) → p3))) → (p4 → (p3 → False)))) ∧ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337774636085217818237974914189 : (p1 → (((p3 ∨ p4) ∨ ((p4 → ((p2 → ((p2 ∧ (p1 → True)) ∧ False)) ∨ p3)) → p4)) ∨ ((p1 → False) → (p4 ∨ (p2 → (p5 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180983610479067026582977682845 : (((False ∧ False) ∨ (p4 → ((p5 → (False → p5)) → ((False → p4) → p3)))) → ((p5 ∧ (p2 ∨ ((p2 ∧ False) ∨ p3))) ∨ (True ∨ (p2 ∧ p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37763146059551513741049341384 : ((((((p4 → p4) → p3) ∧ (((True ∨ (p5 → (True ∨ (p5 ∨ ((p4 ∨ p1) → ((True ∨ p4) ∧ True)))))) ∧ False) → p3)) → p3) ∧ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607964239681988874038117651475 : (((((p2 → (p5 ∨ ((p1 ∧ (p2 → False)) ∨ ((((True ∧ p4) → p1) ∨ p3) ∨ (p3 ∨ ((p4 ∧ p3) ∨ (p5 ∨ p4))))))) ∧ p5) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_42306707600187312985361309987 : (((p2 ∧ (((p4 ∨ p2) ∨ (p4 → (((p1 ∧ p4) → (p1 → p3)) → (p5 ∨ False)))) ∨ (((p4 ∨ p3) ∨ False) ∨ (p1 ∧ p1)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191590650946303814296077933605 : ((p2 ∧ (p2 ∨ (((True → False) ∨ p5) ∧ (p5 ∨ False)))) ∨ (((False ∨ ((False → ((p5 ∨ p5) ∨ p4)) → p4)) ∨ (True → True)) ∨ (p5 ∧ False))) := by
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
theorem thm_5_vars_688428982867662868699073270519 : ((((p2 ∧ (p5 → (((True ∧ ((False ∧ p2) ∨ (True → p1))) ∨ (p2 ∨ p5)) ∨ p3))) ∧ ((p2 ∨ ((p1 ∨ p1) ∨ (True ∧ p3))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349764304425070059023199349859 : (p4 → (((False → ((p2 ∧ p4) ∨ p2)) → ((((False ∨ (p3 ∧ p3)) → ((((p2 ∨ p4) → p2) ∨ p5) ∧ p3)) → p1) ∨ (True ∨ p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709764774678461496511521121726 : ((((p1 → (((True ∨ True) ∨ p1) ∧ (p2 ∨ True))) → ((((True ∧ (p2 → False)) → p1) ∨ (((False ∨ (p3 ∧ p4)) ∨ p5) ∧ p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339665213501795347562629028329 : (p1 → (p3 ∨ ((((p2 ∨ p3) ∨ p2) ∨ (True ∧ ((p4 ∧ (False ∧ ((False → ((p5 ∨ (p2 ∨ (p4 ∨ False))) ∧ p2)) → p1))) ∧ False))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614351571465986817178966688564 : (((((True ∧ (((p5 → False) ∨ ((True ∨ ((p3 ∨ (False → p1)) ∧ True)) → (True ∧ True))) → (p5 ∧ p4))) → ((p5 → False) ∨ p5)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_167884888077406015603001045138 : (((p1 ∨ ((p3 ∧ p1) ∨ (p4 ∨ ((True → p1) → p1)))) → ((False ∨ (True ∨ False)) → p2)) → (p2 ∧ ((((True → p1) → p5) → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p3 ∧ p1) ∨ (p4 ∨ ((True → p1) → p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (False ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54055044622724990219484358697 : ((((((p5 → p4) ∧ p2) → p4) → ((p5 → p2) ∨ p2)) → (((((((p1 → p2) → (True ∨ False)) → p1) ∧ p3) → p3) → p5) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733252973280081711843473394076 : ((((p3 ∧ p3) ∧ (True ∧ (((True ∨ (((p3 → p3) ∧ (True → p1)) → p5)) ∧ (p1 ∧ (True ∨ False))) ∧ (False ∨ ((p4 ∨ p2) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53152403327996217959336678916 : (((((p2 ∧ (((True ∧ p4) ∨ p4) → p5)) ∧ (False ∧ p4)) ∨ p2) ∨ ((p2 ∨ True) ∧ ((((p2 → p5) → False) ∧ (p3 ∨ p5)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769055567507523469236132566994 : (((p5 ∧ (((p2 ∨ False) ∧ p2) → (((p3 ∧ p3) ∨ ((((((False ∧ p4) ∧ p5) ∨ p3) ∨ True) ∨ False) → ((True → p2) ∨ p5))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134849565233112337623788691042 : (((p5 ∨ (((p1 ∧ (p3 ∧ (p2 ∨ (((p4 ∨ ((False ∨ (p5 → p1)) ∨ p5)) ∨ p2) ∧ p1)))) → p3) ∨ p2)) → p3) ∨ ((p1 ∧ False) → p4)) := by
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
theorem thm_5_vars_2093642872341828342522257088 : ((True ∧ ((p4 ∧ (True ∧ (((((p2 ∧ p2) ∧ (False ∨ False)) ∨ p2) ∧ True) ∨ True))) ∧ p3)) ∨ ((p4 → (p4 ∨ False)) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180970638939291106652676584552 : (((p2 → p5) ∧ (p1 ∧ ((True ∧ (((p2 → p2) → p2) ∨ p3)) ∨ p3))) → ((((p1 ∧ (False ∧ (p4 → False))) → (False ∧ True)) → False) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616240443014533388677111906924 : ((((((((False → p4) ∧ (p2 ∧ (p2 → (p4 → False)))) → False) ∧ False) ∨ (((False ∨ ((p1 → p4) → p1)) ∧ (p3 ∨ True)) → p4)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98795510360398611591415977758 : ((True → (((True ∧ (p1 → ((((p1 ∧ ((p1 ∨ ((p3 ∨ True) ∧ (p3 ∧ p1))) → p5)) ∨ p2) → p1) ∨ (p4 ∨ False)))) ∧ False) ∧ False)) → False) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257810040034588491049503945642 : ((p3 ∨ p5) → ((((p4 ∨ (p5 ∧ False)) → (p5 ∧ ((False ∨ False) ∨ ((p5 ∧ p3) ∧ p2)))) ∨ (p5 → True)) ∨ (p2 → (p1 ∨ (p5 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168319612521692211771377183952 : (((p1 → False) ∧ (p1 ∧ (p4 → (((p2 ∧ ((p5 ∧ p4) ∨ p1)) → (p2 ∧ p5)) ∨ True)))) → ((True ∨ ((True ∧ (p2 → p1)) → False)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233987984178136166201268574219 : ((p5 ∨ (True ∨ p3)) → ((((False ∧ ((p2 ∧ p3) ∨ (False → (p5 ∨ p4)))) ∧ (True → p5)) ∨ ((p4 ∨ (False → p2)) → p3)) ∨ (True ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121751898058486843073924642222 : ((((((p4 ∧ p5) ∧ True) ∨ p2) ∨ ((p2 ∨ (p1 ∨ (((p4 → (p2 → (p2 → (p2 ∨ True)))) ∧ p1) ∧ p5))) → p3)) → p4) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38536803278005406249932981162 : (((((((p1 → (p2 → p1)) → True) ∧ (p4 ∨ p1)) ∨ p1) ∧ (p5 → (((p4 ∨ p3) → ((p5 → p5) → (p5 ∧ p1))) ∨ p2))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755923352338973578196317408696 : (((p1 ∧ (((p4 ∧ (((((((p3 ∨ (p4 ∧ p2)) ∨ (p4 ∧ p3)) ∨ p3) → p4) ∨ p3) ∧ (p4 ∧ p3)) ∧ True)) → (False ∨ False)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602110438163426864344895392198 : ((((p5 ∧ ((((p1 ∧ True) ∧ (p4 → ((True ∧ p3) → (p1 ∧ p5)))) ∨ p3) ∧ (((p5 ∨ False) → p1) ∧ ((False ∨ p3) → False)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230404530863430424287491679775 : (((p4 ∨ True) ∧ p1) → (((((False → False) ∨ (p2 ∨ ((p3 ∧ (p2 → p4)) ∨ (False ∧ False)))) ∧ p4) → p2) ∨ (p4 ∨ (p4 → (p4 ∨ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347830207486396419129483359291 : (p3 → (((p2 ∨ False) ∨ p3) → ((((p4 ∧ p4) → False) ∨ (((p3 ∨ False) → ((p2 ∨ True) ∧ ((p5 ∨ (p3 ∧ p2)) → p3))) → p4)) ∨ True))) := by
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
theorem thm_5_vars_50310392321016390043368124429 : ((((((p3 ∧ p1) ∨ (((p3 ∧ p1) ∨ p3) ∨ True)) ∧ (p3 ∨ p3)) ∨ (True ∨ ((p1 ∧ p2) → True))) ∨ ((p2 ∨ p5) ∧ (p4 ∨ p2))) ∨ p2) := by
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
theorem thm_5_vars_148193644159463130836372187512 : ((((False → (p5 ∧ p4)) ∧ (((p2 ∨ ((p1 → False) ∨ False)) → True) → (p1 → p4))) ∧ ((p2 ∨ False) ∨ p3)) ∨ (((p4 ∧ True) ∧ p5) → p4)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149543573100185423419419219179 : ((p2 ∧ (((p5 ∧ p2) → ((((((p3 ∨ False) ∧ (p5 → True)) → p2) → p4) ∨ (p5 ∧ p5)) ∨ p5)) → p2)) ∨ (((p4 ∨ False) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159704947194657816719215230881 : ((((((p4 ∧ (p5 ∧ p5)) ∧ p3) ∨ ((True ∧ (p2 ∧ p1)) → p3)) ∨ (True → (False → True))) ∨ p4) → ((p1 ∧ ((p3 ∨ True) → p1)) ∨ True)) := by
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
        let h7 := h5.left
        let h8 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174055769762540409702430619791 : (((p3 → (((((False ∨ p2) → p3) → False) ∧ ((p2 ∨ p2) ∧ p3)) ∧ False)) → True) → ((((p2 → p1) → (p2 ∨ (p1 → p4))) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44218834673766173062128598055 : ((((((p3 ∨ ((p4 ∨ p3) ∨ (True → (p2 ∨ p1)))) ∨ (((p2 ∧ True) ∨ p4) ∨ p4)) ∧ p2) ∨ (((p4 ∧ False) ∧ p2) ∧ p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112096750634961708953791077821 : ((((True ∧ p5) → (((((p1 ∨ (True ∨ (p1 → p5))) → False) → p3) → p2) ∧ ((p5 ∨ (p5 ∧ (p5 ∨ p4))) ∧ p1))) ∨ True) ∨ (p1 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193842102225783539692777390484 : ((True ∨ ((p5 ∧ ((p3 ∨ p1) → (p4 ∨ p5))) ∨ p2)) → ((p4 → ((p1 → True) → (p4 ∨ p5))) ∧ ((p3 ∧ p5) ∨ ((p2 ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
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
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
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
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150027826410465731347095801836 : ((p5 ∨ (((p1 ∧ p3) → p3) → (((((p3 → p1) → p2) → ((p1 → p1) ∧ p3)) ∧ (p4 ∧ p2)) ∨ p3))) ∨ (p4 → (p3 ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_304982566609829515321943546720 : (p1 ∨ (((((False ∧ p1) ∨ (p1 → ((p2 ∧ (((p3 ∧ p3) ∨ (p4 → (True ∨ True))) ∧ False)) ∧ p1))) → p4) ∨ True) ∨ ((False ∧ True) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678637263712624755870255086771 : (((((False → p3) ∧ ((True ∧ (((False ∨ p1) ∧ p2) → (((False ∨ p3) → p3) → (p1 ∧ True)))) → p3)) ∨ (False ∨ (p3 ∨ (False → p1)))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756012760194958863107956991756 : (((p1 ∧ (((False ∨ p2) ∨ (((p2 ∨ ((True → ((True ∧ p3) ∨ (p3 ∧ False))) ∨ (p1 ∨ (p4 ∨ p4)))) ∧ p4) ∨ (True ∨ False))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299182056275769185950845168160 : (False ∨ ((((((p5 ∧ p3) ∧ p3) ∨ p4) ∧ (p1 ∧ (p4 → (p4 ∧ ((((p4 ∨ ((p1 ∨ p3) ∨ p5)) → p3) → p4) ∨ True))))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210279097051594918106198923590 : ((((p2 → p5) → p4) ∨ True) ∧ ((((((True ∧ (p3 ∨ False)) ∨ p3) ∧ (p3 ∧ p2)) ∨ ((p1 → p5) ∨ True)) ∧ ((False → p2) ∨ p3)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326870171394733098575200016032 : (True → (((((((True → ((p2 ∨ p2) → True)) ∧ p2) ∨ (p2 → ((True ∧ p3) ∧ p4))) ∧ ((p3 → p2) ∧ p5)) ∧ (False ∧ p3)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611158103257134496573612399885 : (((((((p3 ∨ p2) ∨ p3) ∨ ((p2 ∨ (p3 ∧ False)) → ((p1 ∨ (False ∨ p3)) ∧ ((p4 ∨ (p3 ∨ False)) ∧ (False → p4))))) → p3) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179927367866954912596015070860 : ((((((p3 ∨ ((p4 ∨ p1) ∨ p1)) ∧ p4) → (p5 ∨ False)) → True) ∨ p1) → ((p2 → p1) → (p4 ∨ ((True → (p1 ∨ False)) ∨ (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69359438843927639960369982501 : ((p5 → (p4 ∨ (((((False ∧ True) ∧ ((p2 → False) → True)) ∧ p1) ∨ p2) ∨ (((((p4 → p3) ∨ p2) → (False ∨ p1)) ∨ p4) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210206446411490714835910138955 : ((((p4 → False) ∨ p1) ∨ True) ∧ (((((p3 → p2) → (False ∧ (((p5 ∧ True) ∧ p1) → p4))) ∨ p5) ∨ (False ∨ (False → (True → p1)))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255507297397448722915006364069 : ((p5 ∧ p2) → (((((((p5 → False) ∨ p1) → p3) → p1) ∧ p3) → (False ∨ False)) → ((((p5 ∧ p4) → (False ∨ p1)) ∧ True) ∨ (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225971446107789133125320710139 : (((p3 ∧ p1) ∨ p5) ∨ (p1 ∨ ((((p4 ∨ (p2 → (p5 ∧ p1))) → (False ∧ p3)) ∨ (False → (((p4 → p1) ∨ False) → p4))) ∨ (True → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165327887285646242885281087670 : (((((((p5 → p5) ∨ p4) → (p3 → (p2 ∧ p2))) → p4) ∨ p2) ∧ (p4 ∧ (p2 ∨ p3))) ∨ ((p4 ∨ True) → ((False ∧ p2) → (p1 → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20766628356625477864484219679 : (((((False ∧ ((p4 ∨ ((p3 ∨ p1) → p3)) → p1)) ∨ False) ∧ True) ∨ (True ∨ ((True ∧ (p1 → p3)) ∧ ((p2 → p4) ∨ (p4 ∧ True))))) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61720869326176085096659893319 : ((p1 ∧ (True → (p3 ∨ (((p3 ∧ p2) ∨ False) ∨ (p3 ∨ ((p1 ∨ (p2 → p3)) ∨ (p5 ∨ (p2 ∨ ((p3 → (p5 → p4)) → p1))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10621416639669918418340088910 : (((p5 → (((p1 ∨ p4) ∧ True) → ((((((p2 → p2) → p2) ∨ (p2 → True)) → p2) → p1) ∧ (p2 ∧ (p1 ∧ (p2 ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125198499530567231647398462432 : (((p4 ∧ (p4 → p3)) ∨ ((False ∧ p4) → (True ∨ (p2 ∧ (True ∨ (p1 ∨ ((((p4 ∧ p1) ∨ p3) → True) ∧ (p4 → False)))))))) → (p3 ∨ True)) := by
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
theorem thm_5_vars_166260398923310563348521068696 : ((p3 ∧ ((((p4 ∧ p2) → p3) ∧ p5) ∧ (p1 ∧ ((p4 ∧ ((p1 ∨ p4) ∨ p4)) → p1)))) ∨ (((False → False) ∧ ((p3 ∧ p4) → p3)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704240521445352064889786521374 : ((((((False ∧ p4) ∨ ((False ∧ p3) → p5)) → (False ∨ p4)) → (False ∨ (((((p5 ∧ False) ∨ (False ∧ p3)) → (p2 ∧ False)) → p4) ∧ True))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ p4) ∨ ((False ∧ p3) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608063339167513616037247454067 : ((((((((((p3 ∨ p3) → (p2 ∧ (True ∨ p4))) ∧ ((((False ∨ p1) ∨ False) ∨ (False ∧ p4)) ∧ p3)) ∨ True) ∨ p2) ∧ True) ∨ p5) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190671784237138832289204119890 : (((p1 → (p2 ∧ ((p1 ∧ p1) ∨ (p1 ∨ p5)))) → False) ∨ (p1 → (((p4 → ((p5 → (p2 → p3)) ∨ p1)) ∨ p2) ∨ ((False → p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



