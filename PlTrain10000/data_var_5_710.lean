variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42157575335922711394304338233 : ((((p2 → p1) → (False ∧ ((True ∧ p1) → ((((False ∨ ((p1 ∧ p1) → p3)) → (False ∧ (p2 → (p5 → p4)))) ∨ True) ∨ True)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788279976721107409612503730153 : (((p5 ∨ ((p4 → (p4 → (((p5 → (p4 → p1)) ∨ (p2 ∨ ((p1 ∨ (False ∧ (p4 ∨ (True ∨ p2)))) ∨ (False → True)))) ∧ p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157362092247993131730258861631 : (((p2 → ((((p3 → (p1 → (p2 → (p5 ∧ p3)))) ∧ p1) ∧ (True ∧ (p1 ∧ True))) ∧ p3)) → p3) ∨ ((p4 → (p3 ∨ True)) → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256729278455107695246557232407 : ((p1 ∨ p1) → (((p2 → p5) ∧ p3) ∨ (True ∧ ((p1 → ((((p1 ∧ p5) ∧ (True ∨ p5)) ∨ False) ∧ ((p4 ∧ p5) ∨ (p2 ∨ False)))) ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775637336096332048821764833859 : (((False ∨ (p1 ∨ ((((p3 ∨ (((((((p4 → (p5 ∨ False)) → p3) ∧ p4) ∧ False) → p1) ∧ False) → p3)) ∨ (p1 ∧ False)) → p1) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327851041288352297244375016533 : (True → (((((True ∧ p4) ∧ (p2 ∨ p3)) ∧ p1) ∧ ((p3 ∧ ((p2 ∨ p4) ∧ ((p2 ∨ (True ∧ (p5 → p3))) → p2))) ∨ True)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65611107491615652995184768094 : ((p4 ∨ ((p1 ∧ (False ∨ ((((p2 ∨ p4) → (((True ∧ p5) ∧ ((p5 → True) ∨ p2)) ∨ (p3 ∧ p3))) ∧ False) ∧ (p5 → False)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134325541746911078258830653655 : (((p2 ∧ ((p5 ∧ ((((p1 → p1) ∨ ((False → p5) → False)) ∧ p4) ∧ (True → (False → p2)))) ∧ (False ∨ p3))) ∨ False) ∨ (True ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314824189317215500713348488701 : (p3 ∨ (((p1 ∧ (((True ∧ True) ∧ (p5 ∧ (False → p5))) ∨ p4)) ∧ p5) ∨ (((p3 ∧ (True ∧ (((p4 ∧ p5) ∧ True) ∨ p1))) → p3) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118460797483404859376393964294 : ((p3 ∨ (((True → p3) ∨ (False ∨ ((((((p4 ∧ (True ∨ p2)) ∧ p2) ∧ p4) → (False ∧ p1)) ∧ (p1 → p1)) ∨ p2))) ∨ p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711405512121833671869534556322 : ((((p3 ∨ ((p2 → (p3 ∨ False)) ∧ p4)) ∧ ((p3 ∨ p5) ∧ (p2 ∨ (p2 ∨ ((p2 ∨ ((p3 → ((p2 → True) → p1)) → p3)) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135308870008004820596370938363 : (((((p1 ∨ (p1 → ((False ∧ p3) → (p3 ∨ p4)))) ∨ ((True ∨ p2) → (p2 ∧ True))) → p1) ∧ (p2 ∧ (True → True))) ∨ (True ∨ (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743650831205219699407420010831 : ((((True ∧ p1) → (p4 ∨ ((((p4 → p4) → (((True → False) ∨ p2) ∨ True)) ∨ p5) ∨ ((p2 ∧ ((p2 → p5) → (p1 → p1))) ∨ p1)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205380810469720632245405508992 : ((((True → True) ∨ p5) → (p3 ∨ p5)) ∨ (p1 ∨ (p2 ∨ (p5 ∨ (False → ((p4 → False) ∨ (((p3 ∧ True) ∨ False) ∨ (False → (p3 ∨ p4))))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39328169940665232953530816647 : (((p2 ∧ ((((True → ((True ∧ p3) → (p5 ∨ p4))) ∨ p4) ∧ ((p1 → (True ∨ p2)) → (p3 → p2))) ∨ ((p1 ∧ p2) → p3))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604081641571483999779681049966 : ((((p5 ∨ ((p2 ∧ (False ∨ p1)) ∨ (((True ∧ ((False ∨ ((True → p1) → (p3 → (False → True)))) ∧ p3)) ∧ False) ∧ (p1 → True)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199342628338797319315388349425 : ((((True ∧ (p3 ∧ (False ∨ p2))) → p1) ∨ p2) → (((((p1 ∨ p3) ∧ (p4 ∧ p5)) → p1) ∨ ((p2 ∨ p4) ∨ ((p3 ∧ p5) ∨ True))) ∨ True)) := by
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
theorem thm_5_vars_748757012360464602946206192136 : ((((p3 → p5) → ((p5 → (False → True)) ∧ ((p5 → (p3 → ((((((True ∨ False) ∨ p5) ∨ p4) ∧ False) ∧ True) → True))) → (True ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793448323088576983759535605953 : (((True → (False ∨ (((p4 ∨ ((p4 → (((p1 ∧ p5) ∨ ((True ∨ p4) ∧ ((False → (p5 ∨ p3)) ∧ p4))) ∧ False)) ∧ p4)) ∧ p2) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69176007932912749330540670004 : ((p5 → ((p3 → ((p1 ∧ (p2 ∧ ((False → (((p2 ∨ False) ∨ p4) ∧ p4)) → True))) ∨ p1)) → ((True ∧ ((False → p3) → p4)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57532248035788147974446914750 : (((p5 → (p3 ∨ p1)) ∨ ((p3 ∧ p1) ∧ ((p1 ∨ p3) → (((p2 ∧ (((p3 ∨ p3) ∧ (False ∨ p1)) ∨ (False → p5))) ∨ p1) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216842511289719090647534876960 : (((p5 ∧ (p2 ∨ p3)) ∧ p2) → (((True → ((p2 ∧ p2) ∧ ((p4 ∨ (p1 ∧ (p4 ∧ True))) ∧ (p4 ∧ p2)))) ∨ p4) ∨ (False → (p4 ∧ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148100967398997996240680032812 : ((((True → ((((p1 ∨ ((p1 ∨ (p5 ∧ p3)) → p5)) ∨ p3) ∧ p2) ∧ p4)) ∨ (p5 ∧ True)) → (False ∨ p3)) ∨ (p3 ∨ ((True ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47270984489389599611795371358 : ((((p1 ∧ (p3 ∨ (False ∧ True))) ∧ (False ∧ ((p4 ∧ (p5 → (False → p2))) ∧ (((True ∨ p3) ∨ True) → (True ∧ True))))) ∨ (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48070763135538713418471634851 : ((((((False → p2) ∨ (p5 ∨ p5)) ∨ p3) ∧ (True ∧ (p4 → (((p5 ∧ p1) ∧ (p5 ∨ p2)) ∧ ((False ∨ False) ∨ p1))))) → (p5 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41182287265419706026217247665 : ((((((((True ∧ p1) → (False ∧ (p1 → p2))) ∨ (p1 ∨ p5)) ∨ (p1 → (p1 → True))) → (True ∨ p5)) → ((p5 → p3) → p1)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113815881297303292681537996098 : (((p2 ∧ ((p1 → (p1 ∧ p5)) → (p4 ∧ (p2 ∨ ((p3 ∨ p5) ∧ ((p3 ∧ (True → False)) → (p1 ∨ p4))))))) → (p2 → p4)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860033282788318282935534599041 : ((((((p1 ∧ (p3 ∧ (((True ∨ (p5 → (p4 ∨ p4))) ∧ (p5 ∧ p5)) → p1))) ∨ ((p5 ∧ (p2 ∧ p2)) → p2)) ∨ (p3 ∨ p2)) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ (p3 ∧ (((True ∨ (p5 → (p4 ∨ p4))) ∧ (p5 ∧ p5)) → p1))) ∨ ((p5 ∧ (p2 ∧ p2)) → p2)) ∨ (p3 ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112048276470074428504313777232 : ((((True ∨ (p2 → False)) → (((p3 ∧ ((p3 ∨ ((p5 ∧ (False ∨ (p1 ∧ True))) ∨ p3)) → p3)) → (False ∧ p2)) ∨ p1)) ∨ True) ∨ (False ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191076147834568113350218004157 : (((p5 → ((p4 ∧ p3) → False)) → ((p1 ∧ p2) ∧ p1)) ∨ ((((True ∧ (False → (p3 ∧ p5))) ∨ False) ∧ (((p4 → False) ∧ False) ∧ p2)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165980676540101288934877863107 : (((True ∧ False) ∨ ((p4 ∧ (p4 ∧ ((p4 ∧ False) ∨ p1))) ∨ (p1 ∨ (p5 ∧ (p3 ∨ p3))))) ∨ (True ∨ (p1 ∧ (((p1 → p4) → p2) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60086348365180909750893706900 : (((p2 ∨ p5) → (p5 → ((p3 ∨ p3) → ((p5 ∧ (((True ∧ (True ∧ (p1 ∧ p3))) → p3) ∧ ((p2 ∨ False) ∧ p4))) ∨ (True ∨ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720092440081186502371722562672 : ((((((True → p4) → p5) ∧ p3) → (((p3 ∨ ((((p2 ∨ p3) ∨ (p1 ∨ p5)) ∧ p1) ∧ (p4 → p4))) → ((False ∨ p1) → p2)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676581724391506374588026605551 : ((((p1 ∧ (p1 → ((((p4 ∨ ((p3 ∧ p1) → (p2 → (p4 ∨ p2)))) ∨ p1) ∧ (p1 → p1)) ∨ p1))) ∧ ((p5 ∧ True) → (p2 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14920705123624049868827371110 : ((((True → (p3 ∧ (False → p1))) ∨ ((((((True ∨ p4) → (p2 ∨ (p5 ∧ p4))) ∨ p4) ∧ (p3 ∨ p4)) ∨ True) ∨ p1)) ∨ (p5 ∧ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_191864198848002294480744993904 : ((p4 ∨ (((False ∨ (p2 → (p2 ∧ p4))) → p1) → p4)) ∨ (p5 → (p5 ∧ (p4 → ((((p4 ∨ (p2 ∧ True)) ∧ True) ∨ p1) ∧ (p2 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167824206961436544137403508428 : (((p3 ∨ (p4 ∧ (((True ∨ (p5 ∨ p1)) ∧ p3) ∧ p3))) ∧ (((False → p2) → p4) ∧ p2)) → ((((False ∨ (p1 ∨ True)) ∧ p4) ∧ p3) ∧ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h3.left
        let h20 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h3.left
        let h23 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
  -- Conjunctions on the left can always be decomposed.
  let h24 := h1.left
  let h25 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h29 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- False on the left can always be used.
      apply False.elim h30
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h31 := h27 h29
    -- One of the premise coincides with the conclusion.
    exact h31
  case inr h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h25.left
      let h41 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h25.left
        let h45 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h25.left
        let h48 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h33
  -- Conjunctions on the left can always be decomposed.
  let h49 := h1.left
  let h50 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h49
  case inl h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h50.left
    let h53 := h50.right
    -- One of the premise coincides with the conclusion.
    exact h51
  case inr h54 =>
    -- Conjunctions on the left can always be decomposed.
    let h55 := h54.left
    let h56 := h54.right
    -- Conjunctions on the left can always be decomposed.
    let h57 := h56.left
    let h58 := h56.right
    -- Conjunctions on the left can always be decomposed.
    let h59 := h57.left
    let h60 := h57.right
    -- Disjunctions on the left can always be decomposed.
    cases h59
    case inl h61 =>
      -- Conjunctions on the left can always be decomposed.
      let h62 := h50.left
      let h63 := h50.right
      -- One of the premise coincides with the conclusion.
      exact h58
    case inr h64 =>
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h65 =>
        -- Conjunctions on the left can always be decomposed.
        let h66 := h50.left
        let h67 := h50.right
        -- One of the premise coincides with the conclusion.
        exact h58
      case inr h68 =>
        -- Conjunctions on the left can always be decomposed.
        let h69 := h50.left
        let h70 := h50.right
        -- One of the premise coincides with the conclusion.
        exact h58
  -- Conjunctions on the left can always be decomposed.
  let h71 := h1.left
  let h72 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h71
  case inl h73 =>
    -- Conjunctions on the left can always be decomposed.
    let h74 := h72.left
    let h75 := h72.right
    -- We want to use the implication h74 based on <expert-advice>. So we show its premise.
    have h76 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h77
      -- False on the left can always be used.
      apply False.elim h77
    -- We have shown the premise of h74, we can now drive its conclusion.
    let h78 := h74 h76
    -- One of the premise coincides with the conclusion.
    exact h78
  case inr h79 =>
    -- Conjunctions on the left can always be decomposed.
    let h80 := h79.left
    let h81 := h79.right
    -- Conjunctions on the left can always be decomposed.
    let h82 := h81.left
    let h83 := h81.right
    -- Conjunctions on the left can always be decomposed.
    let h84 := h82.left
    let h85 := h82.right
    -- Disjunctions on the left can always be decomposed.
    cases h84
    case inl h86 =>
      -- Conjunctions on the left can always be decomposed.
      let h87 := h72.left
      let h88 := h72.right
      -- One of the premise coincides with the conclusion.
      exact h80
    case inr h89 =>
      -- Disjunctions on the left can always be decomposed.
      cases h89
      case inl h90 =>
        -- Conjunctions on the left can always be decomposed.
        let h91 := h72.left
        let h92 := h72.right
        -- One of the premise coincides with the conclusion.
        exact h80
      case inr h93 =>
        -- Conjunctions on the left can always be decomposed.
        let h94 := h72.left
        let h95 := h72.right
        -- One of the premise coincides with the conclusion.
        exact h80



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149934647970663532917260178057 : ((p3 ∨ ((False ∨ (p1 ∨ p5)) → ((True ∧ (p5 ∧ ((((p4 → (p2 ∨ p3)) → p5) ∧ p3) ∧ p3))) → False))) ∨ (((True ∨ True) → False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324961177357289548617010768001 : (p5 ∨ ((p5 ∨ p5) ∨ ((((p1 → p5) ∨ p2) ∧ p4) ∨ (p1 → (((((p5 → p3) ∧ True) → True) ∨ (True ∨ True)) → ((p5 → p1) ∨ p2)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702674310310709144702452371472 : (((((p2 ∧ (True ∧ ((True ∧ p1) ∨ p2))) ∧ (p4 ∨ p1)) ∨ (((((((True → p4) ∧ p4) ∨ p1) → p5) ∧ (p4 → p4)) → p3) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247632774897401867559847483852 : ((False ∨ p5) ∨ (False ∨ ((p2 → (((p1 ∨ True) → (((((p4 → p3) → p1) ∧ p4) ∧ (False → (False → p5))) → p3)) ∨ (False ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336477007079402032129345358371 : (p1 → ((p3 → ((p2 ∨ (p3 → (p2 ∧ p4))) ∨ (p4 → ((((False → p2) → True) ∨ (p2 ∧ ((p5 → True) ∧ (p2 → p4)))) → p5)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67560755430901803181297828999 : ((p1 → ((p1 ∨ p3) ∧ (p5 ∧ (((p4 ∧ (p2 ∧ p1)) ∨ (((p2 ∧ p4) ∧ p5) ∧ p2)) ∧ ((p2 ∧ ((p5 → p3) → True)) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186692341900886338217493679855 : ((((((p5 ∨ p1) ∨ p5) → False) ∧ p5) ∨ ((p4 ∨ True) → False)) → ((False ∧ (p3 ∨ (((p4 ∧ True) → p4) ∧ p3))) ∨ ((True ∨ p4) ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348195945194334293961020742853 : (p3 → ((True → False) → (((((False → ((p4 ∨ ((p2 ∨ (p5 → (p5 ∧ p2))) ∨ p3)) ∧ p4)) → p3) → p2) ∧ p4) ∨ (p5 ∨ (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152278449569486374803060578368 : ((((p3 ∧ ((False ∨ p1) ∨ p5)) → p1) → (True → (((p4 ∧ p5) ∨ ((p1 → p1) ∧ (p4 → p1))) → True))) → ((p3 → (p2 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351932065742554345934697237090 : (p4 → ((((((True ∧ (p2 ∧ p2)) → p2) ∨ False) → p2) → p4) → ((p2 → (((((p3 ∧ False) → (p3 ∨ p5)) ∧ p3) ∧ p3) ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231065082760380618547029484553 : (((True ∨ p4) ∨ p4) → ((False → True) → ((p3 → False) ∨ ((p4 → (((p1 ∧ ((p5 ∧ p5) → (p1 ∨ (p5 ∨ True)))) → p4) ∧ p3)) → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787680343240946125839290028782 : (((p4 ∨ (p4 ∨ ((p1 ∧ p2) ∨ ((p5 ∨ ((((p2 → p4) ∨ (((p2 ∨ p1) ∧ (p2 ∨ p3)) ∨ p4)) → (p2 ∨ p4)) → p1)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67373408750943988814791755323 : ((p1 → (((p4 ∨ ((True ∧ (((p2 ∨ True) → (p1 ∧ p5)) ∧ (p5 ∨ ((p3 ∨ False) → (True → p3))))) ∧ p1)) ∨ (p3 ∧ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2991875809364671176236598638 : (((p4 ∧ p3) ∧ p5) → ((p4 ∧ ((p4 ∧ (((p5 ∨ p1) → False) ∨ True)) → (False ∨ (p5 → (p1 ∨ p1))))) ∨ ((p5 → p4) → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165191008949889754406851457498 : (((((True → ((p3 ∧ p2) ∧ ((p4 ∨ (p4 ∧ p5)) ∧ True))) → False) ∧ p4) ∨ (p1 → True)) ∨ (True ∧ (p3 ∧ ((p3 ∧ True) ∨ (p5 → p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193615502262171125699322752298 : ((True ∧ ((p1 → ((p3 → False) ∨ (p1 ∧ p2))) ∨ False)) → ((((False → (p4 → (False ∨ True))) ∨ (p3 ∨ p3)) → p1) ∨ (True ∨ (p5 ∧ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344491505202934253711365311052 : (p2 → (True → ((((False ∨ True) ∨ (p2 ∨ (p1 → p5))) → ((p4 ∧ p5) → True)) → (((((False → p5) ∨ p2) → p4) ∨ p2) ∨ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136909279673168296706987326176 : (((True → p2) ∨ ((p1 → ((((p5 ∧ (p2 → p4)) ∧ p3) ∨ (((p5 → p4) → p1) ∧ (p2 → p5))) ∨ True)) ∨ p1)) ∨ ((True ∨ p1) ∧ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190471807499371494946744690505 : ((((((p3 ∨ p4) ∨ True) → (p1 ∧ p4)) ∧ p1) → p2) ∨ (((((p1 → True) ∨ (p2 ∨ p1)) ∨ p5) → False) → ((p5 ∨ (False → False)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 → True) ∨ (p2 ∨ p1)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135417939850201022157619320533 : ((((p2 ∨ p4) → (((p2 → (p3 ∨ p4)) ∨ (p2 ∧ p5)) ∧ ((p1 ∧ (False → p3)) ∨ p5))) ∨ (False ∧ (False ∨ p5))) ∨ (True ∨ (p3 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154295944734791014460685135517 : (((False ∧ (((((p4 ∨ (True ∧ p2)) → p2) → True) ∧ (p4 ∧ ((p5 ∨ False) ∧ p4))) ∨ True)) ∨ True) ∧ ((p2 ∨ p4) ∨ (p4 ∨ (False → p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164864541047209720387423998991 : (((p3 ∨ ((((p5 → (False ∧ (p5 → p4))) ∧ p5) ∨ p1) → ((p1 ∧ p3) ∨ p5))) ∨ False) ∨ ((True ∨ p2) ∨ ((p1 ∨ (p4 ∨ p4)) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137697594345836171596932078068 : ((p1 ∨ (((p1 ∨ (False → False)) → ((p1 ∧ ((p4 → (p2 ∧ ((p2 ∧ True) → p5))) ∨ p4)) → p4)) ∨ (p2 ∨ p1))) ∨ (p2 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776531970159673613013949157806 : (((p1 ∨ ((((p1 ∨ (p2 ∧ p5)) ∨ (True ∧ p5)) ∨ (((((p3 ∨ False) ∧ p1) ∧ (p2 → p3)) ∨ (False ∧ p2)) ∨ (p4 → p2))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150615419575560552804114324182 : (((p1 ∧ ((p5 ∧ (((False ∨ p2) → p1) ∧ (p1 → ((p3 → (p5 ∧ False)) ∨ (p5 ∧ p4))))) ∧ p3)) ∧ True) → ((p4 ∨ p5) ∧ (p1 ∧ p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- One of the premise coincides with the conclusion.
  exact h14
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h29.left
  let h31 := h29.right
  -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
  have h32 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h24
  -- We have shown the premise of h31, we can now drive its conclusion.
  let h33 := h31 h32
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h34 =>
    -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
    have h35 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h34, we can now drive its conclusion.
    let h36 := h34 h35
    -- We need to get the right conjuct of h36 based on <expert-advice>.
    let h37 := h36.right
    -- False on the left can always be used.
    apply False.elim h37
  case inr h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- One of the premise coincides with the conclusion.
    exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699413239796559127712101958813 : (((((p5 → (p3 → ((False → p4) ∧ (True → (True → p5))))) ∧ p4) → ((((p4 ∨ ((p4 ∧ p3) ∨ p5)) ∨ p2) ∧ p3) ∨ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615489152721775969876287752774 : (((((((p2 ∧ (False ∧ p3)) ∧ (p1 ∧ ((p5 → ((p1 ∧ p5) ∨ p5)) ∨ p5))) → p1) → (((p2 ∨ True) → (p3 ∧ p5)) → p5)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227089368465212767041237497400 : (((p3 ∨ p4) → p4) ∨ ((p3 ∧ ((p2 ∨ (True ∨ p4)) ∧ (p4 ∧ (p2 → p5)))) ∨ ((p1 → False) ∨ (p2 ∨ ((True → p3) → (True ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40425683112123749415291182420 : ((((((p1 ∧ (((p2 ∧ p4) ∧ False) → (True → (p1 → p2)))) → False) ∧ ((((p3 ∧ False) → p2) ∧ False) ∧ (p4 → p4))) ∨ p5) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123952291406767093262669521651 : (((p3 ∨ (p3 ∨ (p5 → (((p5 → p1) ∧ (False → p1)) ∨ p4)))) ∧ (p1 ∧ ((False ∨ False) ∨ ((True → False) ∧ (p2 → True))))) → (p3 ∧ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h3.left
      let h25 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h33 := h30 h32
        -- False on the left can always be used.
        apply False.elim h33
  -- Conjunctions on the left can always be decomposed.
  let h34 := h1.left
  let h35 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- False on the left can always be used.
        apply False.elim h41
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h42.left
      let h44 := h42.right
      -- One of the premise coincides with the conclusion.
      exact h37
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h35.left
      let h48 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- False on the left can always be used.
          apply False.elim h51
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- One of the premise coincides with the conclusion.
        exact h47
    case inr h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h35.left
      let h57 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h58
        case inl h59 =>
          -- False on the left can always be used.
          apply False.elim h59
        case inr h60 =>
          -- False on the left can always be used.
          apply False.elim h60
      case inr h61 =>
        -- Conjunctions on the left can always be decomposed.
        let h62 := h61.left
        let h63 := h61.right
        -- One of the premise coincides with the conclusion.
        exact h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621181912025702322747858060529 : ((((True ∧ ((p4 ∨ ((((((p4 ∧ p3) → (p1 ∨ ((p5 ∧ p4) → p4))) ∧ (True ∨ (True ∧ False))) → p1) ∧ p5) ∧ True)) ∧ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_352209795204972205435281583780 : (p4 → ((p4 → ((False → p3) → True)) ∧ ((((p1 ∨ p5) ∧ False) ∧ (((p2 ∨ p4) ∨ p4) ∧ ((p3 ∨ p3) → (p3 ∧ (False ∨ p1))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115298409416871037392781162837 : ((((p1 → (p5 ∧ ((p3 ∧ True) → (p1 ∨ p5)))) ∨ p4) → (p1 ∧ (((((p3 → p3) → p2) → p3) → (False ∨ p4)) ∧ False))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219446629589137439650903924112 : ((p4 ∨ ((p1 → p2) → p3)) → (True ∧ (p3 ∨ (((p5 → ((p5 ∨ True) → False)) ∨ (p1 ∧ p3)) → ((p4 → False) ∨ ((p4 ∨ False) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179385434790793911594524958048 : ((p3 ∨ ((p4 ∨ (p3 ∧ ((((p3 ∨ p5) ∨ p2) ∨ p2) ∧ p3))) ∨ p2)) ∨ ((((False ∧ p5) ∧ p4) → (p5 ∧ (True ∨ p4))) ∨ (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328818853995199895697901875815 : (True → (((p5 ∨ (((p5 → p5) → (p5 ∧ p2)) ∨ True)) → p4) → (((((p1 → (False ∨ p5)) ∧ True) ∨ (p5 ∧ p2)) → p1) → (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 → (False ∨ p5)) ∧ True) ∨ (p5 ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52857610344697382896760800635 : (((True ∧ ((p5 ∧ (p2 → (((p5 ∨ p5) ∧ True) ∧ True))) → (p2 ∨ p5))) → (p2 → ((p1 → ((p1 → p1) ∧ False)) ∧ (p1 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260582371417441012104906480719 : ((p3 → p2) → (((p2 → p3) ∨ (p5 ∨ (True ∨ (p2 ∧ (p5 → (False ∨ (p5 → ((p2 ∧ (((p2 → p5) ∧ True) → True)) → p1)))))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_233455858527128527328349606050 : ((False ∨ (p2 → p5)) → (p5 ∨ (((p5 ∨ True) → (p1 → (p4 ∧ ((p1 ∨ (False → (p4 → (False → (True ∨ p5))))) ∧ (p5 ∧ p3))))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228511862207476324181051568176 : ((False ∨ (p5 → p4)) ∨ (((p3 ∨ ((p1 ∨ (True ∨ True)) ∧ ((((p5 ∨ True) ∧ (p1 ∨ (p4 ∧ p2))) ∧ False) ∨ p5))) ∧ p4) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192642676787919742009012669410 : (((((False ∧ True) → ((p3 → True) ∧ p1)) ∨ p4) → False) → (((p2 ∧ (p1 ∨ ((p3 ∧ p5) → p1))) ∧ p2) ∨ (p4 ∧ ((p3 → p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ True) → ((p3 → True) ∧ p1)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244630760321851753513742501029 : ((False ∧ p5) ∨ ((p5 ∨ ((p5 ∧ (p3 ∧ True)) ∨ ((p1 ∨ (True ∨ ((((p2 → True) ∧ False) → p1) ∨ True))) ∧ p3))) → (p4 → (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615928494347527293933567719614 : (((((p3 → (False ∨ (((True ∧ (((p4 ∨ p3) → p5) ∧ p1)) ∧ p2) ∧ p3))) ∨ ((p1 ∨ False) ∧ ((True ∨ (False → p2)) ∧ p3))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_42533156273108558120294926093 : (((p1 ∨ ((((p1 ∨ ((((p5 → p1) ∧ (p5 → p4)) ∨ p3) ∧ (((p3 → p3) → (p5 → p3)) ∨ True))) ∧ p1) → p3) → p4)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163651904462486599412333486735 : (((False ∨ p1) ∨ (((False → False) ∨ p4) ∨ (((p3 → (True ∨ True)) ∨ (p4 ∨ p5)) → p4))) ∧ ((((p1 ∧ (p2 ∨ p3)) ∨ p1) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721954885369037622634954222545 : ((((True → ((p3 ∧ p2) → p2)) → ((((False ∨ p2) → (p1 → p5)) → (p4 ∨ (((p3 ∧ (p3 ∨ p3)) ∨ True) → (p4 → True)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608690392313867095962581431951 : (((((((p3 → ((((p5 ∧ (p4 → ((p2 ∧ (p4 ∧ False)) ∨ p4))) ∨ p1) ∨ (p1 → p5)) ∨ p5)) ∧ p2) → (p2 → p5)) ∨ True) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_149992827562333271835481297640 : ((p4 ∨ (p3 ∨ (((p5 ∧ p2) ∧ p1) ∨ ((p2 ∨ (((p3 → (p3 → True)) ∨ (p2 ∧ False)) → p2)) → p3)))) ∨ (p1 → (True → (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798935888368433245446726508575 : (((p1 → ((False ∧ p2) ∨ (((p3 → (p3 ∨ p3)) ∨ p5) → (p4 ∧ ((((p5 ∧ p2) ∨ p3) ∧ (p4 ∨ (p3 ∧ p1))) ∨ (True ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343028336076223606815580978057 : (p2 → (((p5 ∧ (p3 ∨ True)) → False) → ((((p5 ∨ ((((True ∧ (False → p2)) ∨ p2) ∨ p4) ∧ (p1 → p5))) ∨ (p1 ∧ p4)) ∧ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777460765763320734787261354225 : (((p1 ∨ ((True → (((p2 ∧ (((p4 → p4) → (True → (p3 → p3))) ∨ p2)) ∧ True) ∧ p1)) → ((((p1 → True) ∧ p4) → p1) ∨ True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_115023684909322881852851598048 : (((p2 ∨ (((True ∨ p2) ∨ (False ∧ (True ∧ False))) → (p4 ∧ False))) ∧ (True ∧ ((p3 ∨ ((p4 ∧ p1) ∨ p1)) ∧ (True ∧ False)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157049843547124802730506184924 : (((p2 ∧ (((((False → p1) ∨ (p5 ∧ False)) → (p3 ∧ ((False ∧ p4) ∨ False))) ∧ p3) ∧ p5)) ∨ True) ∨ (p2 → ((p4 ∧ (p3 ∨ p2)) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737410404634502159280548208590 : ((((p4 → p4) ∧ ((((((True → p4) ∨ True) ∨ p5) → False) ∧ ((((False → (p5 ∨ (p5 ∨ False))) ∨ False) → p1) → True)) → (p5 ∨ p2))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((True → p4) ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707303061748407755777737461395 : (((((((p1 ∨ True) ∧ False) ∨ p3) ∨ (p3 → p5)) ∨ (((p5 → (((p2 ∧ (p5 → p2)) ∨ ((p4 ∨ p4) ∨ p4)) ∨ p3)) → False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206275119662040433530416946038 : ((False ∨ (p5 ∧ ((p3 ∨ False) → p1))) ∨ (p5 ∨ (((False ∧ (p3 ∧ (p1 → (p3 ∨ p5)))) ∨ (p1 → (p5 → (p5 ∨ False)))) ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760087606129077155618491776561 : (((p2 ∧ (((p3 → p3) ∧ p1) ∨ (((p4 ∨ (((False ∨ p5) → p2) ∨ (p5 ∨ (p4 ∨ ((p1 ∧ p1) ∨ p1))))) ∧ (p2 ∨ False)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337516131730962583021527249144 : (p1 → (((((p1 ∧ (False ∧ (p5 ∧ ((p2 → p1) → True)))) → ((p4 ∧ (p5 → False)) ∨ p4)) → p4) ∧ p5) ∨ (((p3 ∧ p5) ∨ p4) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621445691130696863488799930867 : ((((False ∧ (((((((p1 ∨ True) ∨ p3) → ((p3 ∨ (p5 ∨ p1)) ∧ False)) → p1) ∧ p1) ∨ ((False ∧ (p4 ∧ p2)) → False)) ∧ p4)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_219553059989315879557572743590 : ((True → ((p1 ∨ p1) ∧ False)) → ((((p4 ∧ p3) → False) ∧ p2) ∧ (((True ∨ p3) → ((False ∨ ((True ∨ p2) → True)) → p1)) ∨ (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112657670230486475948378074040 : ((((p1 → (p5 → ((((False ∨ (p2 ∨ p5)) ∧ p2) → (p2 ∨ ((p3 ∧ p3) ∧ p5))) ∨ p3))) ∧ ((False → False) ∧ p4)) → False) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46828539018815998547549573573 : (((((((p3 ∨ False) ∧ True) → (((True ∨ ((True ∨ p4) ∧ p1)) → p4) ∧ (p4 ∧ p4))) ∧ ((False ∨ p1) → p3)) ∧ p5) ∨ (True → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337651054433007160911440337169 : (p1 → ((((p5 ∧ (p3 → ((p4 → p1) ∧ (p4 ∧ (p1 ∧ p3))))) → ((False ∨ p2) ∨ p3)) ∨ p1) ∨ (((p4 → (p1 ∨ True)) → p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



