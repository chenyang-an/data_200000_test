variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306680230071428397457183361868 : (p1 ∨ (True ∧ (p3 ∨ (p1 → ((p1 → (False ∧ ((p3 → p2) ∨ p2))) → ((p4 ∧ (p1 → False)) ∨ ((p1 ∨ ((p5 ∧ p5) ∨ p3)) ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190056980352140630552910248232 : (((((((p2 ∨ p3) ∧ p5) → p4) ∧ p1) → p2) ∧ p3) ∨ (p5 ∨ (((p1 ∨ p1) → (False ∨ p2)) → (True → (False → ((True → True) ∨ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351207602415880478575811550317 : (p4 → ((((False ∧ (p2 ∨ (((p1 ∨ ((True ∧ (p3 ∨ True)) ∨ p5)) ∧ True) ∨ p4))) ∧ ((p3 ∨ p1) → True)) ∧ p2) ∨ (p5 → (True → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149152458862664952413680804854 : (((p1 ∨ p1) ∧ (((True ∨ (p2 → ((False → True) → (p4 → True)))) ∨ (p1 ∨ ((p2 ∧ p4) ∧ p3))) ∧ p4)) ∨ ((p5 ∨ p5) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106698545127955359557555589972 : (((((p2 → (False ∧ p1)) ∧ p4) ∧ p2) ∨ ((False ∧ False) ∨ ((False ∨ True) ∨ ((((True → False) ∨ p3) ∨ p5) ∨ (p2 ∨ p5))))) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317751465227927614988512199029 : (p4 ∨ (((p3 ∨ ((p3 ∧ p2) ∧ (((p5 ∨ p3) ∨ ((p4 → (p2 ∧ p4)) ∨ (p5 → p2))) → True))) ∨ (p5 ∧ (p2 → (p3 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616741207616193162172057050131 : (((((((p3 → (p2 → p1)) → p2) ∧ ((p3 → p2) ∨ False)) ∨ ((((p4 → p5) → ((p1 ∧ p1) ∨ p1)) ∧ p1) ∧ (p4 ∧ p1))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_118863431198597721956856339648 : ((True → (((p2 ∧ (p5 → p1)) → p3) ∧ ((p5 ∧ p4) ∧ ((((p1 → True) ∧ ((p4 ∧ p3) ∧ p3)) ∨ (p4 → p1)) → p2)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458133593646936789185660060039 : (((((p5 ∨ (p2 ∧ True)) ∨ ((p5 ∧ p4) ∧ (True ∧ (p5 ∨ ((p5 ∧ (p2 ∧ p3)) ∧ p2))))) ∨ ((((p3 ∨ False) ∧ p4) ∧ True) → p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244809493122056412942090796214 : ((p1 ∧ p1) ∨ (((False → (((False ∨ p4) ∨ p1) ∨ (((p4 ∨ False) ∨ (p3 ∧ p2)) ∨ p5))) → ((p1 ∧ True) ∧ (p4 ∧ False))) → (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (((False ∨ p4) ∨ p1) ∨ (((p4 ∨ False) ∨ (p3 ∧ p2)) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (False → (((False ∨ p4) ∨ p1) ∨ (((p4 ∨ False) ∨ (p3 ∧ p2)) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301118755806743379914754820930 : (False ∨ (((p2 ∧ (True ∧ False)) → (p4 ∧ (p4 → p4))) ∧ (((p2 → (p5 ∨ (p4 ∨ True))) → False) ∨ (((p5 → p4) → (False ∧ p1)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149538537812444127288426547419 : ((p2 ∧ (((p5 ∨ ((p3 ∨ p5) ∧ p4)) ∨ (p5 ∧ ((True ∧ False) → ((False ∨ (p2 ∨ p5)) → p4)))) ∨ p5)) ∨ ((True ∧ p4) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181551222516429074766383979395 : ((False → ((((((False → (p1 ∨ p3)) → p3) ∧ p5) ∧ p2) → p2) → p3)) → (((p3 → p5) → ((p1 ∧ p2) ∨ ((p3 ∨ False) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136138556684799744788984916960 : (((((False → ((p1 ∨ p5) ∨ p1)) → p1) → False) → (((p3 ∧ (True ∧ (((p4 → p1) ∧ p5) ∧ p2))) → p4) ∨ False)) ∨ (p4 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617738554553985039332901714096 : (((((p2 ∧ (((p3 ∧ False) ∧ p2) ∧ p1)) ∨ ((p5 → (((((p5 ∧ p1) → False) ∧ p5) → p1) ∧ ((True ∧ p1) → False))) ∨ True)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165418683806654867244679088932 : (((((p2 → p5) → ((p5 ∧ p4) ∧ (p3 ∧ True))) → (True ∧ p5)) → ((p5 ∨ p3) ∧ p2)) ∨ (((True → p2) ∧ (False ∧ p3)) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149818798128077536229366312302 : ((p1 ∨ (((True ∨ (p3 ∧ (True ∧ False))) ∧ ((((p2 → (p5 ∧ p1)) → p4) ∧ (p2 ∧ p1)) ∨ True)) ∨ p5)) ∨ ((p4 ∧ p5) ∨ (p1 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217550732863988469224366789840 : ((((p1 ∧ p1) ∨ True) → p3) → ((p1 ∨ (p3 → (((p3 → p3) ∨ p1) ∧ (((p4 ∨ p2) ∧ (p2 ∧ p1)) ∨ (p4 → (p4 ∨ p1)))))) ∨ p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311049948818008335067416357870 : (p2 ∨ ((p5 ∧ p2) ∨ ((p2 → ((((p5 ∧ (p4 ∨ p5)) ∧ ((p4 ∧ (False → p2)) ∨ ((p4 ∧ p5) ∨ p3))) ∧ p2) ∨ (p2 ∨ p3))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53250747831826002623160643060 : ((((False → False) ∧ ((p4 → ((p5 → p4) ∧ (p5 → False))) ∨ False)) ∨ (((p3 ∧ True) ∨ True) → (p1 ∨ ((p1 → (False ∧ p1)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39686231031415559775779708736 : (((p4 ∨ ((False ∧ (p1 ∧ (p3 → ((p2 ∧ ((False ∨ False) ∨ p4)) ∨ p5)))) ∨ (((p2 ∧ ((True ∨ p2) ∧ p5)) → p2) → False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51651574445064795831021494032 : ((((p3 → (p1 ∨ (p1 ∨ (((p4 ∧ (p2 ∧ p1)) → (True → p3)) → p1)))) ∨ False) ∧ (((p5 ∧ False) ∧ p2) ∨ (p5 ∧ (p1 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_973674276263533508697801093620 : ((((p5 ∨ True) → ((p4 ∨ True) ∧ ((p5 ∧ (False → ((((p1 ∨ p1) ∧ p4) ∨ (True ∧ False)) → (((p4 ∨ p2) ∧ p5) ∧ True)))) ∧ False))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628747316554101094239381690499 : (((((p1 → (((False ∧ p5) → ((((p5 → p3) ∨ p2) ∧ p2) ∧ (((((p2 → True) ∨ p1) ∧ p2) ∧ p4) ∨ False))) ∧ False)) ∧ p1) → p5) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68900099213848027176719168907 : ((p4 → (p5 ∧ ((((((p2 ∨ (p1 ∨ p5)) → False) ∨ p5) ∧ p2) ∨ ((True ∧ False) ∨ (p2 → p2))) ∧ ((p4 ∨ True) → (p5 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219507560585673759569710457288 : ((p5 ∨ ((p5 ∧ p3) → p1)) → ((p4 ∧ (p1 ∨ (False → ((True → p5) ∧ p5)))) → (p1 → ((p2 ∨ (False ∨ (p1 ∨ (p4 → p2)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713237329042083142472076302324 : ((((p3 ∨ (((True ∧ p3) ∧ False) ∨ False)) ∨ (p5 ∧ (True → ((((p4 ∧ ((((False ∨ False) ∧ p5) → p5) ∧ p1)) → True) ∧ p5) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173892786067218443599633834906 : ((((False ∨ (((False ∨ p5) ∧ p3) → ((p3 ∨ (p4 ∧ p3)) ∧ p5))) ∨ p1) → False) → (((p4 ∨ (True → False)) ∧ (p2 → False)) ∧ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (((False ∨ p5) ∧ p3) → ((p3 ∨ (p4 ∧ p3)) ∧ p5))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((False ∨ (((False ∨ p5) ∧ p3) → ((p3 ∨ (p4 ∧ p3)) ∧ p5))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    -- Conjunctions on the left can always be decomposed.
    let h20 := h15.left
    let h21 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h14
  -- False on the left can always be used.
  apply False.elim h24
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249307834672962475226413594068 : ((p4 ∨ p5) ∨ ((((p4 ∨ False) ∨ (p5 → ((((p3 → p4) ∨ True) ∨ (p1 ∧ (p5 ∧ p2))) ∨ p5))) → False) ∨ (((p2 ∨ p5) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_112214693927350685080015422446 : (((False ∨ (p5 ∧ (p4 ∨ (((p1 → (p5 → ((p3 → (p2 ∧ True)) ∧ (False ∧ (p2 ∨ p4))))) ∧ p1) ∨ (p5 ∧ p1))))) ∨ p3) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217634025247715870156573812263 : ((((p2 ∧ p5) → p4) → p2) → (True ∧ (p4 → (p2 ∨ (False ∨ (((p1 ∨ (False ∨ p4)) ∨ (((p3 ∧ (p4 → False)) → False) → p3)) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ p5) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171998728982414087788873102630 : ((((((p5 → p3) ∨ (p4 ∨ ((p1 ∧ p5) ∨ True))) ∧ p4) → p5) ∨ (p3 → True)) ∨ (p5 ∧ (p2 ∧ (((True ∧ (p3 ∨ p1)) ∨ True) → p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173761370153334568747595433696 : (((((p2 ∧ p3) → p4) ∧ ((p1 → False) ∨ (((p5 ∨ p4) ∧ False) ∨ True))) ∨ p2) → ((False ∨ (p3 ∧ p4)) ∨ (((p1 ∧ p2) ∧ False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h14
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309602743127787739734133488092 : (p2 ∨ (((p4 ∧ (True ∧ ((p2 ∧ (p5 ∧ p4)) ∨ (p1 → ((p4 ∨ (p3 ∨ (p4 → (p3 ∨ False)))) ∧ True))))) ∧ p2) ∨ (p2 → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134054957501860057089346799197 : ((((p4 ∨ ((((True ∨ (p3 ∨ True)) ∧ (False ∨ ((p5 ∨ p1) ∨ True))) → False) ∧ (p2 → (p4 → True)))) ∨ True) ∨ p5) ∨ (p1 → (p1 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186802648866616457000632423786 : ((((p4 ∨ p3) → (p3 ∨ p3)) ∧ (((False ∨ p2) → p2) ∧ p2)) → (p4 → ((((False → p5) ∧ (((p5 ∧ p5) ∧ p1) ∨ True)) ∨ p5) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h16 : (p4 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h17 := h12 h16
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h25 : (p4 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h26 := h21 h25
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h34 : (p4 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h35 := h30 h34
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h37 =>
      -- One of the premise coincides with the conclusion.
      exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172681290797645987611117806724 : (((True ∧ p5) ∨ ((p1 ∧ p2) ∧ (p3 ∧ (p5 → (((True ∨ p1) ∨ p5) ∧ p3))))) ∨ ((((p2 ∧ (p4 → (False → p4))) ∨ p5) ∧ p4) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95275737792669159485482328041 : ((p4 ∧ (True ∧ ((True → (((((p1 → p1) ∨ True) ∨ True) ∨ ((p2 → (p2 ∨ (True ∨ (p1 → p4)))) ∧ p4)) ∧ p1)) ∨ (p4 ∧ p1)))) → p1) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319395168588235598431707980780 : (p4 ∨ (((((True ∧ ((p1 ∧ False) ∧ True)) ∨ p5) ∨ (p3 → p3)) ∧ (p2 ∨ p4)) → ((p3 ∧ (((False → True) ∨ p4) ∨ p1)) ∨ (p3 → p3)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622412351303440590657406132540 : ((((p3 ∧ ((((p1 ∨ False) → (p4 ∨ p1)) → p3) ∨ (p5 ∧ (((p4 ∧ p1) ∧ (p4 → p2)) → (True ∨ (False ∧ (True ∨ True))))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604427629633394233887055235288 : ((((True → (p3 ∨ ((False ∧ p4) ∧ (((p2 ∨ (p2 ∨ p1)) ∨ (((p1 → ((p2 ∧ p1) ∨ True)) ∧ (p2 ∧ p5)) ∨ p4)) → p5)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684729936860593079893316153582 : (((((p4 ∨ True) ∧ (p4 ∨ (((p4 ∧ p1) → p1) → ((p3 ∧ ((p1 ∧ p2) ∨ p3)) ∨ p1)))) ∨ (p5 → (((p2 ∨ False) → True) ∧ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41528970891237753379624330421 : ((((p1 → ((((p4 ∨ (False → True)) → p5) ∨ p5) ∧ p1)) ∧ ((p5 ∨ (p3 ∧ (False ∨ (p4 ∨ (p5 ∨ False))))) → (p3 ∧ p1))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115253679167505971949478539991 : ((((p2 ∨ (p1 ∨ (p4 ∨ False))) → ((False ∧ p2) ∨ True)) ∨ ((p3 → p1) ∨ ((p1 ∧ True) → ((p1 ∨ p4) ∨ (p4 ∨ p5))))) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153402629168528598653627424701 : ((p3 ∨ ((((p3 ∨ True) ∨ p5) ∧ p2) ∧ ((p1 → p2) ∧ (True ∨ (True ∧ (False ∧ ((p3 ∧ True) → False))))))) → ((p2 → p3) → (True ∧ p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h6.left
        let h12 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- False on the left can always be used.
          apply False.elim h17
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h6.left
        let h21 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h23 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h8
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h24 := h2 h23
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- False on the left can always be used.
          apply False.elim h28
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h6.left
      let h32 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h34 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h35 := h2 h34
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- False on the left can always be used.
        apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691679566740867351632289228288 : ((((True ∨ ((((p2 → ((p1 → (p5 → p2)) ∧ p1)) ∧ (p1 → p3)) ∨ True) ∨ p4)) → ((p4 → (p1 ∧ ((False ∨ True) → p5))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1567949239697048457848815776 : ((p2 → (p2 ∧ (p1 ∧ (((p3 → ((p4 ∨ ((p3 ∧ False) ∨ False)) ∨ True)) ∧ p4) ∨ (p4 ∨ ((p5 → p5) ∧ p1)))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200811146044210224526862786613 : ((p5 ∧ (((False → True) ∨ False) → (p2 → p4))) → (((((p5 ∨ (p5 ∧ True)) → p5) → ((p1 → False) ∧ (p2 → (p1 ∨ p1)))) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_161021892753247328790258012462 : (((True → (p2 ∧ True)) ∨ (((p1 → p3) → ((False → True) ∧ p1)) ∧ ((p4 → (p3 → p1)) ∧ p2))) → (((p4 ∧ p4) ∨ p2) ∧ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172182386898915187554329582771 : (((p1 ∨ (p3 ∨ (((p2 ∨ p2) ∧ p4) ∧ (p3 → p5)))) ∨ ((p2 → True) → False)) ∨ ((p5 ∨ (((p4 → p5) ∧ (p4 ∨ p3)) ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117912448157576939249618170117 : ((p5 ∧ (((p2 ∨ ((p5 ∨ (p4 ∨ p1)) ∨ p4)) ∨ p3) ∧ (p3 → ((p3 ∨ (True ∧ p5)) ∨ ((p2 ∧ p5) → (p3 → p2)))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706143285347144761704669481386 : (((((p3 ∨ p5) → ((p4 ∧ (p5 ∧ p3)) → p5)) ∧ (p2 → ((p4 ∧ (False ∧ (((False ∧ False) ∨ (p5 ∧ p1)) ∧ p3))) ∨ (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623021016694523092964549104146 : ((((p5 ∧ (p1 ∧ (p1 ∧ (p5 ∨ (True ∧ ((True → ((((False ∨ p3) ∧ p3) ∨ (((False → p1) ∧ p3) → p4)) → p5)) ∨ p2)))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_173246189207019341553416320391 : ((True → (False ∧ ((p2 → (p5 ∨ (p5 ∧ False))) → (p3 ∨ (p3 ∧ (p2 ∧ p4)))))) ∨ (((False ∧ ((True ∧ p1) ∨ p3)) ∧ True) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38515945521767509932718337105 : (((((((False ∨ True) ∨ (p5 ∧ p1)) ∨ ((True → p4) → p5)) ∨ p3) → ((p5 ∧ (p4 ∨ (True ∧ p3))) ∨ ((p5 ∨ p3) ∧ p1))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325989182032080112940737650372 : (p5 ∨ (True → ((p5 → (((p5 → (p1 ∨ (((p5 ∧ False) → p3) → ((False → p4) ∧ (False ∧ p3))))) ∧ (p4 → True)) ∨ True)) ∨ (p2 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121075467084088628864925406871 : (((p1 ∧ (p3 ∧ (((p4 → True) ∨ (((p1 ∨ p1) ∨ (True ∨ p2)) ∨ (p1 ∨ p3))) ∨ (((False → p2) ∧ True) ∨ p3)))) ∨ p2) → (p2 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h16 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130932472493517578240198010344 : (((((((p4 ∧ p3) ∨ ((p4 → p2) ∨ p5)) → p5) ∨ p5) ∧ p2) → ((False → p3) ∧ (((p4 ∧ False) ∨ True) ∧ p2))) ∧ ((p3 ∨ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352005627817402557558094428489 : (p4 → (((True ∨ p1) ∧ (False ∧ (p5 ∧ (False ∧ p2)))) ∨ (((p2 ∨ True) ∨ p1) → ((p1 ∧ p4) ∨ ((False ∧ (p5 ∨ (False → False))) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h12
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40926729739435517055855849734 : ((((((p4 ∨ (p3 ∧ ((p3 → (p5 ∨ (p2 ∨ (p4 ∨ ((False → False) ∧ p1))))) → (p1 ∧ p5)))) ∨ p5) ∧ p1) ∨ (False → p2)) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608305730612149700305799228003 : (((((((((((False → p5) → ((p4 ∧ True) → p2)) → p4) ∨ p3) ∧ p4) ∨ ((p4 ∧ (False ∨ (p2 → False))) ∧ p1)) ∨ p3) ∨ False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327911689105324120871539984675 : (True → ((((p2 → (p1 ∨ (p5 → (p5 ∨ p5)))) ∧ (((p3 → p5) → p5) → (((True → (p3 ∧ p1)) ∧ p3) ∧ True))) ∧ p3) → (p3 ∧ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : ((p3 → p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h15 := h10 h11
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323606678312538096691894187290 : (p5 ∨ ((((p3 → p5) ∨ (((((True ∧ (p2 → p5)) → p2) ∧ (p4 ∧ (False ∨ p2))) ∧ p3) ∧ False)) ∨ True) ∧ (((p2 ∧ p1) ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320539756566331233998481761444 : (p4 ∨ (True ∧ ((p5 → p3) → (False ∨ ((True → p1) ∨ (p2 ∨ ((p2 ∨ (p2 → (p2 → (((p3 ∨ (True ∧ p5)) ∧ True) → False)))) ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_704032362328400880251242312813 : ((((((p5 → (p4 ∨ p4)) ∨ ((p4 ∨ p4) → p4)) → p1) → (p3 → ((True → ((p4 → p3) ∧ (((p1 → True) ∧ True) ∧ p4))) → p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604020426129962070800042552983 : ((((p5 ∨ (((p2 ∨ (False ∨ (p1 ∨ (p3 ∧ p1)))) → ((p5 ∨ (p1 → ((True → p3) → p5))) ∧ False)) → ((p2 → False) ∨ p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172402697658870334965831333854 : (((p5 ∨ (((True ∧ p3) ∨ p2) ∧ p2)) → ((((False ∧ p5) ∧ p3) ∧ p2) ∨ p4)) ∨ (p4 ∨ (p4 ∨ ((((False ∧ False) ∧ p5) → p4) ∨ True)))) := by
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
theorem thm_5_vars_301323667142992203100353924705 : (False ∨ ((((p4 ∧ p3) ∧ p3) → p4) ∧ (((((((p1 → p2) ∧ (p5 ∧ False)) ∧ p3) ∨ p2) ∨ p1) ∨ (False → p5)) ∨ ((p3 ∧ p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186077147233887849328424815927 : (((((p1 ∨ (True ∧ (p3 ∧ (p1 ∨ p2)))) → p4) → p4) ∨ p3) → ((((p2 ∨ ((p5 ∧ p3) ∨ (True → p5))) ∨ True) ∨ p1) ∧ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749797100036453096597028786979 : (((True ∧ (((p5 → p1) → (((p4 → (p4 → (True → p3))) → p1) ∨ ((p5 ∧ p5) ∨ (((p5 ∧ True) ∧ (p5 ∨ p2)) ∨ p3)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317715790315620858532517189015 : (p4 ∨ (((((p2 ∨ ((((p2 → p5) → p2) → (False → p4)) → (False ∨ (p2 ∧ (True → (p3 → p4)))))) → p5) → p2) → (p4 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50567404674357252226736508543 : (((((((p3 ∨ p4) ∨ ((False → p2) ∧ (True ∧ (False → p4)))) → (p3 ∨ p4)) ∧ (p5 ∨ p1)) → p4) → ((p5 → (p3 ∧ p4)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40296136226907162006489553945 : ((((p5 → ((p5 ∨ p3) → (((p1 ∧ p5) ∧ (((True → p2) ∨ p4) → p3)) ∨ ((p3 ∨ p1) → (p4 ∧ (True → p2)))))) ∧ p4) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327105593556133587785330758710 : (True → (((p1 ∧ p1) ∨ ((((p2 ∨ ((False ∨ p1) ∨ p4)) → (((p3 ∧ True) → p3) ∨ ((p3 ∧ p2) ∧ False))) ∨ (False ∨ p4)) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157215126044303938709667537675 : ((((((p2 → p5) ∧ p3) ∧ (p4 → (p3 → ((True ∧ False) → p2)))) ∧ ((p1 ∧ p2) ∨ p1)) → p4) ∨ (((p2 ∨ (True → True)) ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164789560728736383226253015956 : (((((p3 ∨ (True ∧ p2)) ∧ p1) ∨ (p4 → ((p1 → (p5 → (p5 ∧ p3))) ∧ p4))) ∨ p5) ∨ ((True ∨ True) ∨ (p3 ∧ ((p4 ∨ p4) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68115628719540976702783252145 : ((p2 → (p3 → (((p5 ∨ ((((True → ((p2 ∧ False) ∨ (False ∨ p3))) → (p3 → p4)) ∨ (False ∨ (p5 → p3))) → False)) ∧ p2) ∨ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114409926239118975248848285737 : (((((p1 ∨ False) ∨ p1) ∧ (p5 ∨ (p4 ∧ (p4 → (((p5 ∧ p3) ∧ (p1 ∨ p1)) ∨ False))))) ∨ (True ∨ ((p5 ∧ True) ∧ p2))) ∨ (False → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318212273735963321133092807180 : (p4 ∨ (((((False ∧ p4) ∨ (True → False)) ∧ (p1 ∧ (p4 ∨ p2))) ∧ (False ∨ (p3 ∨ ((True ∧ ((p3 → (False ∨ p2)) ∨ False)) → p1)))) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h22 := h9 h21
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h25 := h9 h24
          -- False on the left can always be used.
          apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231114440405250306620290285308 : (((p1 ∨ True) ∨ p3) → (((p4 ∧ p5) ∨ (False ∨ (p4 ∨ (((p3 → (False → False)) ∨ p2) ∨ (p2 ∨ ((p4 → p4) ∧ (p3 ∧ False))))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688317361664932109571418069819 : (((((p2 ∨ p4) → (((p4 ∨ (((p4 ∨ True) ∨ p3) → False)) ∧ p1) → (p2 ∨ False))) ∧ ((p1 ∨ (((p5 ∧ True) → False) → p5)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135816805830734803701882132370 : ((((((p2 ∧ False) ∧ ((p1 ∨ p4) ∧ p3)) ∧ (p5 → True)) ∨ p4) ∧ (p1 ∨ ((p2 → (p4 ∨ True)) ∨ (p4 ∨ p4)))) ∨ ((p3 ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41086254732382116193414531939 : ((((((False → (p1 ∧ (p3 ∨ p2))) → ((p4 ∨ ((p5 ∨ p2) ∧ (True ∧ p5))) → (p1 ∧ p2))) ∨ True) ∧ (True ∨ (p4 → False))) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_310169143006238502776158329749 : (p2 ∨ ((p4 → ((False ∧ p5) ∧ (True ∨ (((True ∨ True) → (p1 ∧ p2)) → p4)))) → (((p5 → ((True ∧ True) → p3)) ∨ (False ∨ True)) ∨ p4))) := by
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
theorem thm_5_vars_200679225207242187285067995936 : ((p1 ∧ (p2 → ((p5 → (p2 → p4)) ∨ p4))) → (((p5 → False) ∨ ((((p1 ∧ p4) ∨ True) → p5) ∨ False)) ∨ ((False → (p2 → True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165196110781354419422531135771 : ((((((p3 ∨ p5) ∧ (True → (((True ∧ p2) → p3) ∨ False))) ∧ p3) ∨ p2) ∨ (p4 ∨ p4)) ∨ (True ∨ (p4 → ((p2 ∨ (p5 ∨ p2)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250102223446367862756565459817 : ((True → p4) ∨ ((((p3 → p5) ∨ ((p4 → ((False ∨ p4) ∨ True)) ∨ False)) ∧ p4) → ((p1 → ((((p4 ∨ True) → True) → p2) ∨ p4)) ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109792086658752592610488270029 : ((p5 ∨ (((p1 ∨ (True → ((p3 ∧ False) → False))) ∧ (p4 ∨ ((p1 ∧ p4) ∧ (True ∨ (p1 ∧ (False ∨ p2)))))) → (p3 ∨ p4))) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198381752242896843335701856704 : ((p3 ∧ (((True ∧ False) → p1) → (p2 ∨ p2))) ∨ ((True ∧ False) → ((p4 → True) ∨ (p1 ∨ (((((p2 ∨ p5) ∨ p3) ∧ False) ∧ False) → p1))))) := by
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
theorem thm_5_vars_261601797442143153656439265112 : ((p5 → p4) → (p1 ∨ ((p1 ∧ True) ∨ ((((p5 ∧ (p3 → p3)) ∧ p2) ∨ ((p1 → (p2 ∨ (p4 → (False → (p2 ∨ p4))))) ∨ p3)) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118700387897223105509774494606 : ((p5 ∨ ((p5 → ((p4 → ((((p5 ∨ p1) ∨ p1) ∨ p5) ∨ (p3 → (True → p3)))) → (p3 ∨ (p1 ∧ (p2 → p4))))) ∨ p3)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47494817084028013825968929940 : (((p1 ∨ (((p3 ∧ p2) ∨ ((False → ((p2 ∨ True) ∨ True)) ∧ ((p4 ∨ (True ∨ ((True → p1) ∨ p4))) → p3))) ∧ False)) ∨ (p4 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157407758262538192163095619474 : ((((p4 ∧ ((p5 ∨ p2) ∧ (p1 ∨ (p4 ∧ (p5 → False))))) ∨ (p1 → (p1 ∨ p4))) ∧ (False ∧ True)) ∨ ((True ∧ ((p4 → p2) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342305533619091882071611658337 : (p2 → ((p4 → ((p4 ∨ (False ∨ (False ∨ (False ∨ p1)))) ∧ (p3 ∨ ((p2 → (p5 ∨ p1)) → p5)))) ∨ (p5 ∨ (((p5 ∨ p2) ∨ p4) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810854102859591046671682599248 : (((p5 → ((p4 ∧ p3) ∨ (((((p4 → p1) ∧ p3) ∨ False) ∧ p5) ∨ (((p2 ∧ p4) ∨ ((p1 ∧ (p3 ∧ True)) → p1)) → (False ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711326637478948050930911084026 : ((((False ∨ ((p2 → p4) → (p5 → p4))) ∧ ((False ∨ (((((p5 ∧ True) ∨ False) ∨ (True ∧ (p4 → p4))) ∨ p4) ∧ (p2 ∧ p5))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316411012912107761810344206534 : (p3 ∨ (False ∨ (p2 ∨ ((False ∨ ((p3 ∧ (p2 ∨ p1)) ∨ ((p2 ∨ p3) → False))) → (False ∨ ((p2 ∧ ((p3 ∨ p3) → (p5 ∧ p4))) → p5)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : (p3 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- We need to get the left conjuct of h12 based on <expert-advice>.
        let h13 := h12.left
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : (p3 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h19 := h17 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h25 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h26 := h21 h25
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301306309342592468737725426681 : (False ∨ ((p5 ∨ (True ∨ ((p3 ∧ p3) ∧ p2))) → ((p3 ∧ p3) ∨ ((((p4 → (p3 → ((True ∧ (p1 → p4)) ∨ p4))) ∨ p5) → p2) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 → (p3 → ((True ∧ (p1 → p4)) ∨ p4))) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((p4 → (p3 → ((True ∧ (p1 → p4)) ∨ p4))) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h9
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h17
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117047469528600739589080523846 : (((p4 ∨ p1) → ((((p5 ∨ p5) ∨ (((False ∨ ((p5 ∧ True) → ((p1 ∨ False) → p4))) ∧ p2) → p1)) ∨ (False ∨ False)) ∨ p4)) ∨ (p4 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118141415202404427687734117432 : ((False ∨ ((True ∧ ((p3 ∨ ((p1 ∨ p4) → (False ∨ (False ∧ (p2 ∨ True))))) ∧ p1)) ∨ (True → (p4 ∧ (p5 ∨ (p2 ∨ p2)))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



