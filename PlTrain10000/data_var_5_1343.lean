variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41402721672720080782199664167 : (((((((True → False) ∧ (True ∧ (p1 ∨ (True ∨ p3)))) ∧ (True ∧ p2)) ∧ p1) ∨ ((p4 ∧ p5) ∨ (p4 ∧ ((p4 ∧ p1) → p5)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174077632172646220422255723832 : ((((((False → (p2 → (p4 ∨ (p4 ∨ p2)))) ∧ p3) ∧ True) → False) ∧ (p3 ∧ True)) → (p5 ∨ (p1 ∧ (((p5 → p4) ∨ p2) ∨ (p2 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((False → (p2 → (p4 ∨ (p4 ∨ p2)))) ∧ p3) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h7
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41516863503678149362116287072 : (((((p3 ∨ (True → ((p5 ∧ p5) → p3))) ∧ (p1 ∧ p2)) ∧ (((False ∨ p2) ∨ p2) ∧ (p2 ∨ ((p5 ∧ (True → p4)) ∧ True)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42300800082865631735622775336 : (((p2 ∧ ((False ∨ (((p5 ∨ p4) ∨ ((((p5 ∧ p5) → p1) ∨ p1) → p2)) ∨ (p3 ∧ ((p4 ∨ p5) ∧ p3)))) ∧ (True → p3))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56770614192802717904794058643 : ((((False ∧ p1) → False) ∧ ((((((p5 → ((p3 ∨ True) ∨ ((p4 ∨ True) → False))) → p1) → p3) → (True → p4)) → (True ∧ p1)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248632302794116969589304088695 : ((p3 ∨ p1) ∨ ((((p2 ∨ (((((p2 → False) ∨ p5) → (p5 → p4)) → p5) → p1)) → p4) → (p4 → (p3 → (True ∧ p4)))) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115819282226587787818828378360 : ((((p4 → False) ∧ (p1 → p5)) ∧ ((p5 ∧ (p3 → p1)) ∨ ((p4 ∨ ((p3 ∧ (p3 → (p2 → p1))) ∨ (False ∧ True))) → p4))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134802483270417387794087602052 : (((p4 ∧ ((((True ∨ p1) → p3) → False) ∨ ((((True → False) → p2) ∧ (p5 → (True ∨ p1))) ∨ (p3 ∨ True)))) → False) ∨ (p2 → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15473144487027858969800227472 : (((((p4 ∧ p1) → (((True → (False ∧ (False ∨ False))) ∧ (False ∨ ((((True ∨ p3) → p2) ∨ True) ∨ p1))) ∨ p4)) → False) → (False ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p1) → (((True → (False ∧ (False ∨ False))) ∧ (False ∨ ((((True ∨ p3) → p2) ∨ True) ∨ p1))) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_947094964625680539783942646399 : ((((((True ∧ False) ∧ p1) → True) → (((p2 → (p1 ∧ ((p2 ∧ (((p3 → (False ∧ p4)) ∨ p1) ∧ p1)) → p5))) → (p3 ∧ False)) ∧ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ False) ∧ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216404189011191046773669502182 : ((p3 → (p4 → (p2 ∧ False))) ∨ ((p2 ∨ (p3 ∨ p4)) ∨ (p3 → ((p3 ∧ p1) ∨ ((p5 ∨ (p1 ∨ (False → True))) ∨ (p5 → (False ∧ False))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707425331492579318840591172082 : ((((((p4 ∨ p3) ∧ p1) ∧ (p3 ∨ (True ∧ p5))) ∨ ((False → p1) ∨ (((False ∧ p5) ∧ ((((p5 ∧ True) ∧ p2) ∧ p4) ∨ p2)) ∧ p5))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147570907207414471691729276935 : (((((((p3 ∨ False) ∧ (True ∧ p5)) ∧ p1) ∨ ((p3 ∧ ((p2 ∨ p4) ∧ p3)) → (p4 → p3))) ∧ True) → False) ∨ ((False ∨ (True ∨ p3)) ∨ False)) := by
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
theorem thm_5_vars_352269147066799095689671556408 : (p4 → (((p4 ∨ (p3 → p5)) ∨ p3) → (p1 ∨ ((((((p1 → False) ∧ True) → ((p5 → (True ∨ (False ∧ p4))) → p4)) ∧ p3) ∨ p4) ∨ p1)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317693402816293439690268627547 : (p4 ∨ ((((p1 → ((p2 → (p3 → (False ∨ p3))) → ((p1 → (p5 ∨ False)) ∧ (((p1 ∨ False) → p2) → p2)))) ∨ p3) ∧ (p5 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53681351949530869554581046652 : (((False ∧ (((p1 → (p2 ∨ True)) ∨ p4) ∨ (p5 → False))) ∧ ((p1 → ((False ∨ p3) ∧ (True → (False ∧ p1)))) ∧ ((p4 ∨ p2) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169855379234778569977836096521 : ((((True → ((p4 ∨ ((p1 → p4) ∨ p1)) ∧ (p5 ∨ False))) ∨ p5) ∨ (True ∨ p4)) ∧ ((((p4 ∧ (p1 → True)) → p4) → (p4 ∨ p3)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42406018299987760403443182508 : (((p4 ∧ (p4 → (((p2 ∧ (True → (((p2 ∨ (p1 → p2)) ∧ True) → (p1 → (p5 ∨ (False ∨ p5)))))) ∧ (p2 → p3)) ∨ p4))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227074644244329424750769534641 : (((p3 ∨ p2) → False) ∨ ((p1 ∨ (((p1 ∧ p3) ∧ p3) ∨ (False → (((p5 ∧ p5) → True) → (((p3 ∧ (False ∧ p4)) → p3) ∨ p3))))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_890463690626930430490726617 : ((p2 → (((p4 → ((p3 ∧ (((p5 ∨ p1) ∧ (p3 ∨ (True → True))) ∨ (False ∨ ((True ∨ p4) ∧ p2)))) ∨ p2)) → True) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135056568810360697213296017910 : (((((True ∨ (False ∨ (False ∨ (((((True → (p4 ∨ False)) ∨ p5) ∨ True) → True) ∨ False)))) ∨ False) → p2) ∨ (p3 ∨ True)) ∨ (p1 ∧ (p4 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183874314252014300388029809757 : (((((p5 ∨ True) ∨ p4) ∧ (p2 ∨ ((p3 → p2) ∧ p4))) ∧ p5) ∨ (((p1 ∨ p3) → (True ∧ (p3 → ((p2 → False) ∨ p3)))) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310263449598258793425611890882 : (p2 ∨ (((p4 ∨ (p1 ∧ ((p5 ∧ (p4 ∨ p3)) → p3))) ∨ True) ∧ (p1 ∨ (p1 ∨ ((False → (((False ∧ p1) ∧ p3) → (p4 → p1))) ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674572032314137876696387135414 : ((((True → ((((p2 ∧ ((p3 ∧ False) ∨ p5)) ∨ p4) → p5) → (p3 ∨ (((True ∧ True) ∨ True) ∨ (p4 ∨ p5))))) → (p5 ∧ (True ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42005781084937984764295641075 : ((((p3 → True) ∧ ((((p1 ∨ p5) → ((p5 → False) ∧ False)) → p2) ∨ (p4 → (((True ∧ p3) ∧ p5) → ((False → p2) → p2))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662304867598222577072573182233 : (((((True → (p1 ∨ ((((p3 → p4) → p4) ∨ True) ∨ True))) → (((p2 → ((False → p4) ∧ (True → p2))) ∧ False) → p5)) → (p5 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137631306174032606128896299847 : ((False ∨ ((((p2 → p4) → ((False ∨ False) ∨ False)) → (False ∨ (p3 ∧ (p1 ∨ (p1 ∨ (p3 → p3)))))) ∨ (p4 → True))) ∨ (p2 → (p4 ∨ p4))) := by
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
theorem thm_5_vars_200523754001700495717403591787 : (((p2 ∨ p4) → ((p4 ∧ (True ∧ p5)) ∧ True)) → ((((p4 ∧ False) ∨ False) ∨ (((p4 ∨ True) ∨ p2) → (False ∧ p3))) → ((p4 ∧ p1) ∨ p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((p4 ∨ True) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229434924310503721697776234710 : ((p1 → (p1 → p5)) ∨ (((((((p1 ∧ p4) → (p3 → p3)) → (p4 ∧ ((p2 ∧ p3) ∨ p5))) ∧ p2) ∨ p5) → p4) → ((p5 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310288608007615233687525729506 : (p2 ∨ ((((((p4 ∨ p5) ∨ p2) → False) ∧ (p2 → True)) ∧ p1) ∨ ((True → False) ∨ (True → (False → ((p1 → p5) ∧ ((p3 ∧ p5) ∧ p2))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
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
theorem thm_5_vars_612820894696967580758856722441 : ((((((p1 ∨ p2) → ((((True ∧ ((False ∧ True) ∧ p5)) ∨ p2) ∨ ((p2 → (p1 ∨ True)) ∨ p1)) ∧ (p3 ∧ p1))) ∨ (True ∧ False)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317613124985023742445601001089 : (p4 ∨ ((((((((p3 ∧ (True → p4)) → p1) → ((((p2 → p4) → True) ∨ (p4 ∧ p3)) → p5)) ∨ (True ∨ p5)) ∨ p4) ∧ True) ∨ p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157716809452457197063171644753 : (((((True ∧ p1) → (p4 ∧ True)) → (p2 ∧ (p4 ∨ ((p5 → False) ∧ True)))) → ((p2 → p1) ∨ p1)) ∨ ((((p5 ∧ p4) ∨ False) ∧ p2) → p4)) := by
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
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224980619149227419901245263718 : (((True ∧ False) ∧ p4) ∨ ((p5 ∨ (((p4 → False) → ((True → True) → (((p5 ∧ (p1 ∨ False)) ∧ p1) → p5))) ∨ p1)) → (p3 ∨ (p3 → p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148589555075425639940688558002 : ((((p5 ∨ ((True ∧ p3) ∧ False)) ∨ ((p3 → p3) → p5)) ∨ ((False ∨ False) → (False ∨ ((p1 → p4) ∨ p1)))) ∨ ((p1 ∧ p1) ∨ (p4 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902732572961085776990271560068 : ((((((p3 ∧ False) → False) ∧ (((False ∨ (p4 → p3)) → ((((p3 → p1) → p5) ∧ p1) → p5)) → False)) ∧ (((p3 ∨ p5) ∧ p1) ∨ p4)) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : ((False ∨ (p4 → p3)) → ((((p3 → p1) → p5) ∧ p1) → p5)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h17 : (p3 → p1) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h19 := h13 h17
          -- One of the premise coincides with the conclusion.
          exact h19
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h20 := h5 h10
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h22 : ((False ∨ (p4 → p3)) → ((((p3 → p1) → p5) ∧ p1) → p5)) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h21
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h29 := h5 h22
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h31 : ((False ∨ (p4 → p3)) → ((((p3 → p1) → p5) ∧ p1) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h32
      -- Implications on the right can always be decomposed.
      intro h33
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h36 =>
        -- False on the left can always be used.
        apply False.elim h36
      case inr h37 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h38 : (p3 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h39
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h40 := h34 h38
        -- One of the premise coincides with the conclusion.
        exact h40
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h41 := h5 h31
    -- False on the left can always be used.
    apply False.elim h41
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62718579975883678053975992819 : ((p4 ∧ ((p3 ∨ ((p3 → (False ∨ (((p4 → (p2 → (p2 ∨ (True → p4)))) ∨ p3) → (p4 ∨ False)))) → (p2 ∧ (False → p5)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127782228249862261969801514610 : ((True → ((p3 ∨ (p1 ∨ (p4 ∧ (((p4 ∨ p1) → True) → p3)))) ∧ (((p4 ∧ p3) ∧ p3) ∧ (True ∧ (False → (p1 → True)))))) → (p3 ∨ p2)) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124292409038166330245253348908 : (((((((p4 ∧ p1) ∨ p5) ∧ p3) → p4) → p1) ∧ ((p3 ∨ p4) ∧ (((p3 ∨ (p4 ∧ False)) → ((True ∧ p4) ∧ False)) → False))) → (p1 ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : ((((p4 ∧ p1) ∨ p5) ∧ p3) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319538380720706315319175891078 : (p4 ∨ ((((False ∧ (p4 ∨ p3)) ∨ (False ∧ (p5 ∨ False))) ∨ False) ∨ ((p1 ∧ ((True → (p3 ∧ p3)) ∨ p3)) → (p4 ∨ ((False ∧ True) → p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184975553039020926162640789909 : (((p4 ∨ (True ∧ p3)) → (p1 → ((p1 ∧ (p4 → False)) ∨ False))) ∨ (p2 ∨ (((p1 → p2) ∨ p1) ∨ ((p1 → p1) ∨ ((p5 ∧ True) ∨ p2))))) := by
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
theorem thm_5_vars_225440455370069240317236027039 : (((p3 ∨ p5) ∧ p2) ∨ (False ∨ (((p1 ∧ True) ∨ p4) ∨ (True ∨ ((False ∧ False) ∨ ((p5 ∧ (p4 ∨ ((p2 ∨ True) ∧ (p4 ∧ p4)))) → False)))))) := by
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
theorem thm_5_vars_688863130375018852735340714534 : ((((((p3 ∧ (p1 ∧ ((p2 → p1) → (p2 ∧ (True ∨ p3))))) ∨ (p2 ∨ p5)) ∧ p2) ∨ ((False → (True ∧ ((p1 ∨ p1) ∧ p1))) ∨ p5)) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218239586913533289688311822409 : (((True ∨ False) ∨ (p3 → p1)) → (True ∧ ((p3 ∧ p2) ∨ (((True ∨ p4) → (p5 ∧ False)) → ((False ∧ (((False → p4) ∧ True) ∨ p3)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604218532970191230549747961805 : ((((True → ((((p5 ∨ (p3 → True)) ∨ ((((p4 ∧ p3) ∧ ((p4 ∨ p5) ∨ ((True ∧ True) ∧ p2))) ∨ p1) → p4)) → p2) ∨ p2)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217544980676221517655088889104 : ((((True ∧ p4) ∨ True) → p5) → (((((((p1 ∨ p5) → (p3 → p3)) → ((False ∧ False) → p2)) → (p4 ∨ p5)) ∧ p5) ∨ (False ∧ p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137161034185478809904688747335 : ((False ∧ ((((p2 ∧ p1) ∨ ((p2 ∨ ((False ∧ p1) → ((p1 ∧ p2) ∨ (p2 → p4)))) ∧ (False ∧ p4))) → p3) → p2)) ∨ (p4 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263098190683435619935196750242 : (True ∧ ((((((False → ((p3 → p4) → (p5 → ((p2 ∧ p3) ∧ True)))) → (False ∧ p2)) ∧ (p1 ∨ p5)) ∧ p1) ∧ (p5 ∧ True)) ∨ (p3 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60154446945669108746877414505 : (((p4 ∨ p4) → (((((p2 → False) → ((p2 ∨ (False → p1)) → p1)) ∨ (p5 ∧ ((p4 ∧ (True ∧ (p2 ∨ p3))) → p3))) ∨ p1) ∨ p4)) ∨ p1) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182433012113782840994344763785 : (((((((p2 ∨ p5) ∨ p3) → True) ∨ False) → p5) ∨ (True ∨ p3)) ∧ (False ∨ (((p2 → ((p2 → ((p5 → p5) → p1)) ∨ p1)) → True) ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168886885836519361052743647251 : ((p4 ∨ (p5 ∨ ((True ∨ ((True → (p5 ∨ (False → p2))) ∧ (p3 ∧ p4))) → (p5 ∧ p1)))) → ((p4 ∨ p2) ∨ (p5 ∨ ((False → p2) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ ((True → (p5 ∨ (False → p2))) ∧ (p3 ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260589243748555109699601691415 : ((p3 → p2) → ((True → (((p3 ∨ (False → p5)) ∨ ((p3 → (p4 ∨ p2)) → (((p5 ∧ p4) ∧ p2) ∧ p3))) ∧ ((p3 ∨ p2) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177961185441460644940678992539 : ((((p2 ∨ p4) ∨ ((p4 ∨ (p1 → ((p2 ∨ p3) ∧ p2))) ∨ True)) ∨ p2) ∨ (((((p3 ∧ True) ∧ p5) ∧ p5) ∧ p3) ∨ (True ∨ (p1 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87794140930127137676360942986 : ((((((p4 ∨ True) → False) ∧ p2) → p3) → ((False → p1) ∧ (((p4 ∨ p5) → ((((p4 ∨ (p2 → p2)) ∧ p1) ∨ p5) ∨ p4)) → p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ True) → False) ∧ p2) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((p4 ∨ p5) → ((((p4 ∨ (p2 → p2)) ∧ p1) ∨ p5) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h14 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330437138948482163336916195858 : (True → (p3 ∨ ((p5 ∧ (p2 → ((((((p2 ∧ p1) → p5) → p5) → (p5 → p3)) ∨ p1) ∧ p5))) ∨ (((False ∧ (p3 ∨ p4)) → False) → True)))) := by
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
theorem thm_5_vars_172710501007022130009170948114 : (((p2 ∨ p3) ∨ (p2 ∧ (p1 ∧ (p2 ∨ (((p4 ∧ (True → p4)) ∧ p3) → True))))) ∨ (((True ∧ p1) → ((p1 → True) ∨ (p4 → p4))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657434611389610126012962281582 : (((((False ∧ p3) ∨ (((((p5 ∧ ((True → p2) → p4)) → True) ∨ p2) → (False ∧ (p4 → p5))) ∨ (p1 ∨ (p1 ∨ True)))) ∨ (p5 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_147507690252866165702729983544 : (((p2 ∨ (((((p1 ∨ True) ∧ (((p2 ∧ p2) → False) → p2)) → p5) → p2) ∧ ((False → p2) → False))) ∨ p3) ∨ (True ∨ ((p4 → True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58899284374752247676384978073 : (((False ∧ p4) ∨ (p4 ∨ (p4 ∨ (p4 ∨ (True ∨ (((p2 ∨ p2) → (((p5 ∧ p5) ∧ (p4 → ((True → p3) → p4))) ∨ True)) ∧ p5)))))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59318710447613237683148201265 : (((p4 ∨ p2) ∨ (((((p5 → p2) ∧ False) ∨ (p2 ∨ (True ∨ (p5 ∧ True)))) ∨ True) → ((((p3 ∧ p5) ∧ p2) ∨ False) ∨ (p5 → True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
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
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357070946400868309787804408130 : (p5 → (((True ∧ True) ∨ False) → (((p4 ∧ ((p1 → ((p3 ∨ (False ∧ ((False → p3) ∧ p1))) ∨ p2)) ∧ p3)) ∨ ((p2 ∧ p2) ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187775407324869931530159620119 : ((p3 → (((p5 ∧ p4) → ((p2 ∧ p3) ∨ (True ∨ p1))) ∧ False)) → (((p5 ∨ (p5 → (p1 ∧ ((p3 ∧ p4) → p2)))) → False) ∨ (p3 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303845880527125632503835626011 : (p1 ∨ ((((((p3 → p3) → ((True ∧ True) ∨ True)) ∨ (True ∨ (p2 → (p1 → (((True → True) → p2) ∧ False))))) ∨ p5) → (p1 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234074826407363602077124371796 : ((True → (p1 ∧ True)) → ((False ∨ (True ∧ (p2 → (((p5 → (False ∨ (p3 ∧ p4))) → p4) ∨ (p1 ∧ p2))))) ∨ ((True ∨ (p5 ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305286354291194778647162341543 : (p1 ∨ (((((False ∨ (p5 ∧ p4)) ∧ (p2 → p5)) ∨ ((p5 ∨ (True ∨ False)) ∧ (p2 → False))) ∧ p2) ∨ (((p1 → p1) ∨ p4) ∧ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47722137932725544324409740094 : (((((((p4 → (p4 ∧ p1)) ∧ False) ∨ (((p3 ∧ (p1 ∨ True)) ∧ ((True → (True → p5)) ∨ p2)) ∨ True)) → False) ∨ p2) → (p4 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264245591693684931098425836771 : (True ∧ ((p3 ∨ ((p4 ∨ (True ∧ p4)) ∨ True)) ∧ (p2 → (((p3 ∨ p5) ∨ (True → (p3 → (p1 → ((p1 ∨ p3) ∨ False))))) ∨ (p5 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615029803161222694189394760681 : (((((True ∧ ((False → ((p5 → (True ∧ False)) ∧ p3)) → (((True → p3) → (p1 ∧ p4)) ∧ p5))) → ((p5 ∨ False) → (False ∨ p3))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_154205801488309121507515466884 : ((((((p1 ∧ True) → ((p5 ∧ p4) ∨ False)) ∧ ((p4 ∨ p2) ∧ p4)) ∧ (False → (False ∧ p3))) ∨ True) ∧ ((p5 ∧ False) → ((p1 ∧ p2) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657631307506436771552380188762 : (((((True ∨ p3) → (p1 ∨ ((((p3 ∧ (p3 ∨ (False ∧ p1))) ∧ p1) ∨ p2) ∨ ((False → ((True ∧ p4) → False)) → True)))) ∨ (p3 → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114065035393559661449056473942 : (((((True ∨ True) ∨ ((p4 → True) ∧ (p2 ∨ p1))) ∧ ((p3 → ((p4 → p4) ∧ (p1 → p4))) → p2)) ∨ (False → (p5 ∨ p1))) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158353167609202748516677422345 : (((True ∨ p1) ∧ ((False → False) → ((p1 ∨ ((((p1 ∨ p5) → p1) → p2) ∧ p3)) ∨ (p1 ∧ True)))) ∨ ((((p1 ∧ p1) → False) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42191423613987149403432254920 : (((True ∧ (((p2 → (p5 ∧ (p5 → p4))) ∨ (p4 ∧ p4)) ∨ (((p1 → ((p5 → (p3 ∧ p3)) → (p4 → False))) ∧ p3) ∧ True))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230929377569253061916823288575 : (((p3 ∧ p1) ∨ p3) → (p3 ∧ (((p4 ∧ p2) ∨ (((((p4 ∧ p4) → False) → False) ∨ ((p5 → p4) ∧ p5)) ∨ True)) ∨ ((p5 → False) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66249271337535408027602256504 : ((p5 ∨ (((p3 ∧ (p5 → False)) ∨ p2) ∧ ((((((False ∨ (p3 ∨ (p4 → p2))) → True) → p3) ∧ p4) → ((p5 → p3) ∧ p1)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214422390614687769413040770720 : (((p2 → (p4 → p1)) → p1) ∨ (p4 ∨ (p5 ∨ ((p1 → True) ∧ ((p2 ∨ (p4 ∨ (((p2 ∨ (p3 → p2)) ∨ p3) ∨ (p2 ∨ True)))) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141125953043417527643660071348 : (((p3 → ((p3 ∨ ((False → p4) → p2)) ∧ False)) → ((False → ((p3 ∧ p3) ∨ (p2 ∨ False))) ∨ (p2 → (p3 ∧ False)))) → (p2 → (p2 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738892871641167978316269227022 : ((((p3 ∧ False) ∨ ((((((p1 ∧ (((p2 ∧ True) ∧ (p3 ∨ (p3 → True))) ∨ ((p4 ∧ p4) → p2))) ∧ p2) → p5) ∧ p2) ∨ p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192631823584590288077818851089 : ((((((p1 ∧ p3) ∧ (p2 ∧ p2)) ∨ p5) ∨ False) → False) → (p5 → ((p5 → ((p5 → p3) ∨ p2)) ∨ ((((p3 → p3) → True) ∨ p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41755753047643797869525763192 : ((((((True → p3) ∨ p2) → p3) ∨ (p3 → ((p5 ∨ ((True ∧ (p5 → False)) ∨ ((False → p3) → ((p5 → True) ∧ p5)))) → p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54958393492322149412213147027 : ((((p1 ∧ (True → p4)) ∨ (p1 ∧ p2)) ∧ (((((p2 ∨ (False ∨ p4)) ∨ (True → p2)) ∨ p4) → (p1 → p2)) → (p4 → (p4 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252067768485299225486656296945 : ((p4 → p1) ∨ (p2 ∨ ((p2 → ((((True ∧ (p2 → p2)) ∨ (True → ((False ∨ p1) → p2))) → False) ∧ ((p4 → p5) ∨ p3))) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_356688681763506014567484700392 : (p5 → (((p5 → (p4 ∧ (p1 ∧ p5))) → p1) ∧ (((p1 → (p3 ∨ ((((True → p4) ∧ p3) → (True ∧ False)) ∨ (p4 ∧ p2)))) ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149783376494364974689179511799 : ((False ∨ ((((p4 ∧ False) → ((p2 ∧ (p1 ∧ p2)) → (p2 ∨ (p4 → p1)))) → p4) ∨ ((p4 ∨ p3) → p1))) ∨ (False → (p1 ∨ (p3 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113433258537660365145258758927 : ((((((((p2 → p3) ∧ ((p4 ∧ p3) → ((p4 ∨ ((p2 ∧ p4) ∨ p5)) → p1))) ∧ p3) ∨ p2) → p1) ∨ p1) ∨ (p2 → p2)) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166505361773750572026247305988 : ((p4 ∨ (((False → False) → (p1 ∧ (p1 ∨ (((True ∧ (p5 → p5)) ∧ p5) → True)))) ∧ p1)) ∨ (((p2 → (p1 → (p1 → False))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111641370205444470236975221754 : ((((((p3 → p2) ∧ (p1 → (p4 ∧ p1))) ∨ (False ∨ ((((p2 → (p2 ∧ p5)) ∨ p3) ∨ (p5 → True)) ∧ False))) ∨ p1) ∨ True) ∨ (False → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319157666046411607618179867812 : (p4 ∨ ((((((((p2 → False) → (((False → p3) ∧ p4) ∧ p4)) ∨ p3) → p5) ∧ p2) ∨ p1) ∨ p2) ∨ ((((True ∧ p2) → p4) ∧ p2) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616124406386887279382987250184 : (((((((((p1 ∧ (p4 ∨ p3)) → p2) → p4) ∧ (p3 ∨ p3)) → True) ∧ ((((p5 ∧ ((p2 ∨ p5) ∨ p2)) → p3) ∧ p3) ∨ True)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157698897939604742123858502940 : ((((((False → p3) ∨ (((False → p5) ∨ p4) ∧ p1)) → (p1 ∨ False)) ∨ p4) → ((True → p3) ∧ False)) ∨ (p4 → ((p2 → p3) → (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148635693597642566200491796095 : (((p3 → (p1 ∨ (((False → (p5 → True)) ∧ False) ∧ p5))) → (p2 → ((p1 → ((p5 ∧ p4) ∨ p1)) → False))) ∨ (((False ∧ p4) ∧ p1) → p2)) := by
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
theorem thm_5_vars_776227781810943813632607147570 : (((p1 ∨ (((p4 ∨ (((False → (p5 → p3)) → (((p2 ∨ p4) → True) ∧ p5)) ∧ p4)) ∧ ((((True → False) ∨ p3) → True) → True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133623117731520706642782014278 : (((((p1 ∨ (p5 → p2)) ∧ ((((((p5 → p3) ∧ p1) ∧ p1) ∧ False) ∨ (p5 → False)) ∧ (p4 → p2))) → p5) ∧ p3) ∨ ((p5 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301625191013079378654391227582 : (False ∨ ((p4 ∧ (p4 ∨ True)) → (False ∨ (((p2 ∨ (p5 ∧ (p5 → (p4 ∧ p2)))) → (((p5 → True) → p3) → False)) → (p5 ∨ (p4 ∨ p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25546279831145132707718746207 : (((p4 ∨ (p4 ∨ p3)) → ((((False → p2) ∧ p2) ∧ ((False ∧ ((p1 → (p3 → (False → ((p1 → p5) ∧ p5)))) ∧ p1)) ∨ p2)) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52561717112672803800813446514 : ((((p3 → (p3 ∨ ((((False ∧ (p3 → p4)) ∨ p1) ∨ True) → p4))) → p2) ∨ ((p2 → p1) → ((p1 ∧ p4) → (True ∧ (p4 ∨ p3))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173217445520520368191980176125 : ((p5 ∨ (p3 ∧ ((p4 ∨ (p3 ∨ (p4 → (True ∧ p4)))) → ((p5 ∨ p4) ∧ True)))) ∨ (((p5 ∨ p4) → (((True → p5) ∧ p5) ∨ p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45132235070133036475367871904 : ((((p2 → True) → ((p5 ∨ p3) ∧ (((p3 ∨ (True → (False → ((True ∧ (p1 ∨ True)) → (False ∧ True))))) ∨ (p2 → p4)) ∧ p2))) → p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113124109315488135304362351196 : (((p1 → (((p2 → (False → (True → True))) ∧ (p1 → ((p2 → p1) → ((p4 ∧ True) → (p5 → p5))))) ∨ (False ∧ p2))) → p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732393079213157736531644518640 : ((((False ∧ p2) ∧ (p3 ∨ (p4 → (((((p2 ∨ True) ∨ (p4 ∧ True)) ∨ (p2 ∨ ((p3 ∨ (p4 ∨ (p4 → p3))) → True))) → p3) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



