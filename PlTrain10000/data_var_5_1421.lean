variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60895589069954380693639789478 : ((True ∧ (p4 → ((((((p5 ∨ (p3 ∨ (((False ∧ p3) → p2) ∧ (True → p3)))) → p5) ∨ (p5 → False)) ∨ p3) ∨ p2) ∨ (True → p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114523336098383539955976196715 : (((p4 ∧ (False → ((((p4 ∧ (p1 ∨ (p3 ∨ False))) → p3) ∨ ((p3 → True) ∧ p3)) ∧ p4))) → ((p1 → p5) ∨ (p1 ∨ p2))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264220998488756137731711650323 : (True ∧ ((((p2 ∧ p3) ∨ (p3 → False)) ∨ True) ∧ (((p2 ∧ (((p1 → (p2 ∨ p4)) ∧ True) → (False ∨ (False ∧ (False ∨ False))))) ∨ True) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319872896138045424077773990995 : (p4 ∨ (((False ∨ p2) ∨ (p4 ∧ False)) ∨ ((p3 ∨ ((p3 → (p3 → ((((p5 → p1) ∨ p2) → p2) ∨ (p1 ∨ p3)))) ∨ False)) → (p5 → True)))) := by
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
theorem thm_5_vars_357442663514569485437973827263 : (p5 → ((True → p1) → (((p1 → (False ∧ p4)) ∨ (((True → True) ∧ ((((p4 → p2) ∨ ((True ∨ p2) ∨ p3)) → False) ∨ p4)) → False)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228195488621199680900404485557 : ((p5 ∧ (p5 ∧ p2)) ∨ (((((p3 → False) ∨ (p2 ∧ False)) ∨ p4) ∨ ((p2 ∧ p4) → p2)) ∧ (p2 → ((False ∧ p2) → ((p1 → p2) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791922670174996230435275312546 : (((True → (((p5 ∨ (p2 ∧ (((True ∧ (False ∨ (False ∨ p3))) → True) → p3))) ∧ (True → (((False ∧ p4) ∨ False) ∨ p5))) ∨ (p1 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184479865499115806314950023141 : (((((((False ∨ p4) ∧ p5) → p1) ∧ True) → False) ∨ (p4 ∨ p2)) ∨ (False → (False → (((p1 ∧ p3) ∧ (((p2 ∨ False) ∨ p1) → False)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341669887079594341037912328555 : (p2 → ((((p2 → (((p1 ∨ p5) ∨ (((p1 → True) ∨ ((p1 ∨ (True ∧ p3)) ∧ False)) → True)) → (False ∧ True))) ∨ True) ∨ p4) ∨ (p2 ∧ p4))) := by
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
theorem thm_5_vars_66660065894107131385878011941 : ((True → (((p3 ∨ ((p1 → (False → p4)) ∨ True)) ∨ p5) → (((p2 ∧ ((((False ∧ True) ∧ False) ∧ True) ∨ p4)) ∨ False) ∨ (p4 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58984827161004799141789587539 : (((p3 ∧ True) ∨ ((((False → ((p5 ∧ ((p2 → p1) ∨ (p2 → (False → ((p4 → True) ∨ (p2 ∨ False)))))) → p5)) → p3) ∨ p3) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669055032905749283094873661320 : (((((((False ∨ (p4 ∧ (((p4 ∨ False) → p4) ∧ ((p4 → p1) ∧ p4)))) ∨ (p2 → (False ∧ p4))) → p2) → p5) ∨ (p3 ∨ (True ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41455008212687043423138411715 : (((((False → (p4 ∨ (p1 ∧ ((p3 → p4) ∨ True)))) → (p1 ∧ p1)) ∧ (p4 ∧ (p5 → (p2 ∧ (p4 ∨ ((p5 ∨ True) ∨ p1)))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310296246051279145846367379636 : (p2 ∨ (((p3 ∧ (p4 → (((False ∧ p4) ∧ False) → True))) → p2) ∨ ((p4 ∧ (p4 → False)) → ((True ∧ (p4 ∨ p2)) ∨ (p4 ∨ (p5 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190049492693711378325153981570 : ((((p4 ∧ ((p4 ∨ p2) ∨ (p3 ∨ True))) ∨ p4) ∧ True) ∨ ((False → p4) ∨ ((p2 ∨ ((p5 ∨ ((p4 ∨ False) → (p5 → p3))) ∨ p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802693427329882131999317141857 : (((p2 → (p1 → ((p4 ∨ (((p5 → ((True → ((p3 ∨ p1) ∨ (p5 → p2))) ∨ p5)) ∧ p5) ∨ ((p4 ∨ p2) → (p4 ∧ p3)))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61270742587612757126237482249 : ((False ∧ (p2 ∨ ((p1 → ((((p4 ∨ p3) ∧ True) ∨ p3) → (p3 ∨ ((p1 → p2) ∧ (p3 → p4))))) ∨ (p2 ∨ ((p4 ∧ p4) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724973933789720121355633041600 : ((((True → (False ∨ True)) ∧ (((p4 ∧ (p1 ∨ p3)) ∨ (p5 ∧ p1)) ∨ (p3 → ((p1 ∨ p4) → (((p3 ∨ (False ∧ True)) ∨ p3) ∨ p2))))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204843537826105056429185457476 : (((((False ∧ p5) ∧ p3) → p2) → p3) ∨ (False → ((p1 ∨ p2) ∨ (p3 ∨ (((((p1 ∨ (p3 → False)) ∨ p3) ∨ (False → p5)) ∨ p3) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588596139149095914221121219448 : ((((((p3 → p2) → (((False ∨ (True ∧ (p1 ∧ p2))) ∧ (((p4 ∨ ((p2 ∨ False) ∧ False)) ∧ (p1 → p5)) → p4)) ∧ p1)) ∨ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206698057093904600380654759800 : ((p2 → (p1 ∨ ((False ∧ True) ∨ p5))) ∨ (p4 ∨ ((True → (p3 ∨ p1)) ∨ ((p2 ∨ (p1 ∨ (p2 ∧ (((p1 ∧ True) ∧ p5) ∨ True)))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658628683110048449148451957569 : ((((p3 ∨ ((False ∨ p1) ∨ (((p1 ∧ (True → (((p2 ∨ ((p5 ∧ True) ∧ p1)) ∨ (p1 → p4)) ∧ p3))) ∨ p3) → p1))) ∨ (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693710335313704005159140934852 : (((((False ∧ ((((p1 ∧ (p3 ∧ p4)) ∨ False) ∧ (p2 → False)) ∨ p4)) ∨ p4) ∨ ((p5 ∧ ((p3 → False) ∨ ((False → p2) ∨ p1))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57858516183515170985660228997 : (((False ∨ (p2 ∧ True)) → ((((p4 ∧ ((True ∧ (((True → p2) → (p4 ∨ p5)) ∧ p1)) → (p3 → True))) ∨ p3) ∨ p5) → (p5 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61291243915782466029569819274 : ((False ∧ (True → ((p2 ∧ ((p3 ∧ ((p1 → (p4 ∨ p5)) ∨ p4)) ∧ (((p2 ∨ p4) → p4) ∨ (p3 ∧ ((p2 → p2) ∨ p5))))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68315046986531132708214415702 : ((p3 → ((p4 → (p4 ∨ ((False → (False → (p4 ∨ p1))) → ((p5 ∧ ((True → p1) → True)) → p1)))) → ((p3 → (p1 → p1)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732479404002534636361614301125 : ((((False ∧ p5) ∧ ((p3 ∧ (((p3 ∧ p2) ∧ p3) → ((((p2 ∨ p4) ∧ (((p5 ∨ p2) → (p5 → True)) → p5)) → p3) → p5))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205218690924492219402255454032 : ((((p3 ∧ p5) ∧ p5) ∨ (p5 ∧ False)) ∨ (((False ∨ (False ∨ (p5 ∨ (p2 ∨ (True ∨ (p5 ∧ p2)))))) ∨ (p4 ∧ (p1 → True))) ∨ (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_799170239344327429141464099366 : (((p1 → (p1 ∧ ((p3 ∨ (((p4 ∨ p1) → p3) ∧ ((((False → False) → p2) ∨ (p4 ∨ ((p2 → (p2 ∧ p5)) ∨ p5))) ∨ False))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41925581818303133276071851589 : ((((True ∨ (True → p4)) → ((True ∨ p5) → (False ∧ ((p4 ∧ p2) ∨ (((((False ∧ p5) ∧ False) ∧ (p1 ∧ False)) → p4) ∧ p5))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150359333054897541660763395719 : ((p5 → (True ∧ ((p2 ∧ (p5 ∧ ((((False ∧ ((False ∧ p4) ∨ False)) ∧ p2) → p5) → (p2 ∧ p2)))) ∨ True))) ∨ (False → ((p3 ∧ p1) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186661642643898390844685553153 : ((((p1 → (False ∧ (p2 ∧ p1))) → p4) ∧ (True ∧ (p2 ∨ p1))) → ((False ∨ True) ∧ ((((p5 → False) ∧ (p5 ∨ False)) ∨ (p2 ∧ False)) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h18 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h19 := h10 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h21 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h22 := h10 h21
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806488594847978178972607797704 : (((p4 → (((True → ((p3 ∨ (((p4 ∧ p5) ∧ (p2 ∧ p1)) ∧ ((p1 → (False → ((True ∨ p2) ∧ p1))) ∨ p2))) ∨ True)) → p2) → p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → ((p3 ∨ (((p4 ∧ p5) ∧ (p2 ∧ p1)) ∧ ((p1 → (False → ((True ∨ p2) ∧ p1))) ∨ p2))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44909745084420036734678560040 : ((((False → (p1 → p5)) → (((False ∧ False) ∨ (p1 ∨ ((p4 → (p3 → (p1 ∨ (p4 ∧ p1)))) ∧ ((p3 ∨ False) → p4)))) → p1)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623537842046024967314318942338 : ((((False ∨ (((p5 ∨ p5) → False) → ((p1 → p2) ∨ ((p2 ∨ ((p1 ∧ p5) ∧ (p4 ∨ ((p3 ∧ p1) ∧ (True ∧ p3))))) ∧ p4)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148338305283865698193445527763 : ((((((p2 → True) ∧ (p4 ∨ p3)) ∧ (p3 → (False ∨ p1))) ∨ (p1 ∧ p1)) ∧ (p4 ∧ (p3 ∧ (True ∧ True)))) ∨ (False ∨ ((p5 ∧ p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_117472577456923370876712051111 : ((p1 ∧ (p4 ∧ ((((p1 → p3) → (p2 ∨ (p4 ∧ ((p2 ∧ p5) → (p1 → (p3 ∨ (p3 ∧ p5))))))) ∨ (p2 → p4)) ∨ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196188500976863725195484633153 : ((False ∨ (False ∨ ((p2 ∨ p5) → (False → p2)))) ∧ (p5 → ((p5 → p5) → (((p4 ∨ p3) ∨ (((p3 ∧ p1) → (True ∧ False)) ∨ p5)) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68611294946276361972424751592 : ((p4 → ((((False → ((((p1 → p5) ∨ True) ∨ (((p4 ∨ p4) ∨ p5) ∨ (p5 ∨ True))) ∧ True)) → p1) ∨ ((p4 ∨ p4) ∧ p5)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310113719874907097994240506986 : (p2 ∨ (((((p3 ∨ p5) ∨ (p4 ∨ ((p4 ∨ p3) → False))) ∧ (p4 ∨ p2)) ∨ p1) ∨ ((((p5 → False) ∨ p5) ∨ p1) → ((True ∨ False) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673551321600576384710577516187 : ((((((p5 → p1) → p5) ∧ (((((False ∨ (True ∨ (True ∨ p1))) → p4) ∧ True) → True) → (p2 ∧ (True → p3)))) → (p2 ∧ (p5 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765360429779048937878713972646 : (((p4 ∧ (((((False ∨ p5) ∨ (((True ∧ False) ∨ p1) ∧ p2)) ∧ ((p4 → False) → (p2 → p4))) ∧ (True → p1)) → ((p2 ∧ p1) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216356286143517463782350086995 : ((p3 → ((False ∨ False) ∨ p1)) ∨ ((p5 → ((((p1 ∧ (p1 ∧ ((p3 ∧ False) → (((p1 ∧ p2) ∧ p1) ∨ p3)))) ∧ p1) ∧ p1) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172260706225278897085908743517 : (((((True → False) → ((p3 ∨ p3) ∧ p3)) ∧ False) ∨ (p2 ∨ ((False → p3) ∧ p3))) ∨ ((p2 ∧ p3) ∨ (True ∨ (p2 ∨ (p2 ∧ (p2 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64938008185705805221291720661 : ((p2 ∨ (((((p1 ∧ (p5 ∧ p3)) ∧ ((p3 → p1) ∧ p1)) → p4) ∨ False) ∨ ((p1 → ((((p3 ∨ p1) ∧ p4) → p3) ∧ False)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112864698923450541643815011231 : ((((False → (p2 ∨ p4)) ∨ (((((p1 → (p1 ∧ p5)) → False) → (p4 ∨ p2)) ∧ (p3 ∨ p5)) ∨ (False → (p5 ∨ False)))) → False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245800811262366226591463759251 : ((p3 ∧ p3) ∨ ((p1 → p1) ∧ ((p2 → ((False → p5) → (((p3 → p3) ∧ ((((p5 ∨ (p1 ∧ p5)) → p3) ∧ p5) ∨ False)) ∧ p4))) ∨ True))) := by
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
theorem thm_5_vars_118596072836787456303650977427 : ((p4 ∨ ((p2 ∨ (((True ∨ (p3 ∧ p4)) → (False ∧ ((p3 ∧ p4) ∨ p2))) → (p4 ∨ ((p1 → p1) → p1)))) ∧ (p2 ∨ p2))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694417638587971301354908859064 : (((((p1 ∨ False) ∨ (True ∧ ((False ∨ p3) ∨ ((p2 ∨ False) → (p5 ∨ True))))) ∨ ((p4 ∧ (True ∧ p3)) ∨ ((p2 → (p4 ∧ p2)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788383173422706885600191642342 : (((p5 ∨ (((((p4 ∨ (p5 ∧ (p5 ∧ (((True ∨ p3) ∧ p3) ∨ (p2 ∧ (p5 ∧ p2)))))) ∨ False) ∨ True) ∧ ((p5 ∧ p2) → p5)) ∨ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319499059144136439328674530657 : (p4 ∨ ((p2 ∨ (((True ∧ p3) ∧ ((p2 ∧ p3) ∧ p2)) → (p3 ∧ p1))) → (((p1 ∨ True) ∨ p5) ∨ ((p5 ∧ True) ∧ (p5 ∨ (p1 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56064045968660328457900422307 : (((((True → True) → p4) → False) ∨ (((p5 ∨ ((p4 ∨ (p1 ∧ p2)) → (p5 ∨ True))) ∨ ((((True ∧ p1) ∧ p1) → p2) ∧ False)) ∨ False)) ∨ p2) := by
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
theorem thm_5_vars_810237618028574803998965392813 : (((p5 → ((p2 ∨ ((True → ((p4 ∨ ((p2 ∨ (p4 → p3)) → p1)) ∧ p2)) ∧ p1)) ∨ (True → (p5 ∨ (p3 ∨ (p1 ∧ (False ∨ p3))))))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232170916482671128093233181061 : (((True → p5) → p2) → ((((p2 ∨ p2) ∧ (True → False)) → (((p3 → p3) → p4) ∨ (p4 → (p2 ∨ ((p4 ∧ p2) ∨ p5))))) ∨ (p2 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152644427237944940008404228776 : (((p5 ∨ p4) ∧ (True → ((((p1 ∧ True) → (p4 → p5)) ∧ ((p3 → p4) ∨ p2)) ∧ ((p1 ∧ p3) ∧ p5)))) → ((p3 ∨ (p1 ∨ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147474133478845558246261341437 : (((p1 ∧ (p1 ∨ ((False ∨ (p1 ∧ ((p2 → (((p2 ∧ p3) ∨ False) → p5)) → (p3 ∧ p4)))) ∨ True))) ∨ False) ∨ ((p4 → (True ∨ p2)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619676318983312781004156128066 : (((((p4 ∧ p1) ∧ ((p3 ∧ (((((p3 ∨ (p1 → (True ∨ p4))) ∧ p5) → p4) → ((p4 → p4) → p4)) ∧ p1)) ∨ (p5 ∧ p2))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_210525516105965632518449279007 : ((((False ∧ True) ∧ False) → p3) ∧ (p1 → ((p4 ∧ ((True → p1) ∧ (((p2 ∨ True) → (p3 ∧ p4)) → (((p4 ∧ True) ∨ False) ∧ p1)))) ∨ True))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152597990556371538913605739906 : (((p2 ∧ p1) ∧ (p2 ∨ (((p4 → p5) ∧ (True → p1)) ∨ (p4 → ((p1 → p5) → ((False ∨ True) → False)))))) → (p5 ∨ (False ∨ (True ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57069391242062239750293529491 : (((p5 → (p3 ∨ p2)) ∧ (((False ∧ p1) ∧ (False ∧ ((p1 → (((True ∨ p4) ∨ (p2 → (p2 ∨ p4))) ∧ (True ∧ p3))) → p2))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244018365857600116267762260399 : ((True ∧ p2) ∨ (((((False → ((p5 ∨ (p1 ∨ p2)) ∧ (p2 → True))) ∨ p3) → ((False → p5) ∧ False)) → ((p4 ∨ p5) → False)) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345624962001844201332682198144 : (p3 → ((False ∧ (((p1 ∧ (False ∨ (((p1 ∨ (p1 → False)) ∨ (((False → p1) → True) ∧ p4)) → False))) ∨ ((p3 ∨ p1) ∨ p2)) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613988262199590853263199285838 : (((((((p4 ∨ ((p5 → p1) → p2)) → p4) ∨ (((p4 → (True → p3)) → False) → ((p1 → False) ∨ False))) ∨ (p3 → (p5 → p3))) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678237618718043688181436325550 : ((((((False ∧ (((False ∧ (True ∨ p2)) ∨ p5) ∨ True)) → False) → ((True ∨ (p1 ∨ (p3 → p4))) → p2)) ∨ (((p3 ∨ True) → True) ∨ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_119412101486420938617793425516 : ((p4 → (((((True ∧ ((True ∨ p5) ∧ (p5 ∧ ((p4 → (p3 ∧ (p5 ∧ p1))) → p4)))) ∨ False) ∧ p1) ∧ (False → p4)) → p3)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191727370693253168106630275382 : ((False ∨ (((False ∨ (p2 ∨ p1)) ∧ (p1 ∨ p5)) ∧ p5)) ∨ (False → ((False → ((((p3 → False) ∧ True) ∨ True) ∨ (p4 ∨ p3))) ∨ (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587885325425324770183887876420 : ((((((((p3 ∨ p2) ∨ p1) ∧ (p2 ∧ (((p3 → p4) ∨ True) ∧ (True → ((p1 ∧ p2) ∧ (p5 ∧ p4)))))) → (p3 → p5)) ∨ p1) ∧ True) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h13 := h10 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h18 := h10 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h4.left
      let h23 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h28 := h25 h27
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h33 := h25 h32
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- We need to get the left conjuct of h34 based on <expert-advice>.
        let h35 := h34.left
        -- One of the premise coincides with the conclusion.
        exact h35
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h4.left
    let h38 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h41 =>
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h42 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h43 := h40 h42
      -- We need to get the right conjuct of h43 based on <expert-advice>.
      let h44 := h43.right
      -- We need to get the left conjuct of h44 based on <expert-advice>.
      let h45 := h44.left
      -- One of the premise coincides with the conclusion.
      exact h45
    case inr h46 =>
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h47 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h48 := h40 h47
      -- We need to get the right conjuct of h48 based on <expert-advice>.
      let h49 := h48.right
      -- We need to get the left conjuct of h49 based on <expert-advice>.
      let h50 := h49.left
      -- One of the premise coincides with the conclusion.
      exact h50
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264401485458205505890759929340 : (True ∧ ((True ∧ ((p3 ∧ p4) ∨ p2)) ∨ (((((((False ∨ (False → p5)) ∧ True) ∧ p1) ∧ (p4 ∧ p1)) → p2) ∧ p3) ∨ (False → (p3 ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_136270578204185876217755477503 : (((((p2 ∨ p5) ∨ (p3 ∨ False)) → p5) → ((((p5 → (True ∧ ((p4 ∨ p1) ∨ (p2 ∧ p2)))) → p1) ∨ True) ∧ False)) ∨ ((p2 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37896799537020245366593369440 : ((((((p5 → ((p5 → p1) ∨ (p4 ∧ ((((p4 → True) ∨ (p2 ∧ p3)) ∨ True) ∨ False)))) ∨ p3) ∨ (p4 → False)) ∧ (p3 ∨ p2)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345487183517792935421150415463 : (p3 → ((((((p4 → True) → (p2 ∨ (False ∨ (p5 ∧ ((p1 ∨ p3) ∧ p4))))) ∨ p5) ∧ (p5 → p1)) ∨ (((p5 ∧ p1) ∨ p3) ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44870571000577468008305567999 : ((((p5 → (False ∧ p2)) ∨ (p2 ∧ (((p4 → (p3 ∨ True)) → (p5 → ((False ∨ (True → False)) → (False ∨ (p4 ∨ True))))) → p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259490780642933351168263798674 : ((False → p5) → ((p3 → (((p3 ∨ (p4 ∨ False)) ∧ (p1 ∨ ((True ∨ True) ∧ (((p4 ∨ (p5 → p2)) ∧ p4) ∨ p3)))) ∧ (p2 ∨ p3))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322224837376925307883110012324 : (p5 ∨ (((True ∧ ((p2 → (False → (p2 ∧ (p2 → (((False ∧ p3) ∧ p1) ∧ (((p2 ∧ p2) ∨ p4) ∨ (p5 ∧ True))))))) → False)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646830907610156786830560021740 : ((((p2 → ((p5 ∧ ((p5 ∨ True) ∧ p4)) ∧ ((((True ∨ p2) ∨ (((True ∨ p3) ∧ p2) ∨ p5)) → (p1 ∨ (False → p5))) ∨ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118388913609787048251622233135 : ((p2 ∨ ((((p2 ∨ p2) ∨ p2) ∧ (True → p4)) ∨ ((((((p4 → (p2 ∨ (p1 ∨ False))) → p5) ∧ p5) → p4) → True) ∧ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345317346908939947471839603927 : (p3 → ((((((p3 ∧ (p4 ∧ p4)) ∧ p1) ∨ (((True ∨ (p2 → p3)) → (p2 ∧ p3)) → (p5 ∨ (p2 ∨ (p1 → p3))))) ∨ p2) ∧ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51447115919509803483630189718 : (((((p4 ∨ p5) → (((p3 ∧ p5) → ((p3 ∨ p2) ∧ False)) ∧ True)) ∧ ((True → p3) → p1)) → (((p2 → p1) ∨ p4) → (p3 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345162869844201878813121243953 : (p3 → (((p3 ∧ p3) ∧ ((p3 → (((((p4 ∧ (p2 → p4)) ∧ p5) ∨ (p2 ∨ p2)) ∨ p5) → True)) → ((p2 → p1) ∨ (p4 ∨ True)))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68454008063947642702719783077 : ((p3 → (p1 ∧ ((False ∨ False) ∨ (p3 → ((p5 ∨ p3) → (p1 ∨ (((p3 → (p4 ∧ (p4 → ((p2 → p5) ∧ p4)))) → p2) ∧ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149598144241037029273669449478 : ((p3 ∧ (((p5 → (p5 ∨ p3)) → (((p5 → (p3 ∨ p5)) ∨ p3) → True)) ∧ ((False ∧ p1) ∧ (p2 ∧ p3)))) ∨ ((p4 → (p3 → p4)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160325190903416329849397449513 : ((((p2 ∨ p4) ∨ (p5 ∨ (p4 ∧ (((p4 ∧ p4) ∨ (p4 ∨ (p2 ∧ p4))) ∨ True)))) → (p3 ∧ p5)) → (True → (p3 → (p4 ∨ (True → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198888956285886342571196447606 : ((p3 → ((((p2 ∨ p5) → p2) → False) ∧ p5)) ∨ ((p5 ∧ p1) → (p1 ∨ ((False ∧ (False ∧ p1)) → ((p4 ∨ (p5 ∨ p4)) ∨ (True ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61449782827096220188173181899 : ((p1 ∧ ((((False ∧ (False ∨ (((p4 → ((p5 ∨ p5) → p2)) ∨ False) ∧ p1))) ∨ (False ∨ ((p5 → p2) ∧ p3))) ∨ p3) ∧ (p5 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180337750904484957334941339600 : (((False ∨ ((p1 ∧ (p4 ∧ False)) ∨ (p3 ∨ (p2 → p2)))) ∧ (True → p1)) → ((((p1 ∧ p2) ∨ p4) ∧ ((p1 → (p3 → p3)) ∨ p3)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789957889032382325263784370994 : (((p5 ∨ ((False ∨ p3) ∧ (True → ((((((p3 ∧ ((p1 ∨ ((p3 → p4) → p2)) ∨ p3)) ∧ p3) → True) ∧ p3) ∧ p4) ∧ (p3 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148358015316239494388268282669 : (((p1 ∨ (p4 ∧ (p1 ∨ ((p1 ∨ (p2 → ((p2 ∧ p3) → p1))) ∧ p4)))) ∧ (p5 ∨ ((p4 ∧ p1) ∧ True))) ∨ ((p2 ∨ (p1 → True)) ∨ p3)) := by
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
theorem thm_5_vars_137679660698739193062376185740 : ((p1 ∨ ((((p2 ∨ False) ∧ True) ∧ ((p5 → p5) → (((False → (p3 ∧ p3)) → True) ∨ ((p2 ∧ p2) ∧ p1)))) ∧ p4)) ∨ (p1 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49636667609072285337997363046 : ((((((p5 ∧ p5) ∧ p5) ∨ True) ∧ (p1 → ((p4 → ((p5 ∨ (p4 → (p1 → p5))) ∧ (True ∧ True))) ∨ p3))) → ((p2 → p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65633384087468906095238439835 : ((p4 ∨ ((((p3 → True) ∧ (p4 ∧ ((p4 ∧ False) ∧ (True ∧ (((p5 → True) ∧ (True → (False ∧ p1))) ∨ p2))))) ∨ (p3 ∧ p2)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166377559401209866332173163556 : ((False ∨ (((p4 → (p4 ∧ ((p3 ∨ p1) ∨ ((False ∨ p1) → True)))) ∧ (True ∧ p5)) ∨ p2)) ∨ ((p3 → (p3 ∨ p3)) ∨ ((True ∨ p1) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204146954791389963962492778387 : (((((p4 ∧ False) ∧ False) ∨ False) ∧ p4) ∨ (((p1 ∧ p5) ∨ (p4 ∨ p5)) ∨ ((((p1 ∨ ((p3 ∨ True) ∨ True)) ∨ p2) → (p5 → True)) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328672392540083240513203453567 : (True → (((((p3 ∧ False) → p5) → ((p4 → p3) ∧ False)) ∨ (False → p3)) ∧ (p4 → ((((p4 ∨ (True ∨ p3)) ∨ False) ∨ (p1 ∧ p4)) → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168817562654335780761750226402 : ((p2 ∨ (p2 ∧ ((p2 → True) → ((p3 ∧ (False ∧ (p3 → p1))) ∨ ((p5 ∧ True) ∧ p2))))) → (p1 → ((p3 ∨ ((p5 ∧ False) ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187638941892687088395049686332 : ((p5 ∨ ((p3 ∨ (p4 ∨ True)) ∧ ((p5 ∨ (True ∨ p2)) → False))) → (((p5 → p4) → (((p1 ∨ (p2 ∧ (p1 ∧ p3))) ∧ p4) → p4)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (p5 ∨ (True ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h12 : (p5 ∨ (True ∨ p2)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h13 := h6 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : (p5 ∨ (True ∨ p2)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h16 := h6 h15
        -- False on the left can always be used.
        apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49278923012310454541804937827 : (((p3 ∧ (p3 → (True → (((p4 ∧ p4) ∨ ((p1 ∨ p4) ∧ p5)) ∧ ((((p5 ∧ False) ∨ p3) ∨ p4) ∧ p3))))) ∨ (True ∧ (p2 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190788534964539927583364518666 : ((((p4 ∨ ((True ∨ True) ∧ p2)) → False) ∨ (p2 → p3)) ∨ ((p4 ∨ ((False ∨ p1) ∧ (p4 → True))) → (p3 ∨ ((False → p1) ∨ (True → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248777364232594120807949971741 : ((p3 ∨ p3) ∨ ((p4 ∧ p5) ∨ (True ∧ (p2 ∨ (((((p3 → p3) ∧ p4) ∨ True) ∨ (((p3 ∧ p2) ∨ (p5 ∨ p3)) ∧ True)) ∨ (p5 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798995186451460103008256954867 : (((p1 → ((p2 → p3) ∨ (((p3 ∧ (p1 → p1)) ∧ p1) ∨ (p5 ∨ (((p3 ∨ False) → ((((p1 ∨ False) ∧ True) ∧ p3) ∨ p5)) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325994219091285382483589490901 : (p5 ∨ (True → (((((p3 ∨ p4) ∨ (p3 ∧ (p4 → ((p2 ∨ ((False → p4) ∨ p5)) ∧ p2)))) → p1) → p3) ∨ (p2 ∨ ((True ∧ True) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



