/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Security

/-!
# Exhibiting attacks

Lemmas for showing that an explicit trace is an attack on a process and what the
attacker knows after it, so that a query can be refuted by exhibiting a trace.  Nothing
here changes the semantics, which `Process.lean` and `Security.lean` define.

* A trace of a translated body is built one action at a time with `Proc.mem_act`,
  `Proc.mem_inp` and `Proc.mem_new`, and through a parallel composition with
  `Proc.mem_par`, giving the tagged trace, or its special cases: one side idle
  (`Proc.mem_par_left`, `Proc.mem_par_right`), one side running after the other with a
  message handed over (`Proc.mem_par_seq`), and one copy of a replication (`Proc.mem_bang`).
  An idle component has the empty trace, `Cont.Nil`, which `aesop` proves of a body by
  the same rules as `Cont.Tree`.
* The attacker takes up every offer of the protocol: for a trace `u` of the protocol,
  `u.dual` is the attacker's trace and `u.complete` the attack (`Proc.mem_attacks`).
* After an attack the attacker knows everything derivable from the messages
  communicated on channels it knows from the start
  (`Fact.holds_knows_of_derive`), and it derives by the public constructors
  (`Attacker.app_mem_derive`, in `Security.lean`) and destructors
  (`Attacker.dtor_mem_derive`).
-/

namespace ProVerif.TraceSemantics

open Descriptive

variable {M ι : Type}

/-! ## Tagged traces -/

namespace TaggedTrace

/-- A trace tagged throughout with one component has no communications. -/
theorem Comms.tag (i : ι) (t : Trace M) : Comms (t.map (i, ·)) t := by
  induction t with
  | nil => exact .nil
  | cons a t ih => exact ih.cons i a

/-- One component runs alone before the rest. -/
theorem Comms.tag_append (i : ι) (l : Trace M) {s : TaggedTrace ι M} {t : Trace M}
    (h : s.Comms t) : Comms (l.map (i, ·) ++ s) (l ++ t) := by
  induction l with
  | nil => exact h
  | cons a l ih => exact ih.cons i a

variable [DecidableEq ι]

theorem proj_append (s₁ s₂ : TaggedTrace ι M) (i : ι) :
    proj (s₁ ++ s₂) i = proj s₁ i ++ proj s₂ i := by
  simp [proj, List.filter_append]

/-- The components of a trace tagged throughout with `i`. -/
theorem proj_map (i j : ι) (t : Trace M) : proj (t.map (i, ·)) j = if i = j then t else [] := by
  induction t with
  | nil => simp
  | cons a t ih =>
    rcases eq_or_ne i j with rfl | h
    · simp [ih]
    · simp [h, ih]

end TaggedTrace

/-! ## The names created in an explicit trace -/

namespace Trace

@[simp] theorem nonces_nil : nonces ([] : Trace M) = [] := rfl

@[simp] theorem nonces_cons_out (c m : M) (t : Trace M) : nonces (.out c m :: t) = t.nonces := rfl

@[simp] theorem nonces_cons_inp (c m : M) (t : Trace M) : nonces (.inp c m :: t) = t.nonces := rfl

@[simp] theorem nonces_cons_comm (c m : M) (t : Trace M) :
    nonces (.comm c m :: t) = t.nonces := rfl

@[simp] theorem nonces_cons_new (n : ℕ) (t : Trace M) : nonces (.new n :: t) = n :: t.nonces := rfl

@[simp] theorem nonces_cons_event (e : M) (t : Trace M) : nonces (.event e :: t) = t.nonces := rfl

end Trace

/-! ## Traces of processes -/

namespace Proc

theorem nil_mem_nil : [] ∈ (nil : Proc M) := Set.mem_singleton _

theorem nil_mem_act (a : Act M) (P : Proc M) : [] ∈ act a P := Set.mem_insert _ _

theorem nil_mem_inp [Names M] (c : M) (P : M → Proc M) : [] ∈ inp c P :=
  Set.mem_iUnion.2 ⟨Names.nonce 0, nil_mem_act _ _⟩

theorem nil_mem_new [Names M] (P : M → Proc M) : [] ∈ new P :=
  Set.mem_iUnion.2 ⟨0, nil_mem_act _ _⟩

theorem mem_act {a : Act M} {P : Proc M} {t : Trace M} (h : t ∈ P) : a :: t ∈ act a P :=
  Or.inr ⟨t, h, rfl⟩

theorem mem_inp {c m : M} {P : M → Proc M} {t : Trace M} (h : t ∈ P m) :
    .inp c m :: t ∈ inp c P :=
  Set.mem_iUnion.2 ⟨m, mem_act h⟩

theorem mem_new [Names M] {P : M → Proc M} {n : ℕ} {t : Trace M} (h : t ∈ P (Names.nonce n))
    (hn : n ∉ t.nonces) : .new n :: t ∈ new P :=
  Set.mem_iUnion.2 ⟨n, mem_act ⟨h, hn⟩⟩

/-- A trace of `P | Q`, from the tagged trace `s`, whose projections `hl` and `hr` compute
when `s` is explicit. -/
theorem mem_par {P Q : Proc M} {s : TaggedTrace (Fin 2) M} {t l r : Trace M} (hl : s.proj 0 = l)
    (hr : s.proj 1 = r) (hP : l ∈ P) (hQ : r ∈ Q) (hs : s.Comms t) (hn : t.nonces.Nodup) :
    t ∈ P.par Q := by
  subst hl hr
  exact ⟨⟨fun i => s.proj i, s, Fin.forall_fin_two.2 ⟨hP, hQ⟩, fun _ => rfl, hs⟩, hn⟩

/-- A trace of `P` is a trace of `P | Q` when `Q` stays idle. -/
theorem mem_par_left {P Q : Proc M} {t : Trace M} (ht : t ∈ P) (hQ : [] ∈ Q)
    (hn : t.nonces.Nodup) : t ∈ P.par Q :=
  mem_par (s := t.map ((0 : Fin 2), ·)) (by simp [TaggedTrace.proj_map])
    (by simp [TaggedTrace.proj_map]) ht hQ (TaggedTrace.Comms.tag 0 t) hn

/-- A trace of `Q` is a trace of `P | Q` when `P` stays idle. -/
theorem mem_par_right {P Q : Proc M} {t : Trace M} (hP : [] ∈ P) (ht : t ∈ Q)
    (hn : t.nonces.Nodup) : t ∈ P.par Q :=
  mem_par (s := t.map ((1 : Fin 2), ·)) (by simp [TaggedTrace.proj_map])
    (by simp [TaggedTrace.proj_map]) hP ht (TaggedTrace.Comms.tag 1 t) hn

theorem nil_mem_par {P Q : Proc M} (hP : [] ∈ P) (hQ : [] ∈ Q) : [] ∈ P.par Q :=
  mem_par_left hP hQ List.nodup_nil

/-- `P` runs, hands `m` over to `Q` on `c`, and `Q` runs: `t` is `l ++ comm c m :: r`, which
`ht` computes when `t` is explicit. -/
theorem mem_par_seq {P Q : Proc M} {t l r : Trace M} {c m : M} (ht : t = l ++ .comm c m :: r)
    (hP : l ++ [.out c m] ∈ P) (hQ : .inp c m :: r ∈ Q) (hn : t.nonces.Nodup) : t ∈ P.par Q := by
  subst ht
  exact mem_par
    (s := l.map ((0 : Fin 2), ·) ++ (0, .out c m) :: (1, .inp c m) :: r.map ((1 : Fin 2), ·))
    (by simp [TaggedTrace.proj_append, TaggedTrace.proj_map])
    (by simp [TaggedTrace.proj_append, TaggedTrace.proj_map]) hP hQ
    (TaggedTrace.Comms.tag_append 0 l (.pair (by decide) c m (TaggedTrace.Comms.tag 1 r))) hn

/-- A trace of `P` is a trace of `!P`, by one copy. -/
theorem mem_bang {P : Proc M} {t : Trace M} (ht : t ∈ P) (hP : [] ∈ P) (hn : t.nonces.Nodup) :
    t ∈ P.bang :=
  ⟨⟨fun n => if 0 = n then t else [], t.map ((0 : ℕ), ·),
    fun n => by dsimp only; split <;> assumption,
    fun n => TaggedTrace.proj_map 0 n t, TaggedTrace.Comms.tag 0 t⟩, hn⟩

theorem nil_mem_bang {P : Proc M} (hP : [] ∈ P) : [] ∈ P.bang :=
  mem_bang hP hP List.nodup_nil

end Proc

/-- Proves `s.Comms t` for explicit `s` and `t`. -/
macro "comms" : tactic =>
  `(tactic| repeat first
    | exact TaggedTrace.Comms.nil
    | refine TaggedTrace.Comms.pair (by decide) _ _ ?_
    | refine TaggedTrace.Comms.cons _ _ ?_)

/-! ## Idleness of a body

`Cont.Nil b` says that `b` yields a process with the empty trace whenever its
continuation does, which every body does, by the same rules as `Cont.Tree`. -/

/-- `b` yields a process with the empty trace whenever its continuation does. -/
def Cont.Nil {α : Type} (b : Cont (Proc M) α) : Prop :=
  ∀ κ : α → Proc M, (∀ a, [] ∈ κ a) → [] ∈ Id.run (b.run κ)

namespace Cont.Nil

variable {α β : Type}

/-- The process of a body has the empty trace. -/
theorem run {b : Cont (Proc M) Unit} (h : Nil b) : [] ∈ Proc.run b :=
  h _ fun _ => Set.mem_singleton _

@[aesop safe apply] theorem pure (a : α) : Nil (Pure.pure a : Cont (Proc M) α) :=
  fun _ hκ => hκ a

@[aesop safe apply] theorem bind {x : Cont (Proc M) α} {f : α → Cont (Proc M) β}
    (hx : Nil x) (hf : ∀ a, Nil (f a)) : Nil (x >>= f) :=
  fun κ hκ => hx _ fun a => hf a κ hκ

@[aesop safe apply] theorem map {x : Cont (Proc M) α} {f : α → β} (hx : Nil x) :
    Nil (f <$> x) :=
  fun _ hκ => hx _ fun a => hκ (f a)

@[aesop safe apply] theorem letFun {v : β} {f : β → Cont (Proc M) α} (h : Nil (f v)) :
    Nil (letFun v f) :=
  h

@[aesop safe apply] theorem ite {c : Prop} [Decidable c] {x y : Cont (Proc M) α} (hx : Nil x)
    (hy : Nil y) : Nil (if c then x else y) := by
  split
  · exact hx
  · exact hy

@[aesop safe apply] theorem send (c m : M) : Nil (Proc.send c m) :=
  fun _ _ => Set.mem_insert _ _

@[aesop safe apply] theorem recv [Names M] (c : M) : Nil (Proc.recv c) :=
  fun _ _ => Set.mem_iUnion.2 ⟨Names.nonce 0, Set.mem_insert _ _⟩

@[aesop safe apply] theorem fresh [Names M] : Nil (Proc.fresh : Cont (Proc M) M) :=
  fun _ _ => Set.mem_iUnion.2 ⟨0, Set.mem_insert _ _⟩

@[aesop safe apply] theorem emit (e : M) : Nil (Proc.emit e) :=
  fun _ _ => Set.mem_insert _ _

@[aesop safe apply] theorem fork : Nil (Proc.fork : Cont (Proc M) Bool) := fun _ hκ =>
  ⟨⟨![[], []], [], Fin.forall_fin_two.2 ⟨hκ true, hκ false⟩, fun i => by fin_cases i <;> rfl,
    .nil⟩, List.nodup_nil⟩

@[aesop safe apply] theorem repl : Nil (Proc.repl : Cont (Proc M) Unit) := fun _ hκ =>
  ⟨⟨fun _ => [], [], fun _ => hκ (), fun _ => rfl, .nil⟩, List.nodup_nil⟩

@[aesop safe apply] theorem stop : Nil (Proc.stop : Cont (Proc M) α) :=
  fun _ _ => Set.mem_singleton _

@[aesop safe apply] theorem ofOption (o : Option α) : Nil (Proc.ofOption o : Cont (Proc M) α) := by
  intro κ hκ
  cases o with
  | none => exact Set.mem_singleton _
  | some a => exact hκ a

@[aesop safe apply] theorem lift (o : Option α) : Nil (monadLift o : Cont (Proc M) α) :=
  ofOption o

end Cont.Nil

/-! ## The attacker's half of an attack

The attacker takes up every offer: it receives what the protocol sends and sends what
the protocol receives. -/

namespace Trace

/-- The attacker's actions against `u`. -/
def dual : Trace M → Trace M
  | [] => []
  | .out c m :: u => .inp c m :: dual u
  | .inp c m :: u => .out c m :: dual u
  | .comm _ _ :: u => dual u
  | .new _ :: u => dual u
  | .event _ :: u => dual u

/-- `u` with every offer taken up by the attacker. -/
def complete : Trace M → Trace M
  | [] => []
  | .out c m :: u => .comm c m :: complete u
  | .inp c m :: u => .comm c m :: complete u
  | .comm c m :: u => .comm c m :: complete u
  | .new n :: u => .new n :: complete u
  | .event e :: u => .event e :: complete u

/-- The interleaving of `u` and `u.dual`, the protocol tagged `0` and the attacker `1`. -/
def tag : Trace M → TaggedTrace (Fin 2) M
  | [] => []
  | .out c m :: u => (0, .out c m) :: (1, .inp c m) :: tag u
  | .inp c m :: u => (1, .out c m) :: (0, .inp c m) :: tag u
  | .comm c m :: u => (0, .comm c m) :: tag u
  | .new n :: u => (0, .new n) :: tag u
  | .event e :: u => (0, .event e) :: tag u

@[simp] theorem dual_nil : dual ([] : Trace M) = [] := rfl

@[simp] theorem dual_out (c m : M) (u : Trace M) : dual (.out c m :: u) = .inp c m :: dual u := rfl

@[simp] theorem dual_inp (c m : M) (u : Trace M) : dual (.inp c m :: u) = .out c m :: dual u := rfl

@[simp] theorem dual_comm (c m : M) (u : Trace M) : dual (.comm c m :: u) = dual u := rfl

@[simp] theorem dual_new (n : ℕ) (u : Trace M) : dual (.new n :: u) = dual u := rfl

@[simp] theorem dual_event (e : M) (u : Trace M) : dual (.event e :: u) = dual u := rfl

@[simp] theorem complete_nil : complete ([] : Trace M) = [] := rfl

@[simp] theorem complete_out (c m : M) (u : Trace M) :
    complete (.out c m :: u) = .comm c m :: complete u := rfl

@[simp] theorem complete_inp (c m : M) (u : Trace M) :
    complete (.inp c m :: u) = .comm c m :: complete u := rfl

@[simp] theorem complete_comm (c m : M) (u : Trace M) :
    complete (.comm c m :: u) = .comm c m :: complete u := rfl

@[simp] theorem complete_new (n : ℕ) (u : Trace M) :
    complete (.new n :: u) = .new n :: complete u := rfl

@[simp] theorem complete_event (e : M) (u : Trace M) :
    complete (.event e :: u) = .event e :: complete u := rfl

theorem proj_tag_zero (u : Trace M) : u.tag.proj 0 = u := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [tag, ih]

theorem proj_tag_one (u : Trace M) : u.tag.proj 1 = u.dual := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [tag, ih]

theorem comms_tag (u : Trace M) : u.tag.Comms u.complete := by
  induction u with
  | nil => exact .nil
  | cons a u ih =>
    cases a with
    | out c m => exact ih.pair (by decide) c m
    | inp c m => exact ih.pair (by decide) c m
    | comm c m => exact ih.cons 0 _
    | new n => exact ih.cons 0 _
    | event e => exact ih.cons 0 _

theorem nonces_complete (u : Trace M) : u.complete.nonces = u.nonces := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [ih]

theorem closed_complete (u : Trace M) : u.complete.Closed := by
  induction u with
  | nil => simp [Closed]
  | cons a u ih => cases a <;> exact List.forall_mem_cons.2 ⟨nofun, ih⟩

end Trace

/-- An attack: a trace of `P` whose every offer the attacker takes up, the attacker's own
actions being those of `Enemy ∅`. -/
theorem Proc.mem_attacks [Names M] [Attacker M] {P : Proc M} {u : Trace M} (hu : u ∈ P)
    (he : u.dual ∈ Enemy ∅) (hn : u.nonces.Nodup) : u.complete ∈ P.Attacks :=
  ⟨Proc.mem_par (s := u.tag) u.proj_tag_zero u.proj_tag_one hu he u.comms_tag
    (by rw [Trace.nonces_complete]; exact hn), u.closed_complete⟩

/-! ## The attacker's knowledge -/

section knowledge

variable [Attacker M]

open Attacker (derive)

theorem Trace.subset_attackerKnowledge (K : Set M) :
    ∀ t : Trace M, K ⊆ t.attackerKnowledge K
  | [] => le_rfl
  | _ :: t =>
    (Set.subset_union_left.trans (derive.le_closure _)).trans (subset_attackerKnowledge _ t)

theorem Trace.attackerKnowledge_mono {K K' : Set M} (h : K ⊆ K') :
    ∀ t : Trace M, t.attackerKnowledge K ⊆ t.attackerKnowledge K'
  | [] => h
  | _ :: t =>
    attackerKnowledge_mono
      (derive.monotone (Set.union_subset_union h (by rintro m ⟨c, ha, hc⟩; exact ⟨c, ha, h hc⟩))) t

theorem Trace.isClosed_attackerKnowledge {K : Set M} (hK : derive.IsClosed K) :
    ∀ t : Trace M, derive.IsClosed (t.attackerKnowledge K)
  | [] => hK
  | _ :: t => isClosed_attackerKnowledge (derive.isClosed_closure _) t

/-- After `t` the attacker knows everything derivable from the messages communicated on
channels it knows from the start. -/
theorem Trace.derive_comms_subset_attackerKnowledge (t : Trace M) :
    derive {m | ∃ c, Act.comm c m ∈ t ∧ c ∈ derive ∅} ⊆ t.attackerKnowledge (derive ∅) := by
  refine derive.closure_min ?_ (isClosed_attackerKnowledge (derive.isClosed_closure _) t)
  rintro m ⟨c, hm, hc⟩
  induction t with
  | nil => simp at hm
  | cons a t ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · exact subset_attackerKnowledge _ t (derive.le_closure _ (Or.inr ⟨c, rfl, hc⟩))
    · exact attackerKnowledge_mono (Set.subset_union_left.trans (derive.le_closure _)) t (ih hm)

/-- `attacker(m)` holds after `t` when `m` is derivable from the messages communicated on
channels the attacker knows from the start. -/
theorem Fact.holds_knows_of_derive {t : Trace M} {m : M}
    (h : m ∈ derive {m | ∃ c, Act.comm c m ∈ t ∧ c ∈ derive ∅}) : (Fact.knows m).Holds t :=
  t.derive_comms_subset_attackerKnowledge h

/-- A destructor among the attacker's operations, applied to derivable messages on which
it succeeds, yields a derivable message. -/
theorem Attacker.dtor_mem_derive {n : ℕ} {f : (Fin n → M) → Option M}
    (hf : (⟨n, liftFail f⟩ : Σ n, (Fin n → Option M) → Option M) ∈ Attacker.ops)
    {S : Set M} {ms : Fin n → M} (hms : ∀ i, ms i ∈ derive S) {r : M} (h : f ms = some r) :
    r ∈ derive S := by
  have hS : ClosedUnder Attacker.ops (derive S) := derive.isClosed_closure S
  exact hS _ hf (fun i => some (ms i)) (fun i m h => Option.some_injective _ h ▸ hms i) _
    (liftFail_eq_some.2 ⟨ms, fun _ => rfl, h⟩)

end knowledge

/-- A public destructor is among the operations of `Attacker.ofDecls`. -/
theorem Attacker.ofDecls_mem_dtor {F : Sig} {T : Theory F} {pubFun : ∀ n, Set (F n)}
    {pubDtors : Set (Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg)}
    {o : Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg} (h : o ∈ pubDtors) :
    o ∈ (Attacker.ofDecls pubFun pubDtors).ops :=
  Or.inl (Or.inr h)

end ProVerif.TraceSemantics
