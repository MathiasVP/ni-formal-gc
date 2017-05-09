# ni-formal-gc
Coq formalization of timing-sensitive noninterference for a garbage collected language with heap and runtime pc level.

The top-level termination-insensitive non-interference theorem is found in `ni.v`:

```coq
Theorem TINI:
    forall ℓ_adv Γ c m1 m2 m1' m2' h2' h1' t pc1_end pc2_end t1' t2',
      wt Γ bot c ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      initial_memory m1 ->
      initial_memory m2 ->
      memory_low_eq empty_bijection ℓ_adv Γ m1 m2 ->
      ⟨c, bot, m1, emptyHeap, t⟩ ⇒ * ⟨Stop, pc1_end, m1', h1', t1'⟩ ->
      ⟨c, bot, m2, emptyHeap, t⟩ ⇒ * ⟨Stop, pc2_end, m2', h2', t2'⟩ ->
      ∃ ψ s' w',
        ⟨c, bot, m2, emptyHeap, t⟩ ⇒ * ⟨Stop, pc2_end, s', w', t1'⟩
        /\ memory_low_eq ψ ℓ_adv Γ m1' s'.
```

This README provides a guided tour of the contents of the files.

### Language

Our language is almost a standard imperative language augmented with array
operations, a command to obtain the current time and a command to control the
program counter level at runtime.

```
e := n | x | e + e
c ::= skip | x := e | x := new(l, e, e) | x[e] := e | x := y[e] | x := time()
    | c; c | if e then c else c | while e do c | at l with bound e do c
```

### Semantics

Memory and heap are left abstract and specified by mmemory.v. Both memory and
heaps are partially defined. A memory is something which can be used to look up
values given an identifier using `Memory -> id -> option value`.

Likewise, a heap is something which can be used to look up arrays given a
location using `heap_lookup: loc -> Heap -> option (level_proj1 * lookupfunc)`
where `lookupfunc` is an abstract type representing an array, which can be
indexed into using `lookup: lookupfunc -> nat -> option value`.

#### Standard and augmented semantics

A traditional small-step semantics `std_step : config -> config -> Prop` for the
language is presented in `ni.v`, along with an adequacy results
`std_step_implies_step` and `step_implies_std_step`

```coq
Lemma std_step_implies_step:
  ∀ c Γ pc m h t c' pc' m' h' t' Σ pc_end,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
    ⟨c, pc, m, h, t⟩ ⇒ ⟨c', pc', m', h', t'⟩ ->
    ∃ Σ',
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩.

Lemma step_implies_std_step:
  ∀ c Γ pc m h t c' pc' m' h' t' Σ Σ' pc_end,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
    ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    ⟨c, pc, m, h, t⟩ ⇒ ⟨c', pc', m', h', t'⟩.
```

relating the semantics to the augmented semantics found in `mimperative.v` which
augments the standard semantics with type information in the form of a variable
typing environment `Γ: id -> option sectype` and a heap typing environment `Σ:
loc -> option sectype`.

#### Event semantics

We lift the augmented semantics from `mimperative.v` to event semantics
`event_step: config -> config -> tenv -> stenv -> stenv -> event -> Prop`, which
augments the semantics of `mimperative.v` with events:

```coq
Inductive event  :=
| EmptyEvent : event
| AssignEvent : level_proj1 -> id -> value -> event
| NewEvent : level_proj1 -> id -> loc -> event
| GetEvent : level_proj1 -> id -> id -> value -> event
| SetEvent : level_proj1 -> level_proj1 -> id -> nat -> value -> event
| TimeEvent : level_proj1 -> id -> nat -> event
| RestoreEvent: level_proj1 -> nat -> event.
```

The events, as well as the event semantics is found in `augmented.v`. This
file also presents an adequacy result `event_step_adequacy` relating the event
semantics to the augmented semantics from `mimperative.v`:

```coq
Lemma event_step_adequacy:
  forall c c' pc pc' pc'' m m' h h' t t' Γ Σ Σ',
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    ∃ ev,
      ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩.
```

#### Bridge relation

The 'work horse' of the proof is done using a relation called the
'bridge' relation `bridge_step_num: level_proj1 -> config -> config -> tenv ->
stenv -> stenv -> event -> nat -> Prop`. This defines an inductive relation
which 'bridges' over a number of high events in order to get to either a low
event, or a terminating configuration. An adequacy result `bridge_adequacy`
between the bridging relation and the augmented semantics is found in `ni.v`.

```coq
Theorem bridge_adequacy:
  forall Γ n ℓ_adv Σ Σ'' c pc pc'' m m'' h h'' t t'' pc_end,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
    ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ'', n) ⟨Stop, pc'', m'', h'', t''⟩ ->
    (c = Stop \/
     (c <> Stop /\
      ∃ ev c' pc' m' h' t' k Σ',
        n > k /\
        ⟨c, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, k] ⟨c', pc', m', h', t'⟩ /\
        ⟨c', pc', m', h', t'⟩ ⇒ (Γ, Σ', Σ'', n - k - 1) ⟨Stop, pc'', m'', h'', t''⟩)).
```

### Well-formedness

A configuration `⟨c, pc, m, h, t⟩` is well-formed wrt. (Γ, Σ) iff the following
properties hold

- A memory `m` is well-formed wrt. Γ, written wf_tenv m iff
  + If `Γ x` is an integer type, then the value stored in `m` is a number.
  ```coq
    ∀ x l v,
      memory_lookup m x = Some v ->
      Γ x = Some (SecType Int l) ->
      ∃ n, v = ValNum n.
    ```
  + If `Γ x` is an array type, then the value stored in `m` is a location.
    ```coq
    ∀ x l1 t v l2,
      memory_lookup m x = Some v ->
      Γ x = Some (SecType (Array t l1) l2) ->
      ∃ loc, v = ValLoc loc.
    ```
  + Γ contains only wellformed types.
    ```coq
    ∀ τ x, Γ x = Some τ -> wf_type bot τ
    ```
  + Every value in `m` has a type.
    ```coq
    ∀ x v,
      memory_lookup m x = Some v ->
      ∃ τ, Γ x = Some τ).
    ```
- Likewise, a heap is well-formed wrt. Σ, written wf_stenv h Σ iff
  + If `Σ loc` is an integer type, then all values in the array stored at location
    `loc` in `h` is a number.
    ```coq
    ∀ loc ℓ n v μ l,
      Σ loc = Some (SecType Int l) ->
      heap_lookup loc h = Some (ℓ, μ) ->
      lookup μ n = Some v ->
      ∃ n', v = ValNum n'
    ```
  + If `Σ loc` is an array type, then all values in the array stored at location
    `loc` in `h` is a location.
    ```coq
    ∀ loc t l1 l2 n v ℓ μ,
      Σ loc = Some (SecType (Array t l1) l2) ->
      heap_lookup loc h = Some (ℓ, μ) ->
      lookup μ n = Some v ->
      ∃ loc', v = ValLoc loc'
    ```
  + Σ contains only wellformed types.
    ```coq
    ∀ loc τ, Σ loc = Some τ -> wf_type bot τ
    ```
  + All locations stored in `h` has a type.
    ```coq
    ∀ loc ℓ μ,
      heap_lookup loc h = Some (ℓ, μ) ->
      ∃ τ, env loc = Some τ
    ```
- Memory `m` and heap `h` are consistent.
  + If `Γ x` is type `Array t ℓ` and `x` has the value `loc` in `m`, then `Σ loc` is type `t`.
    ```coq
    ∀ x t ε ℓ loc,
      Γ x = Some (SecType (Array t ℓ) ε) ->
      memory_lookup m x = Some (ValLoc loc) ->
      Σ loc = Some t
    ```
  + If `Σ loc1` is type `Array t ℓ` then any location in the array pointed to by `loc1`
    must have type `t`. For technical reasons we only quantify over the reachable locations.
    ```coq
    ∀ loc1 loc2 t ℓ ε n μ l,
        reach m h loc1 ->
        Σ loc1 = Some (SecType (Array t ℓ) ε) ->
        heap_lookup loc1 h = Some (l, μ) ->
        lookup μ n = Some (ValLoc loc2) ->
        Σ loc2 = Some t
    ```
- It holds that either
  + Command `c` is `Stop` or `TimeOut`
  + Command `c` is well-typed, written `wt tenv pc c`.
- Memory `m` and heap `h` are free of dangling pointers. That is, any reachable
  location must have a value in the heap `h`:
  ```coq
  Definition dangling_pointer_free (m: Memory) (h: Heap) :=
    ∀ loc, reach m h loc -> ∃ ℓ μ, heap_lookup loc h = Some (ℓ, μ).
  ```
- Arrays have well-defined bounds. That is, if the array at location `loc` has
  length `len` then any lookup at index `n` into the array such that `0 ≦ n < len`
  will result in a value.
  ```coq
    Definition lookup_in_bounds (m: Memory) (h: Heap) :=
    ∀ loc n len ℓ μ,
      reach m h loc ->
      length_of loc h = Some len ->
      0 <= n ->
      n < len ->
      heap_lookup loc h = Some (ℓ, μ) ->
      ∃ v, lookup μ n = Some v.
  ```
- Memory `m` and heap `h` are *heap-level bound* if
  + If `Γ x` is type `Array s l` and x has the value `loc` in `m`, then the
    security level of the array located at `loc` in `h` is `l`:
    ```coq
      ∀ x s loc k ℓ ε μ,
        Γ x = Some (SecType (Array s l) ε) ->
        memory_lookup m x = Some (ValLoc loc) ->
        heap_lookup loc h = Some (ℓ, μ) ->
        l = ℓ
    ```
  + If `Σ loc` is type `Array s l` and `loc` is the location of the array `μ` and
    security level `ℓ`. Then the security level of any location stored in the
    array μ will be `l`. For technical reasons we quantify only over reachable
    locations.
    ```coq
    ∀ n s l ℓ ℓ' μ ν loc loc' ℓ_p ι,
      reach m h loc ->
      Σ loc = Some (SecType (Array s ℓ_p) (l, ι)) ->
      heap_lookup loc h = Some (ℓ, μ) ->
      lookup μ n = Some (ValLoc loc') ->
      heap_lookup loc' h = Some (ℓ', ν) ->
      ℓ' = ℓ_p
    ```
  + Security levels found in `h` is increasing.
    ```coq
    ∀ loc1 loc2 ℓ1 ℓ2 μ ν n,
      reach m h loc1 ->
      heap_lookup loc1 h = Some (ℓ1, μ) ->
      lookup μ n = Some (ValLoc loc2) ->
      heap_lookup loc2 h = Some (ℓ2, ν) ->
      ℓ1 ⊑ ℓ2
    ```

### Low-equivalence

First define what we mean by a *low location*. Low locations can be either:
* Locations with a low security level in `h`
* Locations that can be reached by following a chain of pointers with a
low security level in Σ. (This is known as *low reachable* locations)

With this in mind, we can discuss the low equivalence relation. We use a partial
bijection `φ` to relate the locations allocated by the two configurations.
The domain (codomain) of `φ` is the set of low locations of the first (second)
configuration.

#### Low equivalence of heap typings
Two heap typings Σ1 and Σ2 are low equivalent if related locations have the same
heap typing. For technical reasons we include the requirement that the locations
be low, even though this is given by the fact that the locations are related
by the bijection.

```coq
Definition low_eq_stenv ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 :=
  ∀ loc1 loc2 τ,
    left φ loc1 = Some loc2 ->
    (Σ1 loc1 = Some τ /\ low ℓ_adv Γ Σ1 m1 h1 loc1) <->
    (Σ2 loc2 = Some τ /\ low ℓ_adv Γ Σ2 m2 h2 loc2).
```

#### Low equivalence of memories
Two memories have low equivalent domains if the domain of the public variables
in `m1` and `m2` is equal.
```coq
Definition low_domain_eq ℓ Γ m1 m2 :=
  ∀ x t l ι,
    Γ x = Some (SecType t (l, ι)) ->
    l ⊑ ℓ ->
    (∃ v, memory_lookup m1 x = Some v) <->
    (∃ u, memory_lookup m2 x = Some u).
```
The two memories `m1` and `m2` are low equivalent if they have low equivalent
domains and all values both in `m1` and `m2` are low equivalent wrt. their type.
```coq
Definition memory_lookup_low_eq ℓ Γ m1 m2 φ :=
  ∀ x τ v1 v2,
    Γ x = Some τ ->
    memory_lookup m1 x = Some v1 ->
    memory_lookup m2 x = Some v2 ->
    val_low_eq ℓ τ v1 v2 φ.
```

#### Low-equivalence of heaps
Two heaps have low equivalent domains if the domain of the low locations
in `h1` and `h2` is equal.
```coq
Definition low_heap_domain_eq ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 :=
    ∀ l1 l2 ℓ,
      left φ l1 = Some l2 ->
      ((∃ μ, heap_lookup l1 h1 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ1 m1 h1 l1)
      <->
      ((∃ ν, heap_lookup l2 h2 = Some (ℓ, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
```
Two heaps are low equivalent if
* They have low equivalent domains.
* Low locations related by φ are heap-value low-equivalent.
```coq
Definition heap_lookup_low_eq ℓ φ m1 m2 h1 h2 Γ Σ1 Σ2 :=
  ∀ loc1 loc2 τ,
    Σ1 loc1 = Some τ ->
    Σ2 loc2 = Some τ ->
    left φ loc1 = Some loc2 ->
    low ℓ Γ Σ1 m1 h1 loc1 ->
    low ℓ Γ Σ2 m2 h2 loc2 ->
    heapval_low_eq ℓ τ loc1 loc2 m1 m2 h1 h2 φ.
```

#### Low equivalence of reachability

Two pairs of memories and heaps `(m1, h1)` and `(m2, h2)` have low equivalent
reachability if locations related by the bijection have the same low reachability.

```coq
Definition low_reach_NI ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 :=
  ∀ loc loc',
    left φ loc = Some loc' ->
    low_reach ℓ_adv Γ Σ1 m1 h1 loc <-> low_reach ℓ_adv Γ Σ2 m2 h2 loc'.
```

#### Low equivalence of heap size
Finally we require that all low partitions of the heap `h` have equal size.
```coq
forall l, l ⊑ ℓ_adv -> size l h = size l h'
```

### Type system
The type system is a standard (Denning-style) information flow type system
augmented with integrity labels to restrict the usage of values affected by time.

#### Preservation

The preservation theorem is standard. The following statement of the
preservation theorem is an excerpt from [preservation.v](https://github.com/MathiasVP/ni-formal-gc/blob/master/preservation.v).

```coq
Lemma preservation:
  ∀ Γ Σ Σ' c1 pc1 m1 h1 t1 c2 pc2 m2 h2 t2 pc',
    wellformed_aux Γ Σ ⟨c1, pc1, m1, h1, t1⟩ pc' ->
    ⟨c1 pc1 m1 h1 t1⟩ ⇒ (Γ, Σ, Σ') ⟨c2, pc2, m2, h2, t2⟩ ->
    wellformed_aux Γ Σ' ⟨c2, pc2, m2, h2, t2⟩ pc'.
```

### Noninterference

The file `nibridge_helper.v` contains various required technical results. Most
importantly, the definition of the invariants used for the technical
non-interference theorem is presented:

```coq
Definition ni_bridge (n1: nat) (ℓ: level_proj1): Prop :=
  forall Γ Σ1 Σ2 Σ3 Σ1' Σ3' φ Φ pc pc1' pc2'' c c' c2 c2' m1 m2 s1 s2'' h1 h2
    w1 w2'' t t2 g2'' s1' w1' ev1 ev2 pc_end n2 t',
    wf_bijection ℓ φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ (inverse φ) Γ Σ2 s1 w1 ->
    wf_taint_bijection ℓ Φ s1 w1 ->
    wf_taint_bijection ℓ (inverse Φ) s1' w1' ->
    wellformed_aux Γ Σ1 ⟨c, pc, m1, h1, t⟩ pc_end ->
    wellformed_aux Γ Σ2 ⟨c, pc, s1, w1, t⟩ pc_end ->
    wellformed_aux Γ Σ3 ⟨c', pc, s1', w1', t'⟩ pc_end ->
    state_low_eq ℓ φ m1 h1 s1 w1 Γ Σ1 Σ2 ->
    pc ⊑ ℓ ->
    taint_eq ℓ Φ Γ Σ2 Σ3 c c' s1 w1 s1' w1' ->
    ⟨c, pc, m1, h1, t⟩ ↷ [ℓ, Γ, Σ1, Σ1', ev1, n1] ⟨c2, pc1', m2, h2, t2⟩ ->
    ⟨c', pc, s1', w1', t'⟩ ↷ [ℓ, Γ, Σ3, Σ3', ev2, n2] ⟨c2', pc2'', s2'', w2'', g2''⟩ ->
    c2 <> TimeOut ->
    c2' <> TimeOut ->
    ∃ ev1' n1' ψ Ψ s2' w2' Σ2',
      ⟨c, pc, s1, w1, t⟩ ↷ [ℓ, Γ, Σ2, Σ2', ev1', n1'] ⟨c2, pc1', s2', w2', t2⟩ /\
      pc1' ⊑ ℓ /\
      pc2'' = pc1' /\
      state_low_eq ℓ ψ m2 h2 s2' w2' Γ Σ1' Σ2'/\
      event_low_eq ℓ (left ψ) ev1 ev1' /\
      taint_eq_events Γ Ψ ev1' ev2 /\
      wf_bijection ℓ ψ Γ Σ1' m2 h2 /\
      wf_bijection ℓ (inverse ψ) Γ Σ2' s2' w2' /\
      wf_taint_bijection ℓ Ψ s2' w2' /\
      wf_taint_bijection ℓ (inverse Ψ) s2'' w2'' /\
      taint_eq ℓ Ψ Γ Σ2' Σ3' c2 c2' s2' w2' s2'' w2''.
Hint Unfold ni_bridge.
```

The major technical theorem is proving that `ni_bridge n ℓ` holds for all `n :
nat` and `ℓ: level_proj1`. The theorem
```coq
Theorem ni_bridge_num: forall n ℓ, ni_bridge n ℓ.
```

is proved by strong induction over the number of intermediate high steps in the
derivation `⟨c, pc, m1, h1, t⟩ ↷ [ℓ, Γ, Σ1, Σ1', ev1, n1] ⟨c2, pc1', m2, h2,
t2⟩`. Both case `n = 0` and case `n > 0` is proved by structural induction in
`c`.

The proof using an interesting technique which relates three configurations
instead of the usual two configurations. The reason stems from the
fact that our definition of non-interference is possibilistic. That is, given
two terminating configurations we can construct another terminating
configuration.
