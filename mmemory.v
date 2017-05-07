Require Import Arith id_and_loc mlattice language LibTactics decision List tactics types Coq.Program.Basics bijection.

Module Type Memory (L: Lattice).
  Module LatProp := LatticeProperties L.
  Module T := Types L.
  Import T L Lang LatProp.

  Parameter Memory: Set.
  Parameter Heap: Set.

  (* A lookupfunc is the result of looking up a location in the heap *)
  Parameter lookupfunc: Set.
  Parameter lookup: lookupfunc -> nat -> option value.

  (* Two lookupfuncs are equal if they contain the same values *)
  Axiom lookupfunc_extensionality:
    forall μ ν,
      (forall n, lookup μ n = lookup ν n) -> μ = ν.

  (* A lookupfunc can be updated at an index to create a new lookupfunc *)
  Parameter update_lookup: lookupfunc -> nat -> value -> lookupfunc.

  (* Looking up a value at an index after updating the same index
     gives back the new value *)
  Axiom lookup_update_eq:
    forall μ n v,
      lookup (update_lookup μ n v) n = Some v.
  Hint Resolve lookup_update_eq.

  (* Updating a lookupfunc only affects the updated index *)
  Axiom lookup_update_neq:
    forall μ n1 n2 v,
      n1 <> n2 ->
      lookup (update_lookup μ n1 v) n2 = lookup μ n2.
  Hint Resolve lookup_update_neq.

  (* There exists an empty memory and an empty heap *)
  Parameter emptyMemory: Memory.
  Parameter emptyHeap: Heap.

  (* A memory can be extended *)
  Parameter extend_memory: id -> value -> Memory -> Memory.

  Notation "m '[' x '→' v ']'" := (extend_memory x v m) (at level 10, no associativity).

  (* Given a location we can get the amount of slots allocated for that location *)
  Parameter length_of: loc -> Heap -> option nat.

  (* A heap partition has a size *)
  Parameter size: level_proj1 -> Heap -> nat.

  (* Each heap partition has a maximum size *)
  Parameter maxsize : level_proj1 -> Heap -> nat.

  (* An empty heap has size 0 *)
  Axiom empty_heap_has_size_0:
    forall l,
      size l emptyHeap = 0.
  
  (* It's impossible to change the maximum size of a heap *)
  Axiom constant_maxsize:
    forall h1 h2 l,
      maxsize l h1 = maxsize l h2.

  (* A heap can be updated *)
  Parameter heap_lookup: loc -> Heap -> option (level_proj1 * lookupfunc).

  (* We can look up a value in a memory given an identifier *)
  Parameter memory_lookup: Memory -> id -> option value.  
  
  (* We can extend a heap to obtain a new heap *)
  Parameter extend_heap:
    value ->
    forall loc ℓ n h,
      heap_lookup loc h = None ->
      size ℓ h + n <= maxsize ℓ h ->
      Heap.
  
  Notation "h '[' loc → '(' n '×' v ',' l ')' ',' H1 ',' H2 ']'" := (extend_heap v loc l n h H1 H2) (at level 10, no associativity, only parsing).
  
  (* Heap partition size increases by N if we extend a heap
     with a new location of size n in that partition *)
  Axiom size_extend_heap_eq_level:
    forall loc n v l h H1 H2,
      size l (h [loc → (n × v, l), H1, H2]) = size l h + n.

  (* Extending a heap partition only affects the heap partition we extend *)
  Axiom size_extend_heap_neq_level:
    forall loc n v l1 l2 h H1 H2,
      l1 <> l2 ->
      size l1 (h [loc → (n × v, l2), H1, H2]) = size l1 h.

  (* We can update a value in the heap (ie. update the lookupfunc stored at
     a location) *)
  Parameter update_heap: loc -> nat -> value -> Heap -> Heap.

  (* Looking up a location in an updated heap gives an updated lookupfunc *)
  Axiom heap_lookup_update_eq:
    forall loc n v h l μ,
      heap_lookup loc h = Some (l, μ) ->
      heap_lookup loc (update_heap loc n v h) = Some (l, update_lookup μ n v).
  Hint Resolve heap_lookup_update_eq.

  (* Updating a heap location only affects that one location *)
  Axiom heap_lookup_update_neq:
    forall loc1 loc2 n v h,
      loc1 <> loc2 ->
      heap_lookup loc1 (update_heap loc2 n v h) = heap_lookup loc1 h.
  Hint Resolve heap_lookup_update_neq.

  (* Looking up a value we just inserted gives back a lookupfunc which always returns the value inserted. *)
  Axiom heap_lookup_extend_eq:
    forall loc l n v h H1 H2,
      { μ | heap_lookup loc (h [loc → (n × v, l), H1, H2]) = Some (l, μ) /\
            forall n, lookup μ n = Some v }.
  Hint Resolve heap_lookup_extend_eq.

  (* Inserting a value into the heap only affects that one value *)
  Axiom heap_lookup_extend_neq:
    forall loc1 loc2 l n v h H1 H2,
      loc1 <> loc2 ->
      heap_lookup loc1 (h [loc2 → (n × v, l), H1, H2]) = heap_lookup loc1 h.
  Hint Resolve heap_lookup_extend_neq.      

  (* We can remove locations from the heap *)
  Parameter reduce_heap: loc -> Heap -> Heap.

  (* Removing a location from a heap actually removes it *)
  Axiom heap_lookup_reduce_eq:
    forall loc h,
      heap_lookup loc (reduce_heap loc h) = None.
  Hint Resolve heap_lookup_reduce_eq.

  (* Removing a location from the heap only removes that one location *)
  Axiom heap_lookup_reduce_neq:
    forall loc1 loc2 h,
      loc1 <> loc2 ->
      heap_lookup loc1 (reduce_heap loc2 h) = heap_lookup loc1 h.
  Hint Resolve heap_lookup_reduce_neq.

  (* Removing a location of size n reduces the size of the heap partition by n *)
  Axiom size_reduce_heap_eq_level:
    forall loc h n l μ,
      heap_lookup loc h = Some (l, μ) ->
      length_of loc h = Some n ->
      size l h = size l (reduce_heap loc h) + n.
  Hint Resolve size_reduce_heap_eq_level.

  (* Removing a location only affects the heap partition we remove from *)
  Axiom size_reduce_heap_neq_level:
    forall loc l1 l2 μ h,
      l1 <> l2 ->
      heap_lookup loc h = Some (l1, μ) ->
      size l2 (reduce_heap loc h) = size l2 h.
  Hint Resolve size_reduce_heap_neq_level.

  (* Looking up a value just inserted gives back that value *)
  Axiom extend_memory_lookup_eq:
    forall x v m,
      memory_lookup (extend_memory x v m) x = Some v.
  Hint Resolve extend_memory_lookup_eq.

  (* Extending the memory only affects the entry we add to the memory *)
  Axiom extend_memory_lookup_neq:
    forall x y v m,
      x <> y ->
      memory_lookup (extend_memory x v m) y = memory_lookup m y.
  Hint Resolve extend_memory_lookup_neq.

  (* If we allocate an array of size n then the length of the location is n *)
  Axiom length_of_extend_eq:
    forall loc l n v h H1 H2,
      length_of loc (h [loc → (n × v, l), H1, H2]) = Some n.
  Hint Resolve length_of_extend_eq.

  (* Extending the heap does not affect any other length than the one we extend the heap with *)
  Axiom length_of_extend_neq:
    forall loc1 loc2 l n v h H1 H2,
      loc1 <> loc2 ->
      length_of loc1 (h [loc2 → (n × v, l), H1, H2]) = length_of loc1 h.
  Hint Resolve length_of_extend_neq.

  (* Updaing a value in the heap leaves the length unchanged *)
  Axiom length_of_update:
    forall loc1 loc2 n v h,
      length_of loc1 (update_heap loc2 n v h) = length_of loc1 h.
  Hint Resolve length_of_update.

  (* Updating a value on the heap does not extend the heap *)
  Axiom heap_lookup_update_none:
    forall loc1 loc2 v h n,
      heap_lookup loc1 h = None ->
      heap_lookup loc1 (update_heap loc2 n v h) = None.

  (* Heaps are abstract objects and we need a way to state that they are equal.
     We say that two heaps are equal if they contain the same locations, and the locations map to the same values.
 *)
  Axiom heap_extensionality:
    forall h1 h2,
      (forall loc, heap_lookup loc h1 = heap_lookup loc h2) <-> h1 = h2.
  
  (* This one is crucial:
     If we have space enough to allocate an array of size n in the heap
     (as specified by H2) then we can find a location which is not in the heap,
     and extend the heap with this location.
 *)
  Axiom fresh_location:
    forall h l n v H2,
    exists loc H1 μ,
      heap_lookup loc (h [loc → (n × v, l), H1, H2]) = Some (l, μ) /\
                       forall n', lookup μ n' = Some v.

  (* Garbage collection *)
  Parameter gc: Memory -> Heap -> nat -> Heap -> Prop.

  (* Definition of what it means for heaps to be disjoint *)
  Definition disjoint (h1 h2 : Heap) :=
    forall loc ℓ μ,
      (heap_lookup loc h1 = Some (ℓ, μ) -> heap_lookup loc h2 = None)
      /\
      (heap_lookup loc h2 = Some (ℓ, μ) -> heap_lookup loc h1 = None).
  Hint Unfold disjoint.

  (* We can union two heaps to produce a new heap provided that they are disjoint *)
  Parameter disjoint_union:
    forall (h1 h2 : Heap)
      (H: disjoint h1 h2),
    Heap.

  Notation "'[' h1 ⊎ h2 ',' H ']'" := (disjoint_union h1 h2 H) (at level 10, no associativity).
  Notation "h1 ⇝ '(' m ',' δ ')' h2" := (gc m h1 δ h2) (at level 10, no associativity). 

  (* Technical details: Throughout many of the proofs we need to show that two heaps are equal. Sometimes the only difference between the two heaps is that they are disjoint for two different reasons. By having this weak form of proof irrelevance for we solve this problem and state that we don't care about WHY the heaps are disjoint, but just the fact that they are disjoint. *)
  Axiom disjoint_union_proof_irrelevance:
    forall h1 h2 H1 H2,
      [h1 ⊎ h2, H1] = [h1 ⊎ h2, H2].

  (* Disjoint union is forms a superset. *)
  Axiom disjoint_union_heap_lookup:
    forall h1 h2 loc ℓ μ H,
      heap_lookup loc h1 = Some (ℓ, μ) ->
      heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ).
  Hint Resolve disjoint_union_heap_lookup.

  (* Locations in h1 ⊎ h2 are locations from h1 and h2 *)
  Axiom disjoint_union_heap_lookup2:
    forall h1 h2 loc ℓ μ H,
      heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ) ->
      heap_lookup loc h1 = Some (ℓ, μ) \/
      heap_lookup loc h2 = Some (ℓ, μ).
  Hint Resolve disjoint_union_heap_lookup2.

  Ltac destruct_disjoint_heap_lookup :=
    match goal with
      [H: heap_lookup _ ([_ ⊎ _, _]) = Some _ |- _] =>
      destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H)
    end.

  Lemma disjoint_sym:
    forall h1 h2,
      disjoint h1 h2 -> disjoint h2 h1.
  Proof.
    intros.
    unfold disjoint in *.
    intros.
    eapply and_comm.
    eauto.
  Qed.
  Hint Resolve disjoint_sym.
  
  (* Disjoint union is a symmetryc operation. This makes sense since we have a proof
     that they are disjoint. *)
  Axiom disjoint_union_sym:
    forall h1 h2 H,
      [h1 ⊎ h2, H] = [h2 ⊎ h1, disjoint_sym _ _ H].    

  (* The characteristic property of an empty heap is that it contains no locations. *)
  Axiom empty_heap_is_empty:
    forall loc,
      heap_lookup loc emptyHeap = None.
  Hint Resolve empty_heap_is_empty.

  (* The size of two disjoint heap partitions is the sum of their sizes *)
  Axiom size_heap_distr:
    forall l h1 h2 H,
      size l ([h1 ⊎ h2, H]) = size l h1 + size l h2.

  (* Updating the heap preserves the size of the heap *)
  Axiom size_update_heap:
    forall l loc n v h,
      size l (update_heap loc n v h) = size l h.

  (* Induction principles for heaps. If a property P is true for the empty heap,
     and if it holds for an extension of the heap assuming it holds from the initial heap, then it holds for every heap.
 *)
  Axiom heap_ind:
    forall P : Heap -> Prop,
      P emptyHeap ->
      (forall loc n v h l H1 H2,
          P h ->
          P (h [loc → (n × v, l), H1, H2])) ->
      forall h, P h.

  (* The same as heap_ind, but for Set. This is used to lift a function operating on locations, to a function opearting on heaps. *)
  Axiom heap_rec:
    forall P : Heap -> Set,
      P emptyHeap ->
      (forall loc n v h l H1 H2,
          P h ->
          P (h [loc → (n × v, l), H1, H2])) ->
      forall h, P h.

  (* Base case and induction case for the recursion principle. Think of these as the two cases as the cases of a fold. *)
  Axiom heap_rec_bc:
    forall P bc ic,
      heap_rec P bc ic emptyHeap = bc.
  
  Axiom heap_rec_ic:
    forall P bc ic loc l n v h H1 H2,
      heap_rec P bc ic (h [loc → (n × v, l), H1, H2]) =
      ic loc n v h l H1 H2
         (heap_rec P bc ic h).

  (* A location has a length iff it has been allocated in the heap *)
  Axiom length_of_lookup_correspondance:
    forall h loc,
      (exists l μ, heap_lookup loc h = Some (l, μ)) <-> (exists n, length_of loc h = Some n).

  (* Union'ing a disjoint heap onto another heap preserves the allocation sizes of all locations *)
  Axiom disjoint_union_length_of:
    forall h1 h2 loc n H,
      length_of loc h1 = Some n ->
      length_of loc ([h1 ⊎ h2, H]) = Some n.
  Hint Resolve disjoint_union_length_of.

  (* If:
     - We have a bijection in the partial between two heaps
     - The partial bijection's domain includes at least the domain of heap h1
     - The partial bijection's codomain includes at lrast the domain of heap h2
     Then:
      The size of the two heaps is the same.
 *)
  Axiom implies_same_size:
    forall h1 h2 φ,
      (forall loc1 loc2,
          left φ loc1 = Some loc2 ->
          length_of loc1 h1 = length_of loc2 h2) ->
      (forall loc length,
          length_of loc h1 = Some length ->
          exists loc', left φ loc = Some loc') ->
      (forall loc length,
          length_of loc h2 = Some length ->
          exists loc', left φ loc' = Some loc) ->
      forall l, size l h1 = size l h2.

  (* This is the key axiom also specified in the paper. The premise is the same as above.
     If:
     - We have a bijection in the partial between two heaps h1 h2
     - We have a bijection in the partial between two heaps h1' h2'
     - The partial bijection's domain includes at least the domain of heap h1
     - The partial bijection's codomain includes at lrast the domain of heap h2
     - A gc happens in h1 producing h1' taking time δ
     Then:
     We can construct a gc in h2 producing h2' taking time δ.
  *)
  Axiom gc_axiom:
    forall h1 h1' h2 h2' m1 m2 φ δ,
      (forall loc1 loc2 ℓ,
          left φ loc1 = Some loc2 ->
          (exists μ, heap_lookup loc1 h1 = Some (ℓ, μ)) <->
          (exists ν, heap_lookup loc2 h2 = Some (ℓ, ν))) ->
      (forall loc1 loc2 ℓ,
          left φ loc1 = Some loc2 ->
          (exists μ, heap_lookup loc1 h1' = Some (ℓ, μ)) <->
          (exists ν, heap_lookup loc2 h2' = Some (ℓ, ν))) ->
      (forall loc ℓ μ,
          heap_lookup loc h1 = Some (ℓ, μ) ->
          exists loc', left φ loc = Some loc') ->
      (forall loc ℓ μ,
          heap_lookup loc h2 = Some (ℓ, μ) ->
          exists loc', left φ loc' = Some loc) ->
      h1 ⇝ (m1, δ) h1' ->
      h2 ⇝ (m2, δ) h2'.
  
End Memory.

Module MemoryProperties (L: Lattice) (M: Memory L).
  Import M T L Lang LatProp.

  Lemma disjoint_empty_heap:
    forall h, disjoint h emptyHeap.
  Proof.
    intros.
    unfolds.
    intros.
    splits.
    - intros.
      eauto.
    - intros.
      assert (heap_lookup loc emptyHeap = None) by eauto 2.
      congruence.
  Qed.
  Hint Resolve disjoint_empty_heap.

  Lemma disjoint_union_empty_heap:
    forall h H,
      h = [h ⊎ emptyHeap, H].
  Proof.
    intros.
    eapply heap_extensionality.
    intros.
    destruct (heap_lookup loc ([h ⊎ emptyHeap, H])) eqn:H_loc.
    - destruct p.
      destruct_disjoint_heap_lookup.
      + eauto 2.
      + assert (heap_lookup loc emptyHeap = None) by eauto 2.
        congruence.
    - destruct (heap_lookup loc h) eqn:H_loc'; try reflexivity.
      destruct p.
      assert (heap_lookup loc ([h ⊎ emptyHeap, H]) = Some (l, l0)).
      {
        eapply disjoint_union_heap_lookup; eauto 2.
      }
      congruence.
  Qed.
  Hint Resolve disjoint_union_empty_heap.

  Lemma disjoint_union_length_of2:
    forall h1 h2 loc n H,
      length_of loc ([h1 ⊎ h2, H]) = Some n ->
      length_of loc h1 = Some n \/ length_of loc h2 = Some n.
  Proof.
    intros.
    assert (exists ℓ μ, heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ)).
    {
      eapply length_of_lookup_correspondance; eauto 2.
    }
    super_destruct; subst.
    destruct_disjoint_heap_lookup.
    - assert (exists n', length_of loc h1 = Some n').
      {
        eapply length_of_lookup_correspondance; eauto 3.
      }
      super_destruct; subst.
      cut (n' = n).
      {
        intros.
        subst.
        eauto.
      }
      {
        cut (length_of loc ([h1 ⊎ h2, H]) = Some n').
        {
          congruence.
        }
        {
          eapply disjoint_union_length_of; eauto.
        }
      }
    - assert (exists n', length_of loc h2 = Some n').
      {
        eapply length_of_lookup_correspondance; eauto 3.
      }
      super_destruct; subst.
      cut (n' = n).
      {
        intros.
        subst.
        eauto.
      }
      {
        cut (length_of loc ([h1 ⊎ h2, H]) = Some n').
        {
          congruence.
        }
        {
          rewrite -> disjoint_union_sym.
          eapply disjoint_union_length_of; eauto.
        }
      }
  Qed.    
  Hint Resolve disjoint_union_length_of2.
  
  Lemma heap_lookup_extend_none:
    forall loc1 loc2 l n v h H1 H2,
      heap_lookup loc1 (h [loc2 → (n × v, l), H1, H2]) = None ->
      heap_lookup loc1 h = None.
  Proof.
    intros.
    destruct (decide (loc1 = loc2)); subst.
    - remember_simple (heap_lookup_extend_eq loc2 l n v h H1 H2).
      super_destruct; congruence.
    - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
      eauto.
  Qed.
  
  Lemma weak_heap_lookup_extend_eq:
    forall loc l n v h H1 H2,
      exists μ, heap_lookup loc (h [loc → (n × v, l), H1, H2]) = Some (l, μ) /\
           forall n, lookup μ n = Some v.
  Proof.
    intros.
    destruct (heap_lookup_extend_eq loc l n v h H1 H2); eauto.
  Qed.
  Hint Resolve weak_heap_lookup_extend_eq.
  
  Lemma heap_lookup_update_eq2:
    forall loc l n v h μ,
      heap_lookup loc (update_heap loc n v h) = Some (l, μ) ->
      exists ν,
        heap_lookup loc h = Some (l, ν) /\
        μ = update_lookup ν n v.
  Proof.
    intros.
    destruct (heap_lookup loc h) eqn:H_loc.
    - destruct p.
      rewrite -> (heap_lookup_update_eq loc n v h l0 l1 H_loc) in *.
      rewrite_inj.
      exists l1.
      splits*.
    - rewrite -> heap_lookup_update_none in * by eauto.
      discriminate.
  Qed.
  Hint Resolve heap_lookup_update_eq2.

  Lemma heap_lookup_update_none2:
    forall loc1 loc2 n v h,
      heap_lookup loc1 (update_heap loc2 n v h) = None ->
      heap_lookup loc1 h = None.
  Proof.
    intros.
    destruct (heap_lookup loc1 h) eqn:H_loc1.
    - destruct p.
      destruct (decide (loc1 = loc2)); subst.
      + erewrite -> heap_lookup_update_eq in * by solve[eauto].
        discriminate.
      + rewrite -> heap_lookup_update_neq in * by solve[eauto].
        rewrite_inj.
        discriminate.
    - reflexivity.
  Qed.
      
  Inductive reach : Memory -> Heap -> loc -> Prop :=
  | reach_mem:
      forall m h x loc,
        memory_lookup m x = Some (ValLoc loc) -> reach m h loc
  | reach_heap:
      forall m h loc loc' ℓ μ n,
        reach m h loc ->
        heap_lookup loc h = Some (ℓ, μ) ->
        lookup μ n = Some (ValLoc loc') ->
        reach m h loc'.
  Hint Constructors reach.

  Axiom reach_dec:
    forall m h loc,
      { reach m h loc } + { ~ reach m h loc }.

  Inductive low_reach: level_proj1 -> tenv -> stenv -> Memory -> Heap -> loc -> Prop :=
  | LowReachMem:
      forall Γ Σ ℓ_adv ℓ_p x τ m h loc l,
        Γ x = Some (SecType (Array τ ℓ_p) (l, ∘)) ->
        l ⊑ ℓ_adv ->
        memory_lookup m x = Some (ValLoc loc) ->
        low_reach ℓ_adv Γ Σ m h loc
  | LowReachHeap:
      forall Γ Σ ℓ_adv l ℓ ℓ_p m h τ loc1 loc2 n μ,
        low_reach ℓ_adv Γ Σ m h loc1 ->
        Σ loc1 = Some (SecType (Array τ ℓ_p) (l, ∘)) ->
        heap_lookup loc1 h = Some (ℓ, μ) ->
        l ⊑ ℓ_adv ->
        lookup μ n = Some (ValLoc loc2) ->
        low_reach ℓ_adv Γ Σ m h loc2.
  Hint Constructors low_reach.

  Axiom low_reach_dec:
    forall ℓ_adv Γ Σ m h loc,
      { low_reach ℓ_adv Γ Σ m h loc } + { ~ low_reach ℓ_adv Γ Σ m h loc }.

  Lemma disjoint_union_heap_lookup3:
    forall h1 h2 loc ℓ μ H,
      heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ) ->
      heap_lookup loc h1 = Some (ℓ, μ) ->
      heap_lookup loc h2 = None.
  Proof.
    intros.
    apply disjoint_union_heap_lookup2 in H0.
    destruct H0; eapply H; eauto 2.
  Qed.
  Hint Resolve disjoint_union_heap_lookup3.

  Lemma disjoint_union_heap_lookup4:
    forall h1 h2 loc ℓ μ H,
      heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ) ->
      heap_lookup loc h1 = None ->
      heap_lookup loc h2 = Some (ℓ, μ).
  Proof.
    intros.
    apply disjoint_union_heap_lookup2 in H0.
    destruct H0; eauto 2 || congruence.
  Qed.    
  Hint Resolve disjoint_union_heap_lookup4.
  
  Lemma disjoint_union_id_left:
    forall h1 h2 H,
      h1 = [h1 ⊎ h2, H] ->
      h2 = emptyHeap.
  Proof.
    intros.
    eapply heap_extensionality.
    intros.
    rewrite -> empty_heap_is_empty.
    assert (forall loc : id_and_loc.loc, heap_lookup loc h1 = heap_lookup loc ([h1 ⊎ h2, H])).
    {
      eapply heap_extensionality; eauto.
    }
    destruct (heap_lookup loc h2) eqn:H_loc; try reflexivity.
    destruct p.
    assert (disjoint h2 h1) by eauto.
    assert (heap_lookup loc ([h2 ⊎ h1, H2]) = Some (l, l0)) as H3 by eauto.
    assert (heap_lookup loc h1 = None) by eauto 2.
    rewrite -> disjoint_union_sym in H3.
    rewrite -> H0 in H4.
    rewrite -> (disjoint_union_proof_irrelevance h1 h2 (disjoint_sym h2 h1 H2) H) in *.
    rewrite_inj.
    discriminate.
  Qed.
  Hint Resolve disjoint_union_id_left.

  Definition levels_satisfy (h: Heap) (p: level_proj1 -> Prop) :=
    forall loc ℓ μ,
      heap_lookup loc h = Some (ℓ, μ) -> p ℓ.

  Lemma disjoint_level_satsify:
    forall h1 h2 h3 h4 p H1 H2,
      [h1 ⊎ h2, H1] = [h3 ⊎ h4, H2] ->
      levels_satisfy h1 p ->
      levels_satisfy h2 (compose not p) ->
      levels_satisfy h3 p ->
      levels_satisfy h4 (compose not p) ->
      h1 = h3 /\ h2 = h4.
  Proof.
    intros.
    splits.
    - eapply heap_extensionality.
      intros.
      destruct (heap_lookup loc h1) eqn:H_loc1; destruct (heap_lookup loc h3) eqn:H_loc3.
      + destruct p0, p1.
        assert (heap_lookup loc ([h1 ⊎ h2, H1]) = Some (l, l0)) by eauto.
        assert (heap_lookup loc ([h3 ⊎ h4, H2]) = Some (l1, l2)) by eauto.
        rewrite -> H in *.
        rewrite_inj.
        reflexivity.
      + destruct p0.
        assert (heap_lookup loc ([h1 ⊎ h2, H1]) = Some (l, l0)) by eauto.
        rewrite -> H in *.
        assert (heap_lookup loc h3 = Some (l, l0) \/ heap_lookup loc h4 = Some (l, l0))
          as H7 by eauto.
        destruct H7.
        * rewrite_inj.
          discriminate.
        * assert (p l) by eauto.
          assert (compose not p l) by eauto.
          contradiction.
      + destruct p0.
        assert (heap_lookup loc ([h3 ⊎ h4, H2]) = Some (l, l0)) by eauto.
        rewrite <- H in *.
        assert (heap_lookup loc h1 = Some (l, l0) \/ heap_lookup loc h2 = Some (l, l0))
          as H7 by eauto.
        destruct H7.
        * rewrite_inj.
          discriminate.
        * assert (p l) by eauto.
          assert (compose not p l) by eauto.
          contradiction.
      + reflexivity.
    - eapply heap_extensionality.
      intros.
      assert ([h2 ⊎ h1, disjoint_sym _ _ H1] = [h4 ⊎ h3, disjoint_sym _ _ H2]) as H'.
      {
        do 2 rewrite <- disjoint_union_sym.
        eauto.
      }
      destruct (heap_lookup loc h2) eqn:H_loc1; destruct (heap_lookup loc h4) eqn:H_loc3.
      + destruct p0, p1.
        assert (heap_lookup loc ([h2 ⊎ h1, disjoint_sym h1 h2 H1]) = Some (l, l0)) by eauto.
        assert (heap_lookup loc ([h4 ⊎ h3, disjoint_sym h3 h4 H2]) = Some (l1, l2)) by eauto.
        rewrite -> H' in *.
        rewrite_inj.
        reflexivity.
      + destruct p0.
        assert (heap_lookup loc ([h2 ⊎ h1, disjoint_sym h1 h2 H1]) = Some (l, l0)) by eauto.
        rewrite -> H' in *.
        assert (heap_lookup loc h4 = Some (l, l0) \/ heap_lookup loc h3 = Some (l, l0))
          as H7 by eauto.
        destruct H7.
        * rewrite_inj.
          discriminate.
        * assert (p l) by eauto.
          assert (compose not p l) by eauto.
          contradiction.
      + destruct p0.
        assert (heap_lookup loc ([h4 ⊎ h3, disjoint_sym h3 h4 H2]) = Some (l, l0)) by eauto.
        rewrite <- H' in *.
        assert (heap_lookup loc h2 = Some (l, l0) \/ heap_lookup loc h1 = Some (l, l0))
          as H7 by eauto.
        destruct H7.
        * rewrite_inj.
          discriminate.
        * assert (p l) by eauto.
          assert (compose not p l) by eauto.
          contradiction.
      + reflexivity.
  Qed.

  Lemma extend_heap_disjoint:
    forall loc h ℓ n v H1 H2,
      heap_lookup loc h = None ->
      disjoint h (emptyHeap [loc → (n × v, ℓ), H1, H2]).
  Proof.
    intros.
    unfolds.
    intros.
    splits.
    - intros.
      destruct (decide (loc0 = loc)); subst.
      + rewrite_inj; discriminate.
      + rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
    - intros.
      destruct (decide (loc0 = loc)); subst.
      + eauto.
      + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        rewrite -> empty_heap_is_empty in *.
        discriminate.
  Qed.

  Lemma disjoint_union_assoc:
    forall h1 h2 h3 H1 H2 H3 H4,
      [h1 ⊎ [h2 ⊎ h3, H1], H2] = [[h1 ⊎ h2, H3] ⊎ h3, H4].
  Proof.
    intros.
    eapply heap_extensionality.
    intros.
    destruct (heap_lookup loc ([h1 ⊎ [h2 ⊎ h3, H1], H2])) eqn:H_1_23.
    - destruct p.
      destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H_1_23).
      + destruct (heap_lookup loc ([[h1 ⊎ h2, H3] ⊎ h3, H4])) eqn:H_12_3.
        * destruct p.
          destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H_12_3).
          {
            assert (heap_lookup loc ([h1 ⊎ h2, H3]) = Some (l, l0))
              by eauto 2.
            congruence.
          }
          {
            assert (heap_lookup loc ([h1 ⊎ h2, H3]) = Some (l, l0))
              by eauto 2.
            destruct (H4 loc l l0).
            specialize_gen.
            congruence.
          }
        * assert (heap_lookup loc ([h1 ⊎ h2, H3]) = Some (l, l0))
            by eauto 2.
          assert (heap_lookup loc ([[h1 ⊎ h2, H3] ⊎ h3, H4]) = Some (l, l0)) by eauto 2.
          congruence.
      + destruct (heap_lookup loc ([[h1 ⊎ h2, H3] ⊎ h3, H4])) eqn:H_12_3.
        * destruct p.
          destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H_12_3).
          {
            destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H0).
            - assert (heap_lookup loc ([h1 ⊎ [h2 ⊎ h3, H1], H2]) = Some (l1, l2)) by eauto 2.
              congruence.
            - assert (heap_lookup loc ([h2 ⊎ h3, H1]) = Some (l1, l2))
                by eauto 2.
              congruence.
          }
          {
            rewrite -> disjoint_union_sym in H.
            assert (heap_lookup loc ([h3 ⊎ h2, disjoint_sym h2 h3 H1]) = Some (l1, l2)) by eauto 2.
            congruence.
          }
        * destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H).
          {
            assert (heap_lookup loc ([h1 ⊎ h2, H3]) =
                    Some (l, l0)).
            {
              rewrite -> disjoint_union_sym.
              eauto.
            }
            assert (heap_lookup loc ([[h1 ⊎ h2, H3] ⊎ h3, H4]) = Some (l, l0)) by eauto 2.
            congruence.
          }
          {
            rewrite -> disjoint_union_sym in H_12_3.
            assert (heap_lookup loc ([h3 ⊎ [h1 ⊎ h2, H3], disjoint_sym ([h1 ⊎ h2, H3]) h3 H4]) = Some (l, l0)) by eauto 2.
            congruence.
          }
    - assert (heap_lookup loc h1 = None).
      {
        destruct (heap_lookup loc h1) eqn:H_1; try reflexivity.
        destruct p.
        assert (heap_lookup loc ([h1 ⊎ [h2 ⊎ h3, H1], H2]) = Some (l, l0)) by eauto 2.
        congruence.
      }
      assert (heap_lookup loc h2 = None).
      {
        destruct (heap_lookup loc h2) eqn:H_2; try reflexivity.
        destruct p.
        assert (heap_lookup loc ([h2 ⊎ h3, H1]) = Some (l, l0)) by eauto 2.
        rewrite -> disjoint_union_sym in H_1_23.
        assert (heap_lookup loc ([[h2 ⊎ h3, H1] ⊎ h1, disjoint_sym h1 ([h2 ⊎ h3, H1]) H2]) = Some (l, l0)) by eauto 2.
        congruence.
      }
      assert (heap_lookup loc h3 = None).
      {
        destruct (heap_lookup loc h3) eqn:H_2; try reflexivity.
        destruct p.
        assert (heap_lookup loc ([h2 ⊎ h3, H1]) = Some (l, l0)).
        {
          rewrite -> disjoint_union_sym.
          eauto.
        }
        rewrite -> disjoint_union_sym in H_1_23.
        assert (heap_lookup loc ([[h2 ⊎ h3, H1] ⊎ h1, disjoint_sym h1 ([h2 ⊎ h3, H1]) H2]) = Some (l, l0)) by eauto 2.
        congruence.
      }
      assert (heap_lookup loc ([h1 ⊎ h2, H3]) = None).
      {
        destruct (heap_lookup loc ([h1 ⊎ h2, H3])) eqn:H_12; try reflexivity.
        destruct p.
        destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H_12); congruence.
      }
      assert (heap_lookup loc ([[h1 ⊎ h2, H3] ⊎ h3, H4]) = None).
      {
        destruct (heap_lookup loc ([[h1 ⊎ h2, H3] ⊎ h3, H4])) eqn:H_12_3; try reflexivity.
        destruct p.
        destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H_12_3); congruence.
      }
      destruct (heap_lookup loc ([[h1 ⊎ h2, H3] ⊎ h3, H4])) eqn:H_12_3.
      + discriminate.
      + reflexivity.
  Qed.

  Lemma disjoint_implies_disjoint_subheap:
    forall h1 h2 h3 H,
      disjoint ([h1 ⊎ h2, H]) h3 ->
      disjoint h1 h3.
  Proof.
    intros.
    unfolds.
    intros.
    splits.
    - intros.
      destruct (H loc ℓ μ).
      specialize_gen.
      assert (heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ)) by eauto 2.
      eauto.
      Unshelve.
      eauto.
    - intros.
      destruct (H0 loc ℓ μ).
      specialize_gen.
      destruct (heap_lookup loc h1) eqn:H_loc; try reflexivity.
      destruct p.
      assert (heap_lookup loc ([h1 ⊎ h2, H]) = Some (l, l0)) by eauto 2.
      congruence.
  Qed.
  Hint Resolve disjoint_implies_disjoint_subheap.

  Lemma disjoint_self_is_empty:
    forall h,
      disjoint h h ->
      h = emptyHeap.
  Proof.
    intros.
    eapply heap_extensionality.
    intros.
    rewrite -> empty_heap_is_empty.
    destruct (heap_lookup loc h) eqn:H_loc; try reflexivity.
    destruct p.
    unfold disjoint in *.
    destruct (H loc l l0).
    specialize_gen.
    congruence.
  Qed.
  Hint Resolve disjoint_self_is_empty.
  
End MemoryProperties.
