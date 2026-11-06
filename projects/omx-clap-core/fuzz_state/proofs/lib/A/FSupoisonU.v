(* fuzz_state's user poison for ANY set U of live heads (POISON-U lane, a Theorem Labs lane; lane table
   (internal path)). New file over lib/A/FSupoison.v (a Theorem Labs lane's FMupoison.v,
   a working branch 7ba11794c88, relocated). fm needs U = [] at every allocator call (design/POISON.md:13-17,
   101-104); fuzz_state calls malloc / realloc / free and the runtime walks with OTHER heads poisoned (grow's
   realloc(v->keys) while keys[0]'s head is live; pj_free frees in any order: (internal path) section 5, P1-P4).

   This file:
   - P2 (proved): ARU is invariant under a permutation of U, so a head is unpoisoned wherever it sits in U
     (ARU_unpoison_any; FSupoison.ARU_unpoison_step removes the head of the list only).
   - P1 / P3 (stated): the donor's leaf and runtime contracts (lib/Reusable/YG0d.v:233-427) in ARU form for any U:
     each is the donor text with AR / acall_pre / ecall_pre read through ARU (the memory with U's shadow bytes read as
     0, U in the whole user granules of live blocks, those bytes reading 0xf7); every other clause verbatim.
   - The U = [] forms are COROLLARIES (X_realizes_of_U : X_realizesU -> X_realizes), so the donor's statements and
     fm's stay byte-identical.
   - fs_heads + ARU_free_outside (proved): afree_realizesU's range premise is DISCHARGED at fs's free sites from
     fuzz_free's own unpoison of the block's head (no premise carried up).
   The realloc leaf in ARU form (arealloc_realizesU) sits over a Theorem Labs lane's realloc model (FSH_ReallocModel.v).
   strcmp / strlen (and chk_ok_of_ARU) are RUNTIME-strings' (FSbz_str.v / FSH_Rt), over this ARU.
   The __asan_report_* calls get NO contract: every walk must PROVE each instrumented check's report branch untaken
   from its ARU range premises (range_addressable / shadow_hull_vis on aview mem, ranges outside U); this is checked
   per walk, not assumed. STATEMENTS + the P2 / corollary / free-outside proofs; no Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* P2: U up to permutation.                                                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma in_ush_perm : forall U U' s, Permutation U U' -> FSP.in_ush U s = FSP.in_ush U' s.
Proof.
intros U U' s P. unfold FSP.in_ush. induction P as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn [existsb].
- reflexivity.
- rewrite IH. reflexivity.
- rewrite !Bool.orb_assoc, (Bool.orb_comm (_ && _) (_ && _)). reflexivity.
- rewrite IH1, IH2. reflexivity.
Qed.

Lemma unpoison_perm : forall U U' mem w, Permutation U U' -> FSP.unpoison U mem w = FSP.unpoison U' mem w.
Proof. intros U U' mem w P. unfold FSP.unpoison. rewrite (in_ush_perm U U' _ P). reflexivity. Qed.

Lemma zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. unfold zdisjoint. intros a b H. lia. Qed.

Lemma pairwise_zdisjoint_perm : forall U U', Permutation U U' -> pairwise zdisjoint U -> pairwise zdisjoint U'.
Proof.
intros U U' P. induction P as [|x l l' P IH|x y l|l l' l'' _ IH1 _ IH2]; cbn [pairwise].
- tauto.
- intros [F H]. split; [|exact (IH H)]. exact (Permutation_Forall P F).
- intros [Fy [Fx H]]. apply Forall_cons_iff in Fy as [Dyx Fy].
  split; [constructor; [exact (zdisjoint_sym _ _ Dyx) | exact Fx]|]. split; [exact Fy | exact H].
- intros H. exact (IH2 (IH1 H)).
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* AR depends only on the memory's values. *)
Lemma AR_ext : forall ly S W mem mem' md, AR segs B ly S W mem md -> (forall w, mem' w = mem w) ->
  AR segs B ly S W mem' md.
Proof.
intros ly S W mem mem' md HAR E.
apply (al_frame _ _ LAWS ly S W mem md mem' md HAR).
- intros a _ _. apply FSP.aview_at. apply E.
- intros a Hv. rewrite (FSP.aview_at segs _ mem' mem a (E _)). exact Hv.
- reflexivity.
- reflexivity.
- reflexivity.
- intros a _ _. apply E.
Qed.

Lemma upoison_ok_perm : forall ly S U U', Permutation U U' -> FSP.upoison_ok B ly S U -> FSP.upoison_ok B ly S U'.
Proof.
intros ly S U U' P [F PW]. split; [exact (Permutation_Forall P F) | exact (pairwise_zdisjoint_perm U U' P PW)].
Qed.

(* ARU with U permuted. *)
Lemma ARU_perm : forall ly S U U' W mem md, Permutation U U' ->
  FSP.ARU segs B ly S U W mem md -> FSP.ARU segs B ly S U' W mem md.
Proof.
intros ly S U U' W mem md P (HAR & OK & PO). split; [|split].
- apply (AR_ext ly S W (FSP.unpoison U mem)); [exact HAR|]. intros w. apply unpoison_perm. symmetry. exact P.
- exact (upoison_ok_perm ly S U U' P OK).
- intros s Hs. apply PO. rewrite (in_ush_perm U U' s P). exact Hs.
Qed.

(* __asan_unpoison_memory_region(h, 16) for a head anywhere in U (fs's out-of-order unpoison, pj_free). *)
Lemma ARU_unpoison_any : forall ly S U1 U2 W mem md h mem1 md1 lo hi,
  FSP.ARU segs B ly S (U1 ++ (h, 16) :: U2) W mem md ->
  ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
     aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
  (forall a, lo <= a < hi -> aview segs (w_H W) mem1 a <> None) ->
  aview segs (w_H W) mem1 (shadow_addr h) = Some 0 -> aview segs (w_H W) mem1 (shadow_addr h + 1) = Some 0 ->
  m_vmmaps md1 = m_vmmaps md -> m_vm_lazy md1 = m_vm_lazy md -> eager_used md1 = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem1 (w64 a) = mem (w64 a)) ->
  FSP.ARU segs B ly S (U1 ++ U2) W mem1 md1.
Proof.
intros ly S U1 U2 W mem md h mem1 md1 lo hi H.
apply (ARU_perm ly S _ ((h, 16) :: U1 ++ U2) W mem md) in H; [|symmetry; apply Permutation_middle].
exact (FSP.ARU_unpoison_step segs B LAWS ly S (U1 ++ U2) W mem md h mem1 md1 lo hi H).
Qed.

(* fs's shape of U (fuzz/alloc.c own / disown): every user-poisoned range is the 16-byte head at the START of a live
   block of at least 16 bytes. fuzz_malloc / fuzz_realloc poison (b, 16) for the block b they just got, the harness's
   raw __wrap_malloc / __wrap_free blocks are never heads, and removal keeps the shape. *)
Definition fs_heads (ly : alayout) (S : astate) (U : list (Z * Z)) : Prop :=
  forall r, In r U -> snd r = 16 /\ exists m, In (fst r, m) (ablocks B ly S) /\ 16 <= req_size m.

Lemma pairwise_In2 : forall {X} (R : X -> X -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
intros X R l. induction l as [|z t IH]; intros x y P Hx Hy NE; [destruct Hx|].
destruct P as [F P]. rewrite Forall_forall in F.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- exfalso. exact (NE eq_refl).
- left. exact (F y Hy).
- right. exact (F x Hx).
- exact (IH x y P Hx Hy NE).
Qed.

(* The block a free (or realloc) releases holds no range of U once its own head is gone: the discharge of
   afree_realizesU's range premise at fs's free sites (fuzz_free unpoisons (p - 16, 16) first: A 0x82d74 before
   `j __wrap_free` 0x82e1c, B 0x82e00 before 0x82ea8; fuzz_realloc A 0x82a98 before `jal __wrap_realloc` 0x82b30,
   B 0x82c54 before 0x82cec). *)
Lemma ARU_free_outside : forall ly S U W mem md P n,
  FSP.ARU segs B ly S U W mem md -> fs_heads ly S U ->
  In (P, n) (ablocks B ly S) -> ~ In (P, 16) U ->
  forall r, In r U -> fst r + snd r <= P \/ P + req_size n <= fst r.
Proof.
intros ly S U W mem md P n H FH HP NIN r Hr.
destruct (FH r Hr) as (E16 & m & Hm & M16).
destruct r as [q s]. cbn [fst snd] in *. subst s.
assert (NE : q <> P) by (intros ->; exact (NIN Hr)).
pose proof (al_blocks _ _ LAWS ly S W (FSP.unpoison U mem) md P n (FSP.ARU_AR _ _ _ _ _ _ _ _ H) HP)
  as (_ & _ & _ & _ & _ & PW & _).
assert (I1 : In (q, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (q, m)); exact Hm).
assert (I2 : In (P, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (P, n)); exact HP).
destruct (pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (NE E')))
  as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia.
Qed.
End p.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* P1 / P3: the donor's contracts (YG0d.v) in ARU form, any U.                                                      *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* acall_pre (YG0d.v:233) over the memory with U's shadow bytes read as 0, plus U's own invariants. *)
Definition acall_preU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
  acall_pre segs B ly S W regs (FSP.unpoison U mem) md ch /\ FSP.upoison_ok B ly S U /\ FSP.upoisoned segs W mem U.

(* acall_post (YG0d.v:242) likewise, with the same U at the return (U's heads lie in other live blocks). *)
Definition acall_postU (stk : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (E : Z -> Prop)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  acall_post segs B stk ly S W regs (FSP.unpoison U mem) md E ly' S' W' regs' (FSP.unpoison U mem') md' /\
  FSP.upoison_ok B ly' S' U /\ FSP.upoisoned segs W' mem' U.

(* malloc_leaf (YG0d.v:251) in ARU form. *)
Definition malloc_leafU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (n : Z) (r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
  exists ly' regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    acall_postU ASTACK ly S U W regs mem md
      (fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
      ly' (snd r) W' regs' mem' md' /\
    getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
    qtight (snd r).

(* amalloc_realizes (YG0d.v:261) for any U. *)
Definition amalloc_realizesU : Prop :=
  forall ly S U W regs mem md n ch,
    acall_preU ly S U W regs mem md ch ->
    getr regs 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
    In (call_trace ly (pc_malloc_ra0 (as_code B)) regs ch) (as_universe B) \/ st_nev S < EV_MAX ->
    amreal segs (malloc n (call_trace ly (pc_malloc_ra0 (as_code B)) regs ch) S) W
      (cfg_at segs (pc_wrap_malloc (as_code B)) regs mem md)
      (malloc_leafU ly S U W regs mem md n).

(* free_leaf (YG0d.v:269) in ARU form. *)
Definition free_leafU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (r : unit * astate) (W' : world segs) (c' : config)
    : Prop :=
  exists ly' regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    acall_postU ASTACK ly S U W regs mem md
      (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
    qtight (snd r).

(* afree_realizes (YG0d.v:277) for any U whose ranges lie outside the freed block (free rewrites that block's whole
   shadow; fs's fuzz_free disowns the block's own head before free). *)
Definition afree_realizesU : Prop :=
  forall ly S U W regs mem md p n ch,
    acall_preU ly S U W regs mem md ch ->
    (p = PNull \/ In (p, n) (blocks S)) ->
    (forall r, In r U -> fst r + snd r <= sptr_addr B ly p \/ sptr_addr B ly p + req_size n <= fst r) ->
    getr regs 10 = w64 (sptr_addr B ly p) ->
    In (call_trace ly (pc_free_ra0 (as_code B)) regs ch) (as_universe B) \/ st_nev S < EV_MAX ->
    amreal segs (free p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S) W
      (cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
      (free_leafU ly S U W regs mem md p n).

#[local] Abbreviation ARU := (FSP.ARU segs B).
#[local] Abbreviation ecall_preU := (FSP.ecall_preU segs B).

(* astack_malloc_realizes (YG0d.v:292) for any U. *)
Definition astack_malloc_realizesU (cid : Z) : Prop :=
  forall ly S U W regs mem md pos S',
    ecall_preU ly S U W regs mem md ->
    count_cid cid (frames S) < fs_frames cid ->
    apath (stack_malloc cid S) [] (PFake cid pos, S') ->
    SRr segs W (cfg_at segs (pc_stack_malloc (as_code B) cid) regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md',
         c' = cfg_at segs (raZ regs) regs' mem' md' /\
         ARU ly S' U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         getr regs' 10 = w64 (frame_addr ly cid pos) /\
         zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
         rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
         (forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
            aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
         (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* aintrin_realizes (YG0d.v:325) for any U. *)
Definition aintrin_realizesU (op : memop) (pc : Z) : Prop :=
  forall ly S U W regs mem md d x n,
    ecall_preU ly S U W regs mem md ->
    getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
    dest_ok segs B ly S W regs mem d n -> amem_range d n ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
    (match op with
     | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
               range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
     | OSet => True end) ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md',
         c' = cfg_at segs (raZ regs) regs' mem' md' /\
         ARU ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         getr regs' 10 = w64 d /\
         (forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
            match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
            aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
         (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* amemcmp_realizes (YG0d.v:344) for any U. *)
Definition amemcmp_realizesU (pc : Z) : Prop :=
  forall ly S U W regs mem md x y n,
    ecall_preU ly S U W regs mem md ->
    getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
    0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
    src_ok segs W regs mem x n -> src_ok segs W regs mem y n -> amem_range x n -> amem_range y n ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
         c' = cfg_at segs (raZ regs) regs' mem' md' /\
         ARU ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         getr regs' 10 = v /\
         (v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
         (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* abcmp_realizes (YG0d.v:360) for any U. *)
Definition abcmp_realizesU (pc : Z) : Prop :=
  forall ly S U W regs mem md x y n,
    ecall_preU ly S U W regs mem md ->
    ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
    getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
    0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
    src_ok segs W regs mem x n -> src_ok segs W regs mem y n ->
    (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
    (forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
    amem_range x n -> amem_range y n ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
         c' = cfg_at segs (raZ regs) regs' mem' md' /\
         ARU ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         getr regs' 10 = v /\
         (v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
         (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* amemchr0_realizes (YG0d.v:391) for any U. *)
Definition amemchr0_realizesU (pc : Z) : Prop :=
  forall ly S U W regs mem md x n k,
    ecall_preU ly S U W regs mem md ->
    getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
    0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
    first_byte segs W mem x n 0 k ->
    src_ok segs W regs mem x (k + 1) -> amem_range x (k + 1) ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
    shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
    (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
    rom_view segs W mem ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md',
         c' = cfg_at segs (raZ regs) regs' mem' md' /\
         ARU ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         getr regs' 10 = w64 (x + k) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
         (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* astrnlen_realizes (YG0d.v:409) for any U. *)
Definition astrnlen_realizesU (pc : Z) : Prop :=
  forall ly S U W regs mem md x n k,
    ecall_preU ly S U W regs mem md ->
    ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
    getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
    0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
    first_byte segs W mem x n 0 k ->
    src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
    shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
    (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
    rom_view segs W mem ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md',
         c' = cfg_at segs (raZ regs) regs' mem' md' /\
         ARU ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         getr regs' 10 = w64 k /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
         (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The U = [] forms are corollaries: each any-U contract gives the donor's (YG0d.v) text unchanged.                *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma acall_preU_nil : forall ly S W regs mem md ch,
  acall_pre segs B ly S W regs mem md ch -> acall_preU ly S [] W regs mem md ch.
Proof. intros ly S W regs mem md ch H. split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs. Qed.

Lemma amalloc_realizes_of_U : amalloc_realizesU -> amalloc_realizes segs B.
Proof.
intros HU ly S W regs mem md n ch Hpre Hn Hnr Hlive Htr.
eapply amreal_mono; [|exact (HU ly S [] W regs mem md n ch (acall_preU_nil _ _ _ _ _ _ _ Hpre) Hn Hnr Hlive Htr)].
intros r W' c' (ly' & regs' & mem' & md' & E & (POST & _ & _) & R10 & QT).
exists ly', regs', mem', md'. exact (conj E (conj POST (conj R10 QT))).
Qed.

Lemma afree_realizes_of_U : afree_realizesU -> afree_realizes segs B.
Proof.
intros HU ly S W regs mem md p n ch Hpre Hp Hr Htr.
eapply amreal_mono; [|exact (HU ly S [] W regs mem md p n ch (acall_preU_nil _ _ _ _ _ _ _ Hpre) Hp
  (fun r Hin => False_ind _ Hin) Hr Htr)].
intros r W' c' (ly' & regs' & mem' & md' & E & (POST & _ & _) & QT).
exists ly', regs', mem', md'. exact (conj E (conj POST QT)).
Qed.

Lemma ecall_preU_of_pre : forall ly S W regs mem md, ecall_pre segs B ly S W regs mem md -> ecall_preU ly S [] W regs mem md.
Proof. intros ly S W regs mem md H. exact (proj2 (FSP.ecall_preU_nil segs B ly S W regs mem md) H). Qed.

Lemma astack_malloc_realizes_of_U : forall cid, astack_malloc_realizesU cid -> astack_malloc_realizes segs B cid.
Proof.
intros cid HU ly S W regs mem md pos S' Hpre Hc Hp.
eapply SRr_mono; [exact (HU ly S [] W regs mem md pos S' (ecall_preU_of_pre _ _ _ _ _ _ Hpre) Hc Hp)|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HARU & R). split; [exact EW|].
exists regs', mem', md'. split; [exact Ec|]. split; [exact (proj1 HARU) | exact R].
Qed.

Lemma aintrin_realizes_of_U : forall op pc, aintrin_realizesU op pc -> aintrin_realizes segs B op pc.
Proof.
intros op pc HU ly S W regs mem md d x n Hpre. intros.
eapply SRr_mono; [apply (HU ly S [] W regs mem md d x n (ecall_preU_of_pre _ _ _ _ _ _ Hpre)); assumption|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HARU & R). split; [exact EW|].
exists regs', mem', md'. split; [exact Ec|]. split; [exact (proj1 HARU) | exact R].
Qed.

Lemma amemcmp_realizes_of_U : forall pc, amemcmp_realizesU pc -> amemcmp_realizes segs B pc.
Proof.
intros pc HU ly S W regs mem md x y n Hpre. intros.
eapply SRr_mono; [apply (HU ly S [] W regs mem md x y n (ecall_preU_of_pre _ _ _ _ _ _ Hpre)); assumption|].
intros W' c' _ (EW & regs' & mem' & md' & v & Ec & HARU & R). split; [exact EW|].
exists regs', mem', md', v. split; [exact Ec|]. split; [exact (proj1 HARU) | exact R].
Qed.

Lemma abcmp_realizes_of_U : forall pc, abcmp_realizesU pc -> abcmp_realizes segs B pc.
Proof.
intros pc HU ly S W regs mem md x y n Hpre. intros.
eapply SRr_mono; [apply (HU ly S [] W regs mem md x y n (ecall_preU_of_pre _ _ _ _ _ _ Hpre)); assumption|].
intros W' c' _ (EW & regs' & mem' & md' & v & Ec & HARU & R). split; [exact EW|].
exists regs', mem', md', v. split; [exact Ec|]. split; [exact (proj1 HARU) | exact R].
Qed.

Lemma amemchr0_realizes_of_U : forall pc, amemchr0_realizesU pc -> amemchr0_realizes segs B pc.
Proof.
intros pc HU ly S W regs mem md x n k Hpre. intros.
eapply SRr_mono; [apply (HU ly S [] W regs mem md x n k (ecall_preU_of_pre _ _ _ _ _ _ Hpre)); assumption|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HARU & R). split; [exact EW|].
exists regs', mem', md'. split; [exact Ec|]. split; [exact (proj1 HARU) | exact R].
Qed.

Lemma astrnlen_realizes_of_U : forall pc, astrnlen_realizesU pc -> astrnlen_realizes segs B pc.
Proof.
intros pc HU ly S W regs mem md x n k Hpre. intros.
eapply SRr_mono; [apply (HU ly S [] W regs mem md x n k (ecall_preU_of_pre _ _ _ _ _ _ Hpre)); assumption|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HARU & R). split; [exact EW|].
exists regs', mem', md'. split; [exact Ec|]. split; [exact (proj1 HARU) | exact R].
Qed.
End u.
