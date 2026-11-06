(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the realloc forms of the event-free second allocator instance (suffix cf), over
   c-asan's ReallocP.v (its P forms, instantiated at mt := malloc_cf, ft := free_cf, cpre := acall_pre_cf at a
   fixed Hp, rpre := True, nmax := cf_malloc_max, lmax := LIVE_MAX, areal := amreal). realloc(p, n) also takes
   afree_realizes_cf's premise ~ In (sptr_addr B ly p) Hp (YG0dcf.v:192): the harness shows a hidden head before it
   reallocates (fuzz_realloc's disown, alloc.c:97, before its realloc, alloc.c:98; its own buffers are never hidden),
   so the base is never hidden at the call (h-mani-a8, 2026-10-29 16:12Z). So arealloc_realizes_cf is written out:
   arealloc_realizes_allP at the instance with that premise after a0.
   The ghost set after a realloc is realloc_hp_cf: on success the old block is freed, so its base leaves Hp
   (law (d); with the premise above, remove of an absent base is Hp); on a NULL result the old block stays live and
   Hp is unchanged (law (e)). The old block is a frame
   exception only on success, so on a NULL result the frame exception is the error buffer alone, exactly
   malloc_cf_null_post's.
   realloc_cf_null_post_of_leaf: on a NULL result, the realloc leaf and the refusal witness mt_refused give
   malloc_cf_null_post: the entry step free_cf PNull keeps the regions, caches and chunks (so shape_cf), and
   malloc_cf_null_path at its end state gives the class-full facts. No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfPath ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The leaves.                                                                   *)
(* The ghost set after realloc(p, n) returned q: law (d) on success, law (e) on NULL. *)
Definition realloc_hp_cf (B : asyms) (ly : alayout) (p q : sptr) (Hp : list Z) : list Z :=
match q with
| PNull => Hp
| _ => remove Z.eq_dec (sptr_addr B ly p) Hp
end.

(* rleaf: malloc_leaf_cf's shape. On success the frame exceptions are the new block, the old block (freed) and
   the error buffer before and after; the first min(n_old, n) bytes are copied; the base of the old block
   leaves Hp. On NULL the old block is untouched, Hp is unchanged and the wrapper wrote errno and the OOM byte.
   As in malloc_leaf_cf, the errbuf slot stays placed (xs_placed_cf, YG0ncf.v) at the post layout. *)
Definition realloc_leaf_cf (segs : list Segment) (B : asyms) (ly : alayout) (S : astate) (Hp : list Z)
(W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf segs B ASTACK ly S (realloc_hp_cf B ly p (fst r) Hp) W regs mem md
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
\/ (fst r <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old)
\/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r <> PNull -> forall i, 0 <= i < Z.min n_old n ->
aview segs (w_H W') mem' (sptr_addr B ly' (fst r) + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
xs_placed_cf ly' (snd r) /\
(* errno's four bytes are kept on SUCCESS (the raw form of c-asan's alloc_post_e / dealloc_post_raw_e: a realloc
   success is a granted Allocate and a Deallocate); the refusal arm stores ENOMEM, above. *)
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(* the frame on the RAW memory, at this leaf's exception set (YG0dcf.v malloc_leaf_cf's) *)
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ (fst r <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n_old)
    \/ Exists (in_zr (bv_unsigned x)) (xs_cf ly S ++ xs_cf ly' (snd r))) ->
 mem' x = mem x).

(* The refused arm: malloc_cf_null_post (Hp unchanged, frame exception the error buffer alone, so the old
   block's bytes are framed; errno 12 and OOM byte 1; blocks and chunks unchanged) and the old block still live. *)
Definition realloc_null_leaf_cf (segs : list Segment) (B : asyms) (ly : alayout) (S : astate) (Hp : list Z)
(W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
malloc_cf_null_post segs B ly S Hp W regs mem md n r W' c' /\ In (p, n_old) (blocks (snd r)).

(* ---------------------------------------------------------------------------- *)
(* 2. The realizes forms: ReallocP's P forms at the cf instance, with their argument lists.  *)
(* pc0, the realloc interceptor's trace[0], is the LONG-branch return of its second GetCurrentPc,
   CfImg's cf_pc_realloc_ra0 (fuzz_preset asan 0x53c74, fuzz_reply asan 0x54328; 0 at cgif, whose pins have no realloc interceptor), by name, never typed; pc is the wrapper's entry.
   realloc(p, n) is arealloc_realizes_allP (ReallocP.v:73-82) at the instance, written out, with rpre := True
   dropped and the freed base not hidden, ~ In (sptr_addr B ly p) Hp, after a0 (afree_realizes_cf's place,
   YG0dcf.v:191-192). *)
Definition arealloc_realizes_cf (segs : list Segment) (B : asyms) (Hp : list Z) (pc : Z) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
amreal segs (realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))).

Definition arealloc_null_realizes_cf (segs : list Segment) (B : asyms) (Hp : list Z) (pc : Z) : Prop :=
arealloc_null_realizesP segs (admits (as_universe B)) malloc_cf free_cf
(fun ly S W regs mem md ch => acall_pre_cf segs B ly S Hp W regs mem md ch)
(fun _ _ => True) cf_malloc_max LIVE_MAX
(fun (R : Type) (t : itree astate R) W c Q => amreal segs t W c Q)
(fun ly S W regs mem md n r W' c' => malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c')
pc cf_pc_realloc_ra0.

(* ---------------------------------------------------------------------------- *)
(* 3. The entry step free_cf PNull: a tick and the internal-init flag, nothing else. *)
Lemma cfr_free_null_gpost : forall tr S, gpost (free_cf PNull tr S) (fun r => rcc_same S (snd r)).
Proof.
intros tr S. unfold free_cf, free. apply gp_bind. apply gp_tick. cbn [fst snd].
apply gp_bind. apply gp_get. cbn [fst snd].
apply gp_bind. match goal with |- context [if ?b then _ else _] => destruct b end.
- apply gp_ret. cbn [fst snd]. apply gp_ret. cbn [snd].
  split; [reflexivity | split; [reflexivity | split; reflexivity]].
- apply gp_modify. cbn [fst snd]. apply gp_ret. cbn [snd].
  split; [reflexivity | split; [reflexivity | split; reflexivity]].
Qed.

Lemma cfr_shape_rcc : forall s s', rcc_same s s' -> shape_cf s -> shape_cf s'.
Proof.
intros s s' (E1 & E2 & _ & E4) (H1 & H2 & H3). unfold shape_cf, cache. rewrite E1, E2, E4.
split; [exact H1|]. split; [exact H2|]. exact H3.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The NULL result.                                                              *)
(* The refused realloc's state, world-free (requested by the kit owner, 2026-10-30): free_cf PNull keeps the chunks (rcc_same), the
   refused malloc_cf keeps the blocks and the chunks, its request is a primary one and its class is marked exhausted
   (malloc_cf_null_path, YGcfPath.v). *)
Lemma realloc_cf_refused_state : forall n tr S S2, shape_cf S -> mt_refused malloc_cf free_cf n tr S S2 ->
blocks S2 = blocks S /\ st_chunks S2 = st_chunks S /\ from_primary n = true /\ exh_mem_cf S2 (chunk_class n) = true.
Proof.
intros n tr S S2 Hsh (S1 & t1 & t2 & Hp1 & Hg1 & Hp2 & Hg2).
pose proof (cfr_free_null_gpost tr S t1 (tt, S1) Hp1 Hg1) as R1. cbn [snd] in R1.
pose proof (cfr_shape_rcc S S1 R1 Hsh) as Hsh1.
destruct (malloc_cf_null_path n tr S1 t2 S2 Hsh1 Hp2 Hg2) as (Hb & Hch & Hfp & Hex).
destruct R1 as (_ & _ & Hch1 & _).
assert (Hb1 : blocks S1 = blocks S) by (unfold blocks; rewrite Hch1; reflexivity).
exact (conj (eq_trans Hb Hb1) (conj (eq_trans Hch Hch1) (conj Hfp Hex))).
Qed.

Theorem realloc_cf_null_post_of_leaf : forall segs B ly S Hp W regs mem md ch p nold n tr S2 W2 c2,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
In (p, nold) (blocks S) ->
mt_refused malloc_cf free_cf n tr S S2 ->
realloc_leaf_cf segs B ly S Hp W regs mem md p nold n (PNull, S2) W2 c2 ->
malloc_cf_null_post segs B ly S Hp W regs mem md n (PNull, S2) W2 c2.
Proof.
intros segs B ly S Hp W regs mem md ch p nold n tr S2 W2 c2 Hpre Hin HREF HL.
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 Hpre))) as W0. unfold Wf_cf in W0.
destruct (realloc_cf_refused_state n tr S S2 (shape_cf_of_WfP_cf _ _ _ _ _ W0) HREF) as (Hb & Hch & Hfp & Hex).
destruct HL as (ly' & regs' & mem' & md' & Hc & Hpost & Hr & Hq & _ & Hx & _ & _ & HR).
destruct (Hx eq_refl) as [He Ho].
unfold malloc_cf_null_post. split; [reflexivity|].
exists ly', regs', mem', md'. split; [exact Hc|].
split.
{ destruct Hpost as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
  intros a Ha N1 N2 N3 N4. apply (A6 a Ha N1 N2 N3).
  intros [[Hf _]|[[Hf _]|HX]]; [apply Hf; reflexivity | apply Hf; reflexivity | exact (N4 HX)]. }
split; [exact Hr|]. split; [exact Hq|]. split; [exact Hb|]. split; [exact Hch|].
split; [exact He|]. split; [exact Ho|]. split; [exact Hfp|]. split; [exact Hex|].
intros x N1 N2 N3 N4. apply (HR x N1 N2 N3).
intros [[Hf _]|[[Hf _]|HX]]; [apply Hf; reflexivity | apply Hf; reflexivity | exact (N4 HX)].
Qed.

(* The refused arm with the old block: it is still a live block after the call. *)
Corollary realloc_cf_null_leaf_of_leaf : forall segs B ly S Hp W regs mem md ch p nold n tr S2 W2 c2,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
In (p, nold) (blocks S) ->
mt_refused malloc_cf free_cf n tr S S2 ->
realloc_leaf_cf segs B ly S Hp W regs mem md p nold n (PNull, S2) W2 c2 ->
realloc_null_leaf_cf segs B ly S Hp W regs mem md p nold n (PNull, S2) W2 c2.
Proof.
intros segs B ly S Hp W regs mem md ch p nold n tr S2 W2 c2 Hpre Hin Href HL.
pose proof (realloc_cf_null_post_of_leaf segs B ly S Hp W regs mem md ch p nold n tr S2 W2 c2 Hpre Hin Href HL) as H.
split; [exact H|].
destruct H as (_ & ly' & regs' & mem' & md' & _ & _ & _ & _ & Hb & _). cbn [snd] in Hb |- *. rewrite Hb. exact Hin.
Qed.

(* The errbuf placement after a realloc: the leaf's last conjunct, with the post layout and state. *)
Lemma realloc_leaf_cf_xs_keep : forall segs B ly S Hp W regs mem md ch p n_old n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S ->
realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c' ->
exists ly' regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
ARcf segs B ly' (snd r) (realloc_hp_cf B ly p (fst r) Hp) W' mem' md' /\ xs_placed_cf ly' (snd r).
Proof.
intros segs B ly S Hp W regs mem md ch p n_old n r W' c' _ _ (ly' & regs' & mem' & md' & Hc & (A1 & A2 & _) & _ & _ & _ & _ & HX & _).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact A2|]. split; [exact A1 | exact HX].
Qed.

End R.
