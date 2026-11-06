(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: [malloc_gen_ns] and [malloc_ok_ns] (with the tactics [splits] and
   [ff04_leaf]) copied from proofs/cgif/cgif_file_fuzzer/lib/YG0u.v:13-205, with its module paths changed; that file
   is not relocated to this unit's lib/Reusable.  Everything after them is new. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_decode/lib/YGCallocModel.v (donor image sha256 5973b76807d8), with its module paths changed. *)
(* The allocator-model side of calloc's contract (lib/Reusable/YGCalloc.v).

   calloc(nm, sz) in its in-range arm is the allocator's malloc tree at n = nm * sz (YG00.v:411 [malloc]); c-asan's
   Allocate statement (lib/Reusable/YGAlloc.v:106-117 [alloc_leaf]) hands its caller the reached result [r] together
   with [exists trc, apath (mt n tr S) trc r /\ gflag trc = true]: [r] is the end of a path of the model tree on
   which every kernel answer was granted.  This file proves what the allocator model says about such an [r], at
   n = nm * sz.  No machine code is involved.

   Premises of the model lemmas, and where a caller finds each:
   - [universe_ok U] and [Wf U S]: the unit's allocator relation carries both at U = as_universe B
     (YG0n.v:206-207 am_wf / am_universe of ARm, the first conjunct of AR); [calloc_model_of_AR] below reads them
     off an AR.  [universe_ok U] is the premise of the depot step of the malloc tree (YG07.v:35 depot_put_ok).
   - [aregime S]: the regime conjunct of the call precondition (YG0d.v:228 acall_pre) and of the Allocate
     statement's [rpre] at the unit's instantiation (YGCalloc.v:302 rpre_cgif); a call rule that carries
     [st_nev S < EV_MAX] instead gets it from YG01.v:205 aregime_small.
   - [0 <= nm], [0 <= sz], [nm * sz < MALLOC_MAX], [blocks_bytes S + nm * sz <= LIVE_MAX]: the room premises of
     YGCalloc.v:193 acalloc_realizesP and :233 acalloc04_rule.
   - [In tr U]: the trace premise of the Allocate statement (YGAlloc.v:92).

   cgif refutes a NULL result of a granted malloc path from the model law record (YCbq.v:1587-1605: YG0d.v:527
   ml_malloc_ns gives [fst r = PNull -> ns = false], YG0d.v:176 atok_apath_flag turns the path's flag into [ns],
   YG0d.v:174 last_flag_true closes it).  The same argument is used here, with the law discharged by its released
   proof (cgif YG0u.v:198 malloc_ok_ns, copied below) instead of being assumed: no [model_laws] hypothesis is left.

   THE SPLIT for YGCalloc.v:229-249 [acalloc04_rule]'s post (res = the returned a0, ly2 / S2 = the post's layout
   and state, S2 = snd r):
   - from the model ([calloc_model_post]): the block is not PNull; [st_nev S2 = st_nev Sc + 1] (the journal's event
     count); [frames S2 = frames Sc]; [secs_ext Sc S2] (YCbq.v:843 secs_ext_length turns it into the journal's
     section-count bound); [Wf] of S2; [qtight Sc -> qtight S2]; the block table [blocks S2 = blocks Sc ++
     [(fst r, nm * sz)]] with the new block fresh; [blocks_bytes S2 = blocks_bytes Sc + nm * sz].
   - from the machine walk: the return configuration; the journal's AR, layout_le, wle, same_io, unchanged-memory
     and stack conjuncts; [aregs_preserved]; [getr regs2 10 = w64 res] with [res = sptr_addr B ly2 (fst r)] (the
     Allocate leaf's a0, carried unchanged through calloc's return); the zero bytes; [kept]; the meter.
   - from the two together ([calloc_addr_side]): [4096 <= res] and [ablocks B ly2 S2 = ablocks B lyc Sc ++
     [(res, nm * sz)]].  These are address facts: they need the unit's AR laws (YG0d.v:496 AR_laws: al_layout,
     al_blocks), AR at the call (the walk's precondition), the leaf's [layout_le] and AR at the post (the Allocate
     leaf's alloc_post), and only the block-table equation from the model.
   [calloc04_post_model] packages both for a caller that holds those machine facts. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ------------------------------------------------------------------------------------------------------------
   Copied from cgif YG0u.v:13-205: malloc's model law with the refusal flag, [fst r = PNull -> ns = false]. *)
Local Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Ltac ff04_leaf :=
lazymatch goal with
| |- (fst _ = PNull -> _ = false) /\ _ =>
split; [ cbn [fst snd ck_user ck_beg ck_rz ck_req padd]; first [ intros HPN; discriminate HPN | intros _; reflexivity | intros _; assumption | congruence ] | ]
| |- _ => idtac
end.
Theorem malloc_gen_ns : forall U s n tr,
universe_ok U ->
Wf U s -> regime_ok s -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> tr_admit U s tr ->
atok true (malloc n tr s) (fun ns r => (fst r = PNull -> ns = false) /\ (malloc_post U s n ns r /\ (BigInv s -> BigInv (snd r)) /\ mgrow s n (snd r))).
Proof.
intros U s n tr HU W Hreg Hn Hlive Htr.
pose proof (tr_admit_room U s tr HU (wf_depot _ _ _ _ _ W) Htr) as ADM.
assert (TREG : st_nev s < EV_MAX \/ (BigP s /\ Z.of_nat (length (st_chunks s)) + 1 <= 2 ^ 23)).
{ destruct Hreg as [Hev | ((_ & HP) & _ & _ & HCH & _)]; [left; exact Hev | right; split; [exact HP | exact HCH]]. }
pose proof (WfP_tick' U s W TREG) as W1. set (s1 := set_nev (st_nev s + 1) s) in *.
assert (PREG1 : forall c, 1 <= c <= 31 -> preg s1 c).
{ intros c Hc. destruct Hreg as [Hev | ((CP & _) & HB & _)]; [left; subst s1; cbn; unfold EV_MAX in *; lia | right].
destruct (HB c Hc) as [HB1 HB2]. split; [exact (CP c Hc) | split; [exact HB1 | exact HB2]]. }
assert (HR1 : forall c, 1 <= c <= 31 -> nrecZ s c + 10248 <= 65536).
{ intros c Hc. destruct Hreg as [Hev | (_ & HB & _)]; [| exact (proj2 (HB c Hc))].
change (nrecZ s c) with (nrecZ s1 c). apply (nrecZ_small U 1 1 1 s1 c W1). subst s1. cbn. unfold EV_MAX in *. lia. }
assert (HSEC1 : Z.of_nat (length (st_sec_arr s1)) < kPtrArrayEntriesPerCommit).
{ destruct Hreg as [Hev | (_ & _ & HS & _)]; [| exact HS]. apply (sec_arr_small U 1 1 1 s1 W1). subst s1. cbn. unfold EV_MAX in *. lia. }
assert (D1 : depot_inv U (st_nev s1) (st_depot s1)) by exact (wf_depot _ _ _ _ _ W1).
unfold malloc. apply atok_bind. apply atok_tick. cbn [fst snd]. fold s1.
apply atok_bind. apply atok_mcheck; [apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage, MALLOC_MAX in *; lia|]. cbn [fst snd].
apply atok_bind. destruct (from_primary n) eqn:Hprim.
-
pose proof (primary_geometry n ltac:(lia) Hprim) as (Gc & Gsz & Gmax & G32 & Gpos).
apply atok_bind. eapply atok_mono; [|apply (cache_alloc_okx U 1 1 1 s1 (chunk_class n) true W1 ltac:(lia) ltac:(lia) (PREG1 (chunk_class n) ltac:(lia)))].
intros ns2 [o s2] ((W2 & RO2 & Hi2 & Ho) & DEF2 & BIG2). cbn [fst snd] in DEF2, BIG2 |- *. apply atok_ret; ff04_leaf.
destruct RO2 as (Rck & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev).
destruct o as [off|].
+ destruct Ho as (x & -> & Hx32 & Hxa & Hxm & Hxni).
apply atok_bind. eapply atok_mono; [|apply (depot_put_ok U s2 tr ns2); [rewrite Rdep, Rnev; exact D1 | exact HU | rewrite Rdep, Rnev; exact ADM]].
intros ns3 [[] s3] (d & -> & Hdinv & Hd & ->). cbn [fst snd].
assert (NR : needs_remap (ck_n (mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated)) = false).
{ unfold ck_n. cbn [ck_req]. destruct (needs_remap (req_size n)) eqn:E; [|reflexivity]. exfalso.
rewrite (needs_remap_secondary n ltac:(lia) E) in Hprim. discriminate. }
rewrite NR. apply atok_bind. apply atok_ret; ff04_leaf. cbn [fst snd]. apply atok_bind. apply atok_modify. cbn [fst snd]. apply atok_ret; ff04_leaf.
pose proof (WfP_set_depot U 0 1 1 s2 d W2 Hdinv) as W3.
assert (Hfresh : ~ In (PPrim (region_off (chunk_class n) + x)) (map ck_beg (st_chunks s2))).
{ intros Hin. apply in_map_iff in Hin as (k & Hb & Hk). apply Hxni. unfold class_elems. do 2 (apply in_app_iff; right). apply in_app_iff; left.
unfold chunk_offs. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. rewrite prim_class_region_off by lia. rewrite Z.eqb_refl. left. lia. }
cbn [st_chunks set_depot]. rewrite upd_chunk_fresh by exact Hfresh.
pose proof (WfP_add_prim_chunk U 0 1 1 (set_depot d s2) (region_off (chunk_class n) + x) n W3 ltac:(lia) Hn Hprim) as W4.
rewrite prim_class_region_off in W4 by lia. replace (region_off (chunk_class n) + x - region_off (chunk_class n)) with x in W4 by lia.
cbn [st_chunks set_depot] in W4.
assert (Wfin : Wf U (set_chunks (st_chunks s2 ++ [mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated]) (set_depot d s2))).
{ unfold Wf. apply (WfP_weaken U 0 (1 - 1) 1); [|lia|lia|lia]. apply W4; [reflexivity | exact Hx32 | | exact Hfresh |].
-- apply cls_ok_add_ko; [exact (wf_classes _ _ _ _ _ W3 (chunk_class n) ltac:(lia)) | exact Hxni | split; [lia | exact Hxa] | exact Hxm].
-- rewrite (blocks_bytes_set s2 (set_depot d)) by reflexivity. unfold blocks_bytes. rewrite Rck. subst s1. cbn. exact Hlive. }
split; [split; [exact Wfin | split; [|split; [|split; [|split]]]] | split].
* cbn. rewrite Rnev. subst s1. reflexivity.
* intros r sm E. exists sm. cbn. rewrite Rsecs. subst s1. cbn. auto.
* unfold frames. cbn. rewrite Rfs. subst s1. reflexivity.
* lazy [ck_user ck_beg ck_rz ck_req padd].
assert (EB : forall S', st_chunks S' = st_chunks s2 ++ [mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated] ->
blocks S' = blocks s ++ [(PPrim (region_off (chunk_class n) + x + rz_size n), n)]).
{ intros S' HS. unfold blocks. rewrite HS, Rck, filter_app, map_app. subst s1. reflexivity. }
rewrite EB by reflexivity. split; [reflexivity|].
intros Hin. apply in_map_iff in Hin as ([p m] & Hp & Hb). cbn [fst] in Hp. subst p.
apply In_blocks in Hb as (k & Hk & Hst & Hu & Hr).
unfold ck_user in Hu. destruct (ck_beg k) as [|boff|rr oo|cc' pp'] eqn:Eb; cbn [padd] in Hu; try discriminate.
injection Hu as Hu.
pose proof (prim_user_inj U 0 0 0 s k boff (chunk_class n) x n W Hk Eb ltac:(lia)) as J.
assert (Hx31 : 0 <= x < kFreeArrayOffset).
{ pose proof (mapped_user_bound U 0 1 1 s2 (chunk_class n) W2 ltac:(lia)). pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W2 (chunk_class n) ltac:(lia))).
unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. lia. }
specialize (J Hx31 Hxm ltac:(lia) Hprim eq_refl ltac:(lia)).
apply Hfresh. rewrite Rck. replace (st_chunks s1) with (st_chunks s) by (subst s1; reflexivity).
apply in_map_iff. exists k. rewrite Eb, J. auto.
* apply (qtight_alloc_app s _ (mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated));
[ cbn [st_chunks set_chunks set_depot]; rewrite Rck; subst s1; reflexivity | reflexivity
| cbn [st_qthread set_chunks set_depot]; rewrite Rqt; subst s1; reflexivity
| cbn [st_qglobal set_chunks set_depot]; rewrite Rqg; subst s1; reflexivity ].
*
intros [CP HB]. cbn [snd]. split.
-- intros c' Hc'.
match goal with |- cdef ?S _ = _ => rewrite (cdef_add_prim s2 S (chunk_class n) x n CAllocated c' ltac:(lia) Hx32 eq_refl eq_refl eq_refl eq_refl eq_refl) end.
rewrite (DEF2 c' Hc'). change (cdef s1 c') with (cdef s c'). rewrite (CP c' Hc'). destruct (c' =? chunk_class n); lia.
-- intros c' Hc'. change (reg (set_chunks ?[a] (set_depot ?[b] s2)) c') with (reg s2 c').
exact (BIG2 (CP (chunk_class n) ltac:(lia)) (HR1 (chunk_class n) ltac:(lia)) HB c' Hc').
*
unfold mgrow, hgrow, sec_hulls. cbn [snd st_chunks st_secs st_qthread st_qglobal set_chunks set_depot]. rewrite Rck, Rsecs, Rqt, Rqg, Hprim.
subst s1. cbn [st_chunks st_secs st_qthread st_qglobal set_nev]. rewrite length_app, crw_app. cbn [length crw fold_right cw ck_beg ck_req].
splits; try reflexivity; lia.
+ subst. apply atok_ret; ff04_leaf. cbn -[BigInv].
split; [split; [|split; [|split; [|split; [|split]]]] | split].
* unfold Wf. eapply WfP_weaken; [exact W2 | lia | lia | lia].
* rewrite Rnev. subst s1. reflexivity.
* intros r sm E. exists sm. rewrite Rsecs. subst s1. cbn. auto.
* unfold frames. rewrite Rfs. subst s1. reflexivity.
* unfold blocks. rewrite Rck. subst s1. reflexivity.
* apply (qtight_ext s); [rewrite Rck | rewrite Rqt | rewrite Rqg]; subst s1; reflexivity.
*
intros [CP HB]. split.
-- intros c' Hc'. rewrite (DEF2 c' Hc'). change (cdef s1 c') with (cdef s c'). rewrite (CP c' Hc'). destruct (c' =? chunk_class n); lia.
-- exact (BIG2 (CP (chunk_class n) ltac:(lia)) (HR1 (chunk_class n) ltac:(lia)) HB).
* unfold mgrow, hgrow, sec_hulls. rewrite Rck, Rsecs, Rqt, Rqg, Hprim. subst s1. cbn [st_chunks st_secs st_qthread st_qglobal set_nev]. splits; try reflexivity; lia.
-
pose proof (secondary_geometry n ltac:(lia) Hprim) as (S1 & S2 & S3 & S4 & S5 & S6).
eapply atok_mono; [|apply (sec_alloc_ok U 1 1 1 s1 n true W1 ltac:(lia) Hn Hprim)].
intros ns2 [o s2] Ho. cbn [fst snd] in Ho |- *.
destruct o as [p|].
+ destruct Ho as (res' & -> & -> & Hres & ->).
set (r := length (st_secs s1)). set (sm := mkSec (sec_map_size n) (needed_size n) true).
set (s2 := set_sec_arr _ _).
apply atok_bind. eapply atok_mono; [|apply (depot_put_ok U s2 tr true); [exact D1 | exact HU | exact ADM]].
intros ns3 [[] s3] (d & -> & Hdinv & Hd & ->). cbn [fst snd].
set (k := mkChunk (PSec r kPage) n CAllocated).
assert (Hfresh : ~ In (PSec r kPage) (map ck_beg (st_chunks (set_depot d s2)))).
{ cbn [st_chunks set_depot s2 set_sec_arr set_sec_reserved set_secs]. intros Hin. apply in_map_iff in Hin as (k' & Hb & Hk').
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W1) k' Hk') as [_ CK]. rewrite Hb in CK.
destruct CK as (_ & _ & sm' & Es & _). apply nth_error_lt in Es. subst r. lia. }
assert (TAIL : forall ns4, atok ns4
((modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) k) s0) ;; ret (ck_user k)) (set_depot d s2))
(fun b r0 => atok b (let (_, s') := r0 in IRet (ck_user k, s')) (fun ns r => (fst r = PNull -> ns = false) /\ (malloc_post U s n ns r /\ (BigInv s -> BigInv (snd r)) /\ mgrow s n (snd r))))).
{ intros ns4. apply atok_bind. apply atok_modify. cbn [fst snd]. apply atok_ret; ff04_leaf. apply atok_ret; ff04_leaf.
rewrite upd_chunk_fresh by exact Hfresh.
pose proof (WfP_add_sec U 1 1 1 s1 n d res' W1 ltac:(lia) Hn Hprim ltac:(subst s1; exact Hlive) Hdinv HSEC1 Hres) as W4.
cbn zeta in W4. fold r sm in W4.
assert (ES : set_chunks (st_chunks (set_depot d s2) ++ [k]) (set_depot d s2)
= set_chunks (st_chunks s1 ++ [k]) (set_depot d (set_sec_arr (st_sec_arr s1 ++ [r]) (set_sec_reserved res' (set_secs (st_secs s1 ++ [sm]) s1))))).
{ subst s2 s1. destruct s. reflexivity. }
rewrite ES. split; [split; [|split; [|split; [|split; [|split]]]] | split].
6:{ apply (qtight_alloc_app s _ k); subst s1 k; reflexivity. }
7:{
unfold mgrow, hgrow, sec_hulls. cbn [snd st_chunks st_secs st_qthread st_qglobal set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite Hprim.
subst s1 k. cbn [st_chunks st_secs st_qthread st_qglobal set_nev]. rewrite !length_app, crw_app, sec_hulls_app1. subst sm. cbn [length crw fold_right cw ck_beg sm_len].
splits; try reflexivity; lia. }
6:{
intros [CP HB]. cbn [snd]. split.
- intros c' Hc'. rewrite <- (CP c' Hc'). apply cdef_ext; [reflexivity|]. unfold class_elems, chunk_offs.
cbn [st_chunks st_regions st_cache st_qthread st_qglobal set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
subst s1 k. cbn [st_chunks set_nev]. rewrite flat_map_app. cbn [flat_map ck_beg app]. rewrite app_nil_r. reflexivity.
- intros c' Hc'. exact (HB c' Hc'). }
- unfold Wf. eapply WfP_weaken; [exact W4 | lia | lia | lia].
- subst s1. cbn. reflexivity.
- intros r0 sm0 E0. exists sm0. subst s1. cbn. rewrite nth_error_app1 by (eapply nth_error_lt; exact E0). auto.
- subst s1. reflexivity.
- assert (EB : forall S', st_chunks S' = st_chunks s1 ++ [k] -> blocks S' = blocks s ++ [(PSec r (kPage + rz_size n), n)]).
{ intros S' HS. unfold blocks. rewrite HS, filter_app, map_app. subst s1 k. reflexivity. }
lazy [ck_user ck_beg padd k ck_rz ck_req]. fold k.
rewrite EB by reflexivity. split; [reflexivity|].
intros Hin. apply in_map_iff in Hin as ([p m] & Hp & Hb). cbn [fst] in Hp. subst p.
apply In_blocks in Hb as (k' & Hk' & _ & Hu & _).
unfold ck_user in Hu. destruct (ck_beg k') as [|boff|rr oo|cc' pp'] eqn:Eb; cbn [padd] in Hu; try discriminate.
injection Hu as <- Hoff. apply Hfresh. cbn [st_chunks set_depot s2 set_sec_arr set_sec_reserved set_secs]. subst s1. cbn [st_chunks set_nev].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k' Hk') as [_ CK]. rewrite Eb in CK. destruct CK as (_ & Eoo & _).
apply in_map_iff. exists k'. rewrite Eb, Eoo. auto. }
lazy [ck_n ck_req k]. fold k. destruct (needs_remap (req_size n)) eqn:NR.
* apply atok_bind. apply atok_bind. apply atok_askz.
{ cbn -[Z.mul Z.div Z.add Z.le Z.lt Z.modulo kClearShadowMmapThreshold rz_size req_size sec_map_size needed_size kPage].
unfold needs_remap in NR. apply Z.leb_le in NR.
pose proof (req_size_bounds n ltac:(lia)) as (_ & Q1 & Q2). pose proof (rz_size_bounds n) as [Z1 Z2].
split; [rewrite Z.mul_comm, Z.div_mul by lia; exact NR|].
exists r, (kPage + rz_size n), sm. splits.
- reflexivity.
- subst s2 r s1. cbn [st_secs set_depot set_sec_arr set_sec_reserved set_secs set_nev]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
- reflexivity.
- unfold kPage. lia.
- subst sm. cbn [sm_len].
pose proof (needed_primary_bounds n ltac:(lia)) as (NP1 & _).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)). unfold kPage in *. nia.
- unfold kPage. apply Z.mod_divide; [lia|]. exists (512 + 2 * (rz_size n / 16)). pose proof (Z.div_mod (rz_size n) 16 ltac:(lia)). lia. }
intros z Hz. cbn in Hz. cbn [fst snd]. unfold aGranted. destruct (Z.eqb_spec z 1) as [->|Nz].
-- cbn [progz Z.eqb Pos.eqb]. apply atok_ret; ff04_leaf. apply TAIL.
-- replace (progz _ z) with false by (cbn; destruct Hz as [->| ->]; cbn; congruence). apply atok_spin.
* apply atok_bind. apply atok_ret; ff04_leaf. apply TAIL.
+ destruct Ho as [-> ->]. apply atok_ret; ff04_leaf. cbn -[BigInv].
split; [split; [|split; [|split; [|split; [|split]]]] | split].
* unfold Wf. eapply WfP_weaken; [exact W1 | lia | lia | lia].
* subst s1. reflexivity.
* intros r0 sm0 E0. exists sm0. subst s1. auto.
* subst s1. reflexivity.
* subst s1. reflexivity.
* apply (qtight_ext s); subst s1; reflexivity.
* intros H. exact H.
* unfold mgrow, hgrow, sec_hulls. rewrite Hprim. subst s1. cbn [st_chunks st_secs st_qthread st_qglobal set_nev].
pose proof (sec_map_size_range n Hn) as SMR. pose proof (Z.div_pos (sec_map_size n) 8 ltac:(lia) ltac:(lia)). splits; try reflexivity; lia.
Qed.
Theorem malloc_ok_ns : forall U s n tr,
universe_ok U ->
Wf U s -> aregime s -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> tr_admit U s tr ->
atok true (malloc n tr s) (fun ns r => malloc_post U s n ns r /\ (fst r = PNull -> ns = false)).
Proof.
intros U s n tr HU W Hev Hn Hlive Htr.
eapply atok_mono; [|exact (malloc_gen_ns U s n tr HU W (aregime_ok s Hev) Hn Hlive Htr)]. intros b r (H0 & H & _). split; [exact H | exact H0].
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The live-byte count is the sum of the sizes in the block table, so appending one block of n bytes adds n. *)
Lemma blocks_bytes_blocks : forall s, blocks_bytes s = fold_right (fun b acc => snd b + acc) 0 (blocks s).
Proof.
intros s. unfold blocks_bytes, blocks. induction (st_chunks s) as [|k t IH]; [reflexivity|].
cbn [fold_right filter]. destruct (is_alloc k); cbn [map fold_right snd]; rewrite IH; reflexivity.
Qed.
Lemma blocks_bytes_snoc : forall s s' p n, blocks s' = blocks s ++ [(p, n)] -> blocks_bytes s' = blocks_bytes s + n.
Proof.
intros s s' p n H. rewrite !blocks_bytes_blocks, H, (fold_right_add_app snd). cbn [fold_right snd]. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The malloc tree at calloc's size n = nm * sz.  The hypothesis
   [exists trc, apath (malloc (nm * sz) tr S) trc r /\ gflag trc = true] is, word for word, the conjunct of
   YGAlloc.v:116 [alloc_leaf] at mt = YG00.malloc and n = nm * sz, so a caller of that leaf passes it as is. *)
Lemma calloc_size : forall nm sz, 0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> 0 <= nm * sz < MALLOC_MAX.
Proof. intros nm sz H1 H2 H3. split; [apply Z.mul_nonneg_nonneg; assumption | exact H3]. Qed.

Lemma calloc_model_atok : forall U S nm sz tr,
universe_ok U -> Wf U S -> aregime S ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes S + nm * sz <= LIVE_MAX -> tr_admit U S tr ->
atok true (malloc (nm * sz) tr S) (fun ns r => malloc_post U S (nm * sz) ns r /\ (fst r = PNull -> ns = false)).
Proof.
intros U S nm sz tr HU HW HR Hnm Hsz Hn Hlive Htr.
exact (malloc_ok_ns U S (nm * sz) tr HU HW HR (calloc_size nm sz Hnm Hsz Hn) Hlive Htr).
Qed.

(* Every path of the tree, granted or not, ends one allocation event later: malloc begins with [tick]
   (YG00.v:412) and nothing after it touches the event count (YG01.v:451 malloc_post). *)
Lemma calloc_path_event : forall U S nm sz tr trc r,
universe_ok U -> Wf U S -> aregime S ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes S + nm * sz <= LIVE_MAX -> tr_admit U S tr ->
apath (malloc (nm * sz) tr S) trc r ->
st_nev (snd r) = st_nev S + 1.
Proof.
intros U S nm sz tr trc r HU HW HR Hnm Hsz Hn Hlive Htr Hp.
destruct (atok_apath _ _ _ trc r (calloc_model_atok U S nm sz tr HU HW HR Hnm Hsz Hn Hlive Htr) Hp) as (ns & HQ & _).
destruct r as [p S2]. unfold malloc_post in HQ. destruct HQ as (_ & Hnev & _). exact Hnev.
Qed.

(* The granted path's end satisfies malloc's post at flag true, and is not PNull (the argument of YCbq.v:1592-1605). *)
Lemma calloc_granted_post : forall U S nm sz tr r,
universe_ok U -> Wf U S -> aregime S ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes S + nm * sz <= LIVE_MAX -> tr_admit U S tr ->
(exists trc, apath (malloc (nm * sz) tr S) trc r /\ gflag trc = true) ->
malloc_post U S (nm * sz) true r /\ fst r <> PNull.
Proof.
intros U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr (trc & Hp & Hg).
pose proof (atok_apath_flag _ _ _ trc r (calloc_model_atok U S nm sz tr HU HW HR Hnm Hsz Hn Hlive Htr) Hp) as [HQ HNS].
rewrite (last_flag_true trc Hg) in HQ, HNS.
split; [exact HQ | intros E; discriminate (HNS E)].
Qed.

(* 1. ONE EVENT. *)
Lemma calloc_one_event : forall U S nm sz tr r,
universe_ok U -> Wf U S -> aregime S ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes S + nm * sz <= LIVE_MAX -> tr_admit U S tr ->
(exists trc, apath (malloc (nm * sz) tr S) trc r /\ gflag trc = true) ->
st_nev (snd r) = st_nev S + 1.
Proof.
intros U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr (trc & Hp & _).
exact (calloc_path_event U S nm sz tr trc r HU HW HR Hnm Hsz Hn Hlive Htr Hp).
Qed.

(* 2. NON-NULL. *)
Lemma calloc_nonnull : forall U S nm sz tr r,
universe_ok U -> Wf U S -> aregime S ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes S + nm * sz <= LIVE_MAX -> tr_admit U S tr ->
(exists trc, apath (malloc (nm * sz) tr S) trc r /\ gflag trc = true) ->
fst r <> PNull.
Proof.
intros U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex.
exact (proj2 (calloc_granted_post U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex)).
Qed.

(* 3. BLOCK TABLE: the new block is appended, fresh, and the live bytes grow by n. *)
Lemma calloc_block_table : forall U S nm sz tr r,
universe_ok U -> Wf U S -> aregime S ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes S + nm * sz <= LIVE_MAX -> tr_admit U S tr ->
(exists trc, apath (malloc (nm * sz) tr S) trc r /\ gflag trc = true) ->
blocks (snd r) = blocks S ++ [(fst r, nm * sz)] /\ ~ In (fst r) (map fst (blocks S)) /\
blocks_bytes (snd r) = blocks_bytes S + nm * sz.
Proof.
intros U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex.
destruct (calloc_granted_post U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex) as [HQ Hnn].
destruct r as [p S2]. unfold malloc_post in HQ. destruct HQ as (_ & _ & _ & _ & Hbl & _). cbn [fst snd] in *.
assert (Hbl' : blocks S2 = blocks S ++ [(p, nm * sz)] /\ ~ In p (map fst (blocks S))).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
destruct Hbl' as [E Hf]. split; [exact E|]. split; [exact Hf|]. exact (blocks_bytes_snoc S S2 p (nm * sz) E).
Qed.

(* 4. Everything the model gives for calloc's call-rule post, in one statement. *)
Corollary calloc_model_post : forall U S nm sz tr r,
universe_ok U -> Wf U S -> aregime S ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes S + nm * sz <= LIVE_MAX -> tr_admit U S tr ->
(exists trc, apath (malloc (nm * sz) tr S) trc r /\ gflag trc = true) ->
fst r <> PNull /\ Wf U (snd r) /\ st_nev (snd r) = st_nev S + 1 /\ secs_ext S (snd r) /\
frames (snd r) = frames S /\
blocks (snd r) = blocks S ++ [(fst r, nm * sz)] /\ ~ In (fst r) (map fst (blocks S)) /\
blocks_bytes (snd r) = blocks_bytes S + nm * sz /\
(qtight S -> qtight (snd r)).
Proof.
intros U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex.
destruct (calloc_block_table U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex) as (Hbl & Hf & Hbb).
destruct (calloc_granted_post U S nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex) as [HQ Hnn].
destruct r as [p S2]. unfold malloc_post in HQ. destruct HQ as (HW2 & Hnev & Hsecs & Hfrs & _ & Hqt). cbn [fst snd] in *.
split; [exact Hnn|]. split; [exact HW2|]. split; [exact Hnev|]. split; [exact Hsecs|]. split; [exact Hfrs|].
split; [exact Hbl|]. split; [exact Hf|]. split; [exact Hbb | exact Hqt].
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The machine side of the split: what the walk must supply, and how it meets the model's block table. *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The model premises [universe_ok] and [Wf] at U = as_universe B, read off the unit's allocator relation. *)
Lemma calloc_model_of_AR : forall segs B ly S W mem md,
AR segs B ly S W mem md -> universe_ok (as_universe B) /\ Wf (as_universe B) S.
Proof.
intros segs B ly S W mem md H.
exact (conj (am_universe _ _ _ _ (proj1 H)) (am_wf _ _ _ _ (proj1 H))).
Qed.

(* The address side (YCbq.v:1597-1615, cgif's malloc call rule): with AR at the call, the post's layout_le and AR at
   the post (all from the machine walk) and the model's block-table equation, the block table at addresses gains
   exactly (sptr_addr B ly2 p, n), and that address is at least 4096. *)
Lemma calloc_addr_side : forall segs B lyc ly2 Sc S2 W mem md W2 mem2 md2 p n,
AR_laws segs B ->
AR segs B lyc Sc W mem md -> layout_le (length (st_secs Sc)) lyc ly2 -> AR segs B ly2 S2 W2 mem2 md2 ->
blocks S2 = blocks Sc ++ [(p, n)] ->
ablocks B ly2 S2 = ablocks B lyc Sc ++ [(sptr_addr B ly2 p, n)] /\ 4096 <= sptr_addr B ly2 p.
Proof.
intros segs B lyc ly2 Sc S2 W mem md W2 mem2 md2 p n LAWS HAR Hly HAR2 Hbl.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly) as (Eab & _ & _).
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(sptr_addr B ly2 p, n)]).
{ unfold ablocks in *. rewrite Hbl, map_app, Eab. reflexivity. }
split; [exact Eab2|].
assert (Hnew : In (sptr_addr B ly2 p, n) (ablocks B ly2 S2)).
{ rewrite Eab2. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ n HAR2 Hnew) as (_ & H4096 & _). exact H4096.
Qed.

(* Items 1-3 and the address side together, in the order of acalloc04_rule's post: the model premises come from AR
   at the call ([calloc_model_of_AR]); [layout_le] and AR at the post are the Allocate leaf's. *)
Corollary calloc04_post_model : forall segs B lyc ly2 Sc W mem md W2 mem2 md2 nm sz tr r,
AR_laws segs B ->
AR segs B lyc Sc W mem md -> aregime Sc ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> blocks_bytes Sc + nm * sz <= LIVE_MAX -> tr_admit (as_universe B) Sc tr ->
(exists trc, apath (malloc (nm * sz) tr Sc) trc r /\ gflag trc = true) ->
layout_le (length (st_secs Sc)) lyc ly2 -> AR segs B ly2 (snd r) W2 mem2 md2 ->
fst r <> PNull /\ st_nev (snd r) = st_nev Sc + 1 /\ frames (snd r) = frames Sc /\ secs_ext Sc (snd r) /\
Wf (as_universe B) (snd r) /\ (qtight Sc -> qtight (snd r)) /\
blocks_bytes (snd r) = blocks_bytes Sc + nm * sz /\
4096 <= sptr_addr B ly2 (fst r) /\
ablocks B ly2 (snd r) = ablocks B lyc Sc ++ [(sptr_addr B ly2 (fst r), nm * sz)].
Proof.
intros segs B lyc ly2 Sc W mem md W2 mem2 md2 nm sz tr r LAWS HAR HR Hnm Hsz Hn Hlive Htr Hex Hly HAR2.
destruct (calloc_model_of_AR segs B lyc Sc W mem md HAR) as [HU HW].
destruct (calloc_model_post (as_universe B) Sc nm sz tr r HU HW HR Hnm Hsz Hn Hlive Htr Hex)
as (Hnn & HW2 & Hnev & Hsecs & Hfrs & Hbl & _ & Hbb & Hqt).
destruct (calloc_addr_side segs B lyc ly2 Sc (snd r) W mem md W2 mem2 md2 (fst r) (nm * sz) LAWS HAR Hly HAR2 Hbl)
as [Eab H4096].
split; [exact Hnn|]. split; [exact Hnev|]. split; [exact Hfrs|]. split; [exact Hsecs|]. split; [exact HW2|].
split; [exact Hqt|]. split; [exact Hbb|]. split; [exact H4096 | exact Eab].
Qed.
End a.
