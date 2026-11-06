(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AGif1.v at 95e6f1d72b6 (sha256 973e433a72c9) into lib/B (libreac/fuzz_decode image B, fuzz_decode.asan-ubsan), with its module paths changed only (it states no image numeral; image B's own copy because its Require closure reaches image modules); later the model labels became the model's tags (202260 -> 3, 449860 -> 12). *)
(* The cgif_file instance of the hit-g interface AGif0n.AIface: ARX = ARX_cgif (inst = TFIB_INST /\ AR), AOX = aowned,
   rpre = aregime /\ qmeter, mt = malloc, lpost = qtight, and the depot post dpost_cgif.  The fields come from the
   released route: the view from AGiy (YFiy), the shape from YFi3, the depot callee and the owned set from AGix (YFix),
   the post from AGj1 (YFj1) with YG07.malloc_ok / YG0d.atok_apath_flag for Wf and qtight of the final state. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YFhy AGhy AGis YFi3. From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YGAlloc. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import AllocGcgif AGif0cgif AGiy AGix AGj1. From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import AGif0n. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import AGif2cgif.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order. *)
Set Default Proof Using "All".
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* The post of the depot callee: its answer is a granted one, and the depot's memory facts after the put and the
   constant cells hold at the memory it returns. *)
Definition dpost_cgif (B : asyms) (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (tr : list Z) (z : Z)
(m : word -> option byte) : Prop :=
aok S (KDepot tr) z /\ depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs (w_H W) m) /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) m)) (as_const B ly).

(* The redzone class of the hit-g sizes. *)
Lemma rz_log_range : forall n, 49 <= n <= 64512 -> 1 <= rz_log n <= 6 /\ rz_lo (rz_log n) <= n <= rz_hi (rz_log n).
Proof.
intros n Nrange0. unfold rz_log.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [cbn; lia|]. destruct (Z.leb_spec n 448); [cbn; lia|].
destruct (Z.leb_spec n 3968); [cbn; lia|]. destruct (Z.leb_spec n 16128); [cbn; lia|]. destruct (Z.leb_spec n 32256); [cbn; lia|].
destruct (Z.leb_spec n 64512); [cbn; lia|]. lia.
Qed.

(* The cached chunk's offset is a multiple of 16 (AGiy.off_aligned). *)
Lemma off_split : forall B ly S rd n l off, ARm B ly S rd -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S (chunk_class n)) = l ++ [off] -> off mod 32 = 0 /\ off = 16 * (off / 16).
Proof.
intros B ly S rd n l off HARm Hn0 FP Hcache.
pose proof (AGiy.off_aligned B ly S rd n l off HARm Hn0 FP Hcache) as A32. split; [exact A32|].
apply Z.mod_divide in A32 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 2) * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (a) The view, assembled from AGiy's facts.                                                                       *)
Section v.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte).
Variables (n cl cnt v : Z) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Lemma hview_of_ARm : hview B W ly TFIB_INST mem0 cl cnt v.
Proof.
pose proof (AGiy.inst_cells B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def) as (I1 & I2 & I3).
pose proof (AGiy.cache_vals B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def) as (C1 & C2 & C3).
constructor.
- exact LY.
- exact IMG.
- rewrite (am_tsd _ _ _ _ HARm). exact (ts_tsd B TS).
- exact (AGiy.Hcnt' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
- exact (AGiy.v_facts B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
- exact (am_const B ly S _ HARm).
- exact (conj I1 (conj I2 I3)).
- exact (conj C1 (conj C2 C3)).
- exact (AGiy.unwinding_val B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
- exact (AGiy.junk_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
- exact (AGiy.chunk_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
- exact (AGiy.shadow_vals B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Qed.
End v.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis HD1 : tfib_depot_spec B.

Lemma inst_cgif : forall inst ly S W mem md, ARX_cgif B inst ly S W mem md -> inst_ok inst.
Proof. intros inst ly S W mem md [-> _]. unfold inst_ok, TFIB_INST. lia. Qed.

Lemma view_cgif : forall inst ly S W mem md n l off,
ARX_cgif B inst ly S W mem md -> rpre_cgif S n -> 0 <= n -> from_primary n = true ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
off mod 32 = 0 /\ hview B W ly inst mem (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16).
Proof.
intros inst ly S W mem md n l off [Ei HAR] _ Hn0 FP Hinited Hcache. subst inst.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
destruct (off_split B ly S _ n l off HARm Hn0 FP Hcache) as [A32 Hoff].
split; [exact A32|].
exact (hview_of_ARm B W ly mem n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff).
Qed.

(* (b) Before the pop, malloc still has its tick and its size check; the refill is a no-op on a non-empty cache. *)
Lemma shape_cgif : forall n tr S l off, 0 <= n -> from_primary n = true ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
malloc n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 3 ;; malloc_join_t 12 n tr (chunk_class n)) S.
Proof.
intros n tr S l off Hn0 FP Hinited Hcache.
assert (Hne : pc_chunks (cache S (chunk_class n)) <> []) by (rewrite Hcache; destruct l; discriminate).
rewrite (malloc_primary_eq n tr S FP).
rewrite (bind_ret_l tick _ S tt (set_nev (st_nev S + 1) S) eq_refl).
rewrite (bind_ret_l tick _ S tt (set_nev (st_nev S + 1) S) eq_refl).
cbv beta.
destruct (n <? kMaxAllowedMalloc - kPage).
- rewrite (bind_ret_l (mcheck true 3) _ (set_nev (st_nev S + 1) S) tt (set_nev (st_nev S + 1) S) eq_refl).
rewrite (bind_ret_l (mcheck true 3) _ (set_nev (st_nev S + 1) S) tt (set_nev (st_nev S + 1) S) eq_refl).
cbv beta.
rewrite (bind_ret_l (refill_tree (chunk_class n)) _ (set_nev (st_nev S + 1) S) tt (set_nev (st_nev S + 1) S)
(refill_tree_ready (chunk_class n) (set_nev (st_nev S + 1) S) Hinited Hne)).
reflexivity.
- reflexivity.
Qed.

(* The depot callee, entered with the depot and the constant cells as at mem0 (AGix.depot_call). *)
Lemma depot_cgif : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX_cgif B inst ly S W mem0 md0 -> In tr (as_universe B) ->
(forall x : word, DZONE ly (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
~ DZONE ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
dpost_cgif B inst ly S W tr z mem').
Proof.
intros inst ly S W mem0 md0 tr regs mem md buf [_ HAR] Htr MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md0 (proj1 (proj2 HAR))) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
exact (AGix.depot_call B ly TS LY IMG HTSD HD1 W S mem0 md0 tr regs mem md buf HAR Htr MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES).
Qed.

(* (c) The post: AR of the final state (AGj1.AR_final at the post-tick state) and qtight. *)
Lemma post_cgif : forall inst ly S W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
ARX_cgif B inst ly S W mem0 md0 -> rpre_cgif S n -> n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX -> In tr (as_universe B) ->
49 <= n <= 64512 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
wframe W ly regs0 mem0 tr ->
0 <= jb <= 255 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) (off / 16) + RZ (rz_log n) - 15) 1 jb ->
at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
(fun z m => dpost_cgif B inst ly S W tr z m) odd z W
(mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> n mod 8 <> 0) ->
(exists trc, apath (malloc n tr S) trc
(ck_user (new_chunk (chunk_class n) off n), st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) /\
gflag trc = true) ->
ARX_cgif B inst ly (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
qtight (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z).
Proof.
intros inst ly S W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat [Ei HAR0] [Hev HQ] Hmax Hlive Htr Nrange0 Hinited Hcache
WFR Hjb Hjb_def HR Hodd [trc [HP HG]].
(* Wf and qtight of the final state, from malloc's contract along the granted path. *)
pose proof (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ (proj1 HAR0)) Hev ltac:(lia) Hlive Htr) as AT.
pose proof (atok_apath_flag _ _ _ trc _ AT HP) as MPo. unfold malloc_post in MPo.
destruct MPo as (WF' & _ & _ & _ & _ & QT). pose proof (QT (qmeter_tight _ HQ)) as QT'. clear QT.
(* The post-tick state carries AR at the entry memory. *)
pose proof (AR_tick B ly S W mem0 md0 HAR0 Hev) as HAR.
set (S1 := set_nev (st_nev S + 1) S) in *.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S1 md0 (proj1 (proj2 HAR))) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
assert (Hinited1 : st_cache_inited S1 = true) by exact Hinited.
assert (Hcache1 : pc_chunks (cache S1 (chunk_class n)) = l ++ [off]) by exact Hcache.
destruct (rz_log_range n Nrange0) as [Hkz Nrange].
assert (Hn0 : 0 <= n) by lia.
pose proof (@AGis.casek_sizes n (rz_log n) Hkz Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly S1 _ n l off HARm Hn0 FP Hcache1) as [_ Hoff].
pose proof (AGiy.Hcl' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hcl.
pose proof (AGiy.Hv' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hv.
pose proof (AGiy.Hcnt' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hcnt.
pose proof (AGiy.Hv2' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hv2.
pose proof (AGix.SKPRES B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) (rz_log n) S1 l off tr TS LY IMG HARm Hinited1 Hcache1 eq_refl eq_refl Hoff Hkz Nrange) as HSKpres.
destruct WFR as (Hsp & Htrlen & _ & Hbp & _).
(* The depot post at the entry state gives it at the post-tick state (the tick keeps the depot). *)
assert (HDPOST : forall z0 m, dpost_cgif B inst ly S W tr z0 m ->
aok S1 (KDepot tr) z0 /\ depot_mem_ok B ly (depot_after z0 tr S1) (aview tfibsegs (w_H W) m) /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) m)) (as_const B ly)).
{ intros z0 m (A & D & C). split; [exact A|]. split; [|exact C].
apply (AGix.depot_mem_ok_ext B ly TS LY IMG HTSD (depot_after z0 tr S)); [|exact D].
unfold depot_after. destruct (z0 =? 0); reflexivity. }
split; [|exact QT'].
split; [exact Ei|].
exact (AGj1.AR_final W ly regs0 mem0 md0 n tr (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp Htrlen Hbp (fun z0 m => dpost_cgif B inst ly S W tr z0 m) HSKpres Hkz Nrange
B S1 l off TS HTSD HARm Hinited1 Hcache1 eq_refl eq_refl Hoff HDPOST odd z regs' mem' mat HR Hodd (conj WF' QT') HAR).
Qed.

(* (d) The allocator memory the walk writes is owned (AGix.hit_owned). *)
Lemma owned_cgif : forall inst ly S W mem md n l off odd a,
ARX_cgif B inst ly S W mem md -> rpre_cgif S n -> 49 <= n <= 64512 ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
hit_writes ly n (chunk_class n) (off / 16) (rz_log n) odd a -> aowned B ly S a.
Proof.
intros inst ly S W mem md n l off odd a [_ HAR] _ Nrange0 Hinited Hcache Ra Hodd Hw.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
destruct (rz_log_range n Nrange0) as [Hkz Nrange].
pose proof (@AGis.casek_sizes n (rz_log n) Hkz Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly S _ n l off HARm ltac:(lia) FP Hcache) as [_ Hoff].
exact (AGix.hit_owned B W ly mem n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) (rz_log n) S l off [] TS LY IMG HARm
Hinited Hcache eq_refl eq_refl Hoff Hkz Nrange odd a Ra Hodd Hw).
Qed.
(* An uninitialized per-thread cache is empty (the cache invariant of Wf; YFij.malloc_prim). *)
Lemma uninit_cgif : forall inst ly S W mem md c, ARX_cgif B inst ly S W mem md -> 1 <= c <= 31 ->
st_cache_inited S = false -> pc_chunks (cache S c) = [].
Proof.
intros inst ly S W mem md c [_ HAR] Hc CI. pose proof (proj1 HAR) as HARm.
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) c Hc)) as WC.
rewrite CI in WC. cbv iota in WC. rewrite WC. reflexivity.
Qed.
End b.

Theorem iface_cgif (B : asyms) : TfibSyms B -> tfib_depot_spec B ->
AIface B (fun tr _ => In tr (as_universe B)) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX qtight (dpost_cgif B) 3 12.
Proof.
intros TS HD1. constructor.
- exact (inst_cgif B TS HD1).
- exact (view_cgif B TS HD1).
- exact (shape_cgif B TS HD1).
- exact (depot_cgif B TS HD1).
- intros inst ly S W tr z m H. exact (proj1 H).
- exact (post_cgif B TS HD1).
- exact (owned_cgif B TS HD1).
- exact (uninit_cgif B TS HD1).
Qed.
End a.
