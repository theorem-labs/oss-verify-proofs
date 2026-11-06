(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif1k.v (cold/c-frame-alloc-dgraw-frozen ced28ed2383, file sha256 48748393de25) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: the instance's trace premise is fs's `fun tr S => tr_admit (as_universe B) S tr` (FS-INSTANCE.md 1.4, L; fs's YG07.malloc_ok takes tr_admit), and post_cgif_k takes it too; the proof text is unchanged. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGif1k.v (donor image sha256 64b53ff86172), with its module paths changed, names TfibSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* The cgif_file instance of the k path's interface AGif0n.AIfaceK (0 <= n <= 48, redzone 16): the k twins of
   AGif1.post_cgif and AGif1.owned_cgif.  The post comes from AGjf's AR_transport (the k twin of AGj1's, YFj1) at the
   post-tick state, over the k walk's post at_RETkw (AGj6.at_RET without its fill-byte clause, which AR_transport does not
   read); Wf and qtight of the final state come from YG07.malloc_ok / YG0d.atok_apath_flag as in AGif1.  The owned set is
   AGjb.hit_owned_k (the k twin of AGix.hit_owned, YFix). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AFhy AGhy AGis AFi3.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YGAlloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AllocGcgif AGif0cgif AGiy AGix AGj1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AGif2cgif AGif1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AGj6 AGjc AGjb AGjf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order. *)
Set Default Proof Using "All".
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGjf.AR_final over the k walk's post at_RETkw: AGjf.AR_final destructs AGj6.at_RET and hands its parts to
   AGjf.AR_transport, which reads all of them except the fill-byte clause; at_RETkw is exactly the rest.            *)
Section k.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v jb : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let BPv : Z := bv_unsigned (getr regs0 12).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Variable DPOST : Z -> (word -> option byte) -> Prop.
Hypothesis HSKpres : forall a, AGj6.SKv ly cl v <= a < AGj6.SKv ly cl v + (AGj6.RZ + AGj6.R8v n) / 8 -> apresent (w_H W) mem0 a.
Hypothesis Nrange : 0 <= n <= 48.
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : SegBSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis HDPOST : forall z m, DPOST z m ->
aok S (KDepot tr) z /\ depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs (w_H W) m) /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) m)) (as_const B ly).
Lemma AR_final_kw : forall odd z regs' mem' mat,
at_RETkw W ly regs0 mem0 md0 n cl cnt v jb DPOST odd z W
(mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> AGj6.NPv n mod 8 <> 0) ->
Wf (as_universe B) (st_final S cl l off n tr z) /\ qtight (st_final S cl l off n tr z) ->
AR tfibsegs B ly S W mem0 md0 ->
AR tfibsegs B ly (st_final S cl l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
intros odd z regs' mem' mat HR Hodd MP HAR.
unfold at_RETkw in HR. cbv zeta in HR.
destruct HR as (_ & regs2 & mem2 & mat2 & EC & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
injection EC as E1 E2 E3. subst regs2 mem2 mat2.
destruct (HDPOST z memD DP) as (AOK & DEPD & CSTD).
destruct VALS as (V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
exact (AGjf.AR_transport W ly regs0 mem0 md0 n tr cl cnt v jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp Htrlen Hbp DPOST HSKpres Nrange
B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def
odd z regs' mem' memD mat Hodd MP HAR AOK DEPD CSTD PRD EQD MEQF PRS PRW V3 V4 V5 V6 V7 V8 V9 V10).
Qed.
End k.

Section b.
Variable B : asyms.
Hypothesis TS : SegBSyms B.
Hypothesis HD1 : tfib_depot_spec B.

(* if_post_k: AR of the final state (AR_final_kw at the post-tick state) and qtight (AGif1.post_cgif for k). *)
Lemma post_cgif_k : forall inst ly S W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
ARX_cgif B inst ly S W mem0 md0 -> rpre_cgif S n -> n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX -> tr_admit (as_universe B) S tr ->
0 <= n <= 48 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
wframe W ly regs0 mem0 tr ->
0 <= jb <= 255 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (AGj6.Kv ly (chunk_class n) (off / 16) + AGj6.RZ - 15) 1 jb ->
at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
(fun z m => dpost_cgif B inst ly S W tr z m) odd z W
(mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> AGj6.NPv n mod 8 <> 0) ->
(exists trc, apath (malloc n tr S) trc
(ck_user (new_chunk (chunk_class n) off n), st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) /\
gflag trc = true) ->
ARX_cgif B inst ly (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
qtight (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z).
Proof.
intros inst ly S W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat [Ei HAR0] [Hev HQ] Hmax Hlive Htr Nrange Hinited Hcache
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
assert (Hn0 : 0 <= n) by lia.
pose proof (@AGj6.case0_sizes n Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly S1 _ n l off HARm Hn0 FP Hcache1) as [_ Hoff].
pose proof (AGjc.Hcl' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hcl.
pose proof (AGjc.Hv' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hv.
pose proof (AGjc.Hcnt' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hcnt.
pose proof (AGjc.Hv2' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off TS LY IMG HARm Hn0 FP Hinited1 Hcache1 eq_refl eq_refl Hoff) as Hv2.
pose proof (AGjb.SKPRES B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S1 l off tr TS LY IMG HARm Hinited1 Hcache1 eq_refl eq_refl Hoff Nrange) as HSKpres.
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
exact (AR_final_kw W ly regs0 mem0 md0 n tr (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp Htrlen Hbp (fun z0 m => dpost_cgif B inst ly S W tr z0 m) HSKpres Nrange
B S1 l off TS HTSD HARm Hinited1 Hcache1 eq_refl eq_refl Hoff HDPOST odd z regs' mem' mat HR Hodd (conj WF' QT') HAR).
Qed.

(* if_owned_k: the allocator memory the k walk writes is owned (AGjb.hit_owned_k; AGif1.owned_cgif for k). *)
Lemma owned_cgif_k : forall inst ly S W mem md n l off odd a,
ARX_cgif B inst ly S W mem md -> rpre_cgif S n -> 0 <= n <= 48 ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
0 <= a < 2 ^ 64 -> (odd = true -> AGj6.NPv n mod 8 <> 0) ->
hit_writes_k ly n (chunk_class n) (off / 16) odd a -> aowned B ly S a.
Proof.
intros inst ly S W mem md n l off odd a [_ HAR] _ Nrange Hinited Hcache Ra Hodd Hw.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
pose proof (@AGj6.case0_sizes n Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly S _ n l off HARm ltac:(lia) FP Hcache) as [_ Hoff].
exact (AGjb.hit_owned_k B W ly mem n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S l off [] TS LY IMG HARm
Hinited Hcache eq_refl eq_refl Hoff Nrange odd a Ra Hodd Hw).
Qed.
End b.

Theorem iface_cgif_k (B : asyms) : SegBSyms B -> tfib_depot_spec B ->
AIfaceK B (fun tr S => tr_admit (as_universe B) S tr) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX qtight (dpost_cgif B) 202260 449860.
Proof.
intros TS HD1. constructor.
- exact (post_cgif_k B TS HD1).
- exact (owned_cgif_k B TS HD1).
Qed.
End a.
