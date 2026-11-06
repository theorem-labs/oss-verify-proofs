(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif1m.v (a working branch ced28ed2383, file sha256 a8ba029fc832) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 6 image addresses moved by code-verified function pairs (6 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: the instance's trace premise is fs's `fun tr S => tr_admit (as_universe B) S tr` (FS-INSTANCE.md 1.4, L; fs's YG07.malloc_ok takes tr_admit), and post_miss_cgif / post_miss_k_cgif / depot_miss_cgif take it at the entry state S0; depot_miss_cgif gives AGif1.depot_cgif its areq_ok premise by YG01.tr_admit_len (the depot premise does not read the state; FS-INSTANCE.md 2.1, if_depot_miss). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/AGif1m.v; 95 of its 188 lines of code are new or changed and 352 lines of the source are left out. *)
(* fuzz_state image A: the ARU (any-user-poison) form of AGif1m.refill_cgif, the callee field [if_refill] of AIfaceM at
   fs's instance ARX_ARU (a Theorem Labs lane, 2026-10-29).

   rule 24: no function proved (kind: instance lift - an ARU refill contract composed into the record field's shape;
   no new walk).

   WHAT THIS FILE PROVES.  [fs_refill_U] is lib/A/FSReallocAG.v's hypothesis (H4r) H_refill_U (FSReallocAG.v:287-288)
   at image A's instances (AGif2cgif.AImg_cgif, so im_segs = tfibsegs; AGif0cgif.AGImg_cgif; rtree := AFl1.refill_tree,
   the tree AGif1m.iface_cgif_m uses):
     forall B, TfibSyms B -> tfib_refill_specURaw B -> forall Up,
       FSupoisonARXmA.if_refill_t B (ARX_ARU im_segs B TFIB_INST Up) (aowned B) FS_rpreA qtight AFl1.refill_tree.
   [fs_refill_U_closed] is the same statement without the premise: FSupoisonAllocRt.tfib_refill_okU gives it once
   FSupoisonAllocR.refill_leafU carries the raw conjunct (a working branch 8593de5d3aa).
   FS_rpreA (lib/A/FSRealloc_rmodel.v:63) is AllocGcgif.rpre_cgif (lib/A/AllocGcgif.v:25) by its text,
   aregime S /\ qmeter S.  Its proof [refill_aru] is AGif1m.refill_cgif's (lib/A/AGif1m.v:163-261) line for line; the
   changed steps:
   - AR is read on FSupoison.unpoison Up of each memory (FSupoison.ARU).  AR at the call-time memory (AGif1m.v:190-210)
     moves across the unpoisoning pointwise (FSupoisonARXm.aview_unpoison_eq, unpoison_eq, apresent_unpoison_fwd);
   - the refill's pre is FSupoisonAllocR.refill_preU: refill_pre at the unpoisoned call-time memory (AGif1m.v:211-225),
     upoison_ok at the post-tick state (the tick keeps every block), and Up's shadow bytes at 247 in the call-time
     memory (they lie in the shadow band, below the stack window, where the call-time memory reads as the entry
     memory: FSupoisonARXm.ush_band);
   - the post's aview frame off errno: the leaf's frame is on the unpoisoned memories; a byte that is not owned at the
     entry state is off Up (Up's shadow bytes are owned: FSupoison.ush_facts), so there both memories read as the real
     ones (FSupoisonARXm.aview_unpoison_off);
   - the post's presence: the refill's stack window is off Up (FSupoisonARXm.stack_off_ush,
     apresent_unpoison_bwd);
   - errno (AGif1m.v:247-255) and the raw conjunct (AGif1m.v:258) read the premise's raw frame, as AGif1m reads
     CLrefillR's (RAWF, AGif1m.v:230).
   No step reads as_dhash: the lift takes TfibSyms only (ts_tp, ts_errno), so it carries no
   (forall t, as_dhash B t = tfib_dhash t) premise.

   THE PREMISE [tfib_refill_specURaw] (the gap; a Theorem Labs lane owns the walk).  if_refill_t's post is AGif0n.rleaf
   (lib/Reusable/AGif0n.v:254-269).  It carries a raw-memory frame (:266-267: mem' x = mem x off the owned bytes and
   the callee's stack window) and an aview frame that does not exclude errno (:263-264).
   - AR side: CLrefill0.tfib_refill_specR (lib/A/CLrefill0.v:35-38).  Its leaf refill_leafR (:27-34) is refill_leaf
     plus the raw frame; CLrefillR.tfib_refill_okR proves it, and AGif1m.refill_cgif reads it at AGif1m.v:230 (RAWF),
     :247-255 (errno, through rw_not_hidden) and :258 (the raw conjunct).
   - U side: FSupoisonAllocRt.tfib_refill_okU (lib/A/FSupoisonAllocRt.v:889) proves FSupoisonAllocR.tfib_refill_specU
     (lib/A/FSupoisonAllocR.v:385-388).  Its leaf refill_leafU (:379-384) is FSupoisonU.acall_postU
     (lib/A/FSupoisonU.v:171-176): YG0d.acall_post's aview frame (lib/Reusable/YG0d.v:243-251) on the unpoisoned
     memories, which excludes ascratch (YG0d.v:216-217: the stack window and the errno cells), and no raw frame.
   - The walk has the raw frame and drops it: the B2 leaf FSupoisonAllocRt.LEAF_B2U destructs at_RET2's raw clause
     MEQ' (lib/A/FSupoisonAllocRt.v:497) and concludes refill_leafU; the B3 leaves conclude LEAFQU :=
     FSupoisonAllocR.refill_leafU (lib/A/FSupoisonAllocRf.v:930).
   [tfib_refill_specURaw] is tfib_refill_specU with refill_leafU's text (FSupoisonAllocR.v:381-384) plus, as the LAST
   conjunct inside its `exists regs' mem' md'`, the raw frame of CLrefill0.refill_leafR (CLrefill0.v:33-34) on the
   machine's (real) memory: the text of (internal path) (refill_leafU, a Theorem Labs lane 19:00Z),
   character for character.  Once FSupoisonAllocR.refill_leafU carries that conjunct, tfib_refill_specURaw B is
   FSupoisonAllocR.tfib_refill_specU B by conversion, and FSupoisonAllocRt.tfib_refill_okU closes it by one exact.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0m YG08.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFhy AGhy AGis AFi3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif AGif0cgif AGiy AGix AGj1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import CLrefill0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AB13 AFkq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YFfk.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif AGif1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
(* the AR twin (its image helpers T_zone_of, rw_not_hidden, apresent_aview_some), the ARU kit, the record premise *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AGif1m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocR FSupoisonARXm FSupoisonARXmA.
(* the U refill walk (a Theorem Labs lane), for the closure [fs_refill_U_closed] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonAllocRt.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSRealloc_rmodel.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require ImgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module XM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonARXm.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The missing U-raw refill contract: FSupoisonAllocR.refill_leafU / tfib_refill_specU (FSupoisonAllocR.v:379-388)*)
(*    with the raw frame of CLrefill0.refill_leafR (CLrefill0.v:33-34) on the machine's memory as the last conjunct. *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section s.
Variable B : asyms.

Definition refill_leafURaw (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (c : Z) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B RSTACK ly S U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    getr regs' 10 = w64 (match pc_chunks (cache (snd r) c) with [] => 0 | _ => 1 end) /\
    (forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ (spZ regs - RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x).

Definition tfib_refill_specURaw : Prop :=
  forall ly S U W regs mem md c,
    FAR.refill_preU B ly S U W regs mem md c ->
    amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs mem md) (refill_leafURaw ly S U W regs mem md c).
End s.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. if_refill at ARX_ARU: AGif1m.refill_cgif's text with ARX_cgif := ARX_ARU tfibsegs B TFIB_INST Up.             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis HRU : tfib_refill_specURaw B.

Lemma refill_aru : forall Up inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
XM.ARX_ARU tfibsegs B TFIB_INST Up inst ly S0 W mem0 md0 -> FSRealloc_rmodel.FS_rpreA S0 n -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 A_REFILL_RET -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 TFIB_TP ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal tfibsegs (refill_tree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at tfibsegs A_Refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf (XM.ARX_ARU tfibsegs B TFIB_INST Up) (aowned B) qtight inst ly S0 n (chunk_class n) W regs mem
     (with_vm_backing (m_vm_lazy md0) mat md0)).
Proof.
intros Up inst ly S0 W mem0 md0 n sp0 regs mem mat [Ei HARU0] [Hev HQ] Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW1 PRES1
SP R1 R3 R4 R10 R11 R12 R13.
pose proof HARU0 as (HAR0 & OK0 & PO0).
pose proof (proj1 HAR0) as HARm0. pose proof (am_layout _ _ _ _ HARm0) as LY.
pose proof (img_cover_of_ledger ly S0 md0 (proj1 (proj2 HAR0))) as IMG.
pose proof (lo_top ly LY) as (_ & _ & _ & K2 & _ & _ & K1).
pose proof (AGif1m.T_zone_of ly LY IMG) as ZT.
pose proof (primary_geometry n Hn0 FP) as (Gc & _).
set (cl := chunk_class n) in *. assert (Hcl : 1 <= cl <= 31) by lia.
set (S1 := set_nev (st_nev S0 + 1) S0).
set (md1 := with_vm_backing (m_vm_lazy md0) mat md0).
pose proof (AR_tick B ly S0 W (FSP.unpoison Up mem0) md0 HAR0 Hev) as HAR1. fold S1 in HAR1.
pose proof (WfP_tick _ S0 (am_wf _ _ _ _ HARm0) Hev) as WfP1. fold S1 in WfP1.
(* AR at the call-time memory read unpoisoned (AGif1m.v:190-210, each step through the pointwise unpoisoning) *)
assert (HARc : AR tfibsegs B ly S1 W (FSP.unpoison Up mem) md1).
{ apply (AR_frame_law_ok tfibsegs B ly S1 W (FSP.unpoison Up mem0) md0 (FSP.unpoison Up mem) md1 HAR1).
  - intros a Ha Ho. apply (XM.aview_unpoison_eq tfibsegs (w_H W) Up mem0 mem a).
    apply AG1; [exact Ha|]. intros Hst. apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison Up mem0) md0 a HAR1); [lia | exact Ho].
  - intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
    assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
    assert (AV : forall m, aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
    rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
    destruct (Z_lt_le_dec a' (sp0 - AFSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a' sp0) as [H2|H2]].
    2:{ apply AGif1m.apresent_aview_some. apply XM.apresent_unpoison_fwd. apply PRES1. lia. }
    all: rewrite (XM.aview_unpoison_eq tfibsegs (w_H W) Up mem0 mem a' (AG1 a' Ha' ltac:(lia))); exact Hv.
  - apply m_vmmaps_wvb.
  - apply m_vm_lazy_wvb.
  - apply eager_used_wvb.
  - intros a Ha Hx.
    assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
    assert (HB : kLowShadowBeg <= a < kHighMemBeg) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    pose proof (zone3_apart_hsh _ _ a ZT HB) as TH.
    unfold YG0d.w64, YG0n.w64 in *. apply XM.unpoison_eq. apply RAW1; rewrite unsigned_lit_small by exact Ha'.
    + clear - HB K1 Hlo. unfold kHighMemBeg, AFSTACK in *. lia.
    + clear - TH. unfold t_unwinding, kThreadObjSize in *. lia. }
(* the refill's pre over U (FSupoisonAllocR.refill_preU): AGif1m.v:211-225 at the unpoisoned memory, U's invariants *)
assert (PRE : FAR.refill_preU B ly S1 Up W regs mem md1 cl).
{ unfold FAR.refill_preU. split; [|split].
  - pose proof HAR0 as (_ & _ & [BUD _] & _).
    unfold refill_pre. rewrite SP. unfold raZ. rewrite R1, R3, R4, R10, R11, R12, R13, (ts_tp B TS).
    split; [exact HARc|].
    split; [unfold abudget in *; unfold S1; change (sec_live_bytes (set_nev (st_nev S0 + 1) S0)) with (sec_live_bytes S0);
      change (sec_hulls (set_nev (st_nev S0 + 1) S0)) with (sec_hulls S0); cbn [st_nev set_nev]; unfold EV_A in *; lia|].
    split; [split; [pose proof (wf_prim_ev _ _ _ _ _ WfP1) as PE; lia|];
      split; [exact (aregime_preg_tick S0 cl Hev Hcl) | exact (aregime_mid_tick S0 Hev)]|].
    split; [split; [apply qtight_qloose; exact (qmeter_tight _ HQ) | apply (rroom_tick S0); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (qmeter_room _ HQ)]]|].
    split; [apply ret_ok_even; reflexivity|]. split; [unfold w64, YG0d.w64, YG0n.w64, A_REFILL_RET; rewrite unsigned_lit_small by lia; lia|].
    split; [clear - Hal; replace (sp0 - 176) with (sp0 + (-11) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
    split; [clear - Hlo; unfold AFSTACK, RSTACK in *; lia|]. split; [lia|].
    split; [intros a Ha; apply XM.apresent_unpoison_fwd; apply PRES1; clear - Ha; unfold AFSTACK, RSTACK in *; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite Ei; reflexivity|]. split; [reflexivity|]. split; [exact Hcl | exact Hmiss].
  - (* the tick keeps every block *)
    exact OK0.
  - (* Up's shadow bytes lie below kHighMemBeg, so below Allocate's window, where mem reads as mem0 *)
    intros s Hs. pose proof (XM.ush_band tfibsegs B ly S0 Up W mem0 md0 s HARU0 Hs) as (_ & L2 & Rs).
    rewrite (AG1 s Rs); [exact (PO0 s Hs)|]. clear - L2 K1 Hlo. lia. }
pose proof (HRU ly S1 Up W regs mem md1 cl PRE) as RR.
pose proof (AFkq.refill_tree_apost (as_universe B) 1 1 1 S1 cl WfP1 Hcl ltac:(lia) (aregime_preg_tick S0 cl Hev Hcl)) as APOST.
pose proof (YFfk.amreal_apost tfibsegs _ _ W _ _ APOST RR) as RR2.
eapply amreal_mono; [|exact RR2].
intros r W' c' [(_ & RO & CI) (regs' & mem' & md' & Ec & ((AR' & _ & WLE & RP & IO & FR & PR) & OK' & PO') & A0 & RAWF)].
destruct RO as (Rck & _ & _ & _ & Rqt & Rqg & _).
assert (ENO : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> 0x9f000 <= a < 0x5fd000) by (unfold TFIB_ERRNO; lia).
(* a byte not owned at the entry state is off Up: Up's shadow bytes are owned (FSupoison.ush_facts) *)
assert (OFFO : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S0 a -> XM.off_ush Up a).
{ intros a Ra NO. unfold XM.off_ush. rewrite (Z.mod_small a (2 ^ 64) Ra).
  destruct (FSP.in_ush Up a) eqn:E; [|reflexivity]. exfalso.
  exact (NO (proj1 (FSP.ush_facts tfibsegs B ly S0 Up W mem0 md0 a HARU0 E))). }
unfold rleaf. exists ly, regs', mem', md'.
split; [exact Ec|].
split; [exact (conj Ei (conj AR' (conj OK' PO')))|].
split; [exact (qtight_ext S0 (snd r) Rck Rqt Rqg (qmeter_tight _ HQ))|].
split; [exact CI|].
split; [unfold blocks_bytes; rewrite Rck; reflexivity|].
split; [apply layout_le_refl|].
split; [exact WLE|].
split; [exact RP|].
split; [exact IO|].
split.
{ intros a Ra NO NO' NS. unfold ImgBaseAG.RSTACK, AFl1.RSTACK in *.
  change (aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
  destruct (Z_le_gt_dec TFIB_ERRNO a) as [E1|E1]; [destruct (Z_lt_ge_dec a (TFIB_ERRNO + 4)) as [E2|E2]|].
  - (* errno: never hidden, so the raw frame gives the view *)
    pose proof (AGif1m.rw_not_hidden W a (ENO a (conj E1 E2))) as Hh.
    assert (Hh' : w_H W' (Z_to_bv 64 a) = false) by (destruct (w_H W' (Z_to_bv 64 a)) eqn:E; [rewrite (WLE _ E) in Hh; discriminate | reflexivity]).
    assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ra).
    unfold aview, mbyte, mrestrict. rewrite Hh, Hh'.
    rewrite (RAWF (Z_to_bv 64 a)); [reflexivity | rewrite Ex; exact NO | rewrite Ex; exact NO' | rewrite Ex; unfold AFl1.RSTACK; exact NS].
  - (* off errno: the leaf's frame on the unpoisoned memories, which read as the real ones off Up *)
    rewrite <- (XM.aview_unpoison_off tfibsegs (w_H W') Up mem' a (OFFO a Ra NO)),
      <- (XM.aview_unpoison_off tfibsegs (w_H W) Up mem a (OFFO a Ra NO)).
    apply (FR a Ra NO NO'); [|intros []]. unfold ascratch. intros [X|X]; [unfold AFl1.RSTACK in X; exact (NS X)|]. rewrite (ts_errno B TS) in X. lia.
  - rewrite <- (XM.aview_unpoison_off tfibsegs (w_H W') Up mem' a (OFFO a Ra NO)),
      <- (XM.aview_unpoison_off tfibsegs (w_H W) Up mem a (OFFO a Ra NO)).
    apply (FR a Ra NO NO'); [|intros []]. unfold ascratch. intros [X|X]; [unfold AFl1.RSTACK in X; exact (NS X)|]. rewrite (ts_errno B TS) in X. lia. }
split; [intros x NO NO' NS; exact (RAWF x NO NO' NS)|].
split.
{ (* the refill's stack window is off Up, so presence on the unpoisoned memory is presence on the real one *)
  intros a Ha. pose proof (PR a Ha) as Pa.
  apply (XM.apresent_unpoison_bwd (w_H W') Up mem' a); [|exact Pa].
  apply (XM.stack_off_ush tfibsegs B ly S0 Up W mem0 md0 a HARU0).
  clear - Ha SP Hlo Hhi. unfold AFSTACK, ImgBaseAG.RSTACK, AFl1.RSTACK in *. lia. }
exact A0.
Qed.
End b.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. FSReallocAG's (H4r) H_refill_U, from the U-raw refill contract.                                               *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Theorem fs_refill_U : forall B, TfibSyms B -> tfib_refill_specURaw B -> forall Up,
  FSupoisonARXmA.if_refill_t B (XM.ARX_ARU ImgBase.im_segs B TFIB_INST Up) (aowned B) FSRealloc_rmodel.FS_rpreA qtight
    AFl1.refill_tree.
Proof. intros B TS HRU Up. exact (refill_aru B TS HRU Up). Qed.

(* The closure: at a working branch 8593de5d3aa, FSupoisonAllocR.refill_leafU ends with RAW-TEXT.md's
   refill conjunct (FSupoisonAllocR.v:386-388), so tfib_refill_specURaw B is FSupoisonAllocR.tfib_refill_specU B by
   conversion and FSupoisonAllocRt.tfib_refill_okU (FSupoisonAllocRt.v:902) gives it. *)
Theorem fs_refill_U_closed : forall B, TfibSyms B -> forall Up,
  FSupoisonARXmA.if_refill_t B (XM.ARX_ARU ImgBase.im_segs B TFIB_INST Up) (aowned B) FSRealloc_rmodel.FS_rpreA qtight
    AFl1.refill_tree.
Proof. intros B TS Up. exact (fs_refill_U B TS (FSupoisonAllocRt.tfib_refill_okU B TS) Up). Qed.
End a.

About fs_refill_U.
Print Assumptions fs_refill_U.
About fs_refill_U_closed.
Print Assumptions fs_refill_U_closed.
