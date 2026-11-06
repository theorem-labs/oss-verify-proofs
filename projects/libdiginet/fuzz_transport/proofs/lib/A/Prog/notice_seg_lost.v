(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v for libreac/fuzz_grant's program walk: the listing's names are gsym, PALib names fuzz_grant.asan's objects and the wrappers' 4-byte jumps, and fuzz_grant's image bound; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy (proofs/libreac/fuzz_grant/lib/A/Prog/GrantPaLib.v, file sha256 1750b9b228be; donor not released) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed. *)
(* Modified by Theorem Labs, 2026-10: image B's twin of this unit's lib/A/Prog/DecodePaLib.v, in the shape of proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBPaLib.v (file sha256 73c9e12166f6; donor not released): the names are dbsym's (the wrappers' free and malloc entries are DB___interceptor_trampoline_free and DB___interceptor_trampoline_malloc); PALib names fuzz_decode.asan-ubsan's objects of lib/B/Prog/DecodeBAddr.v and lib/B/AsanCells.v: the shadow-base GOT word is object 1 (GOT_CELL_K 0x992e8) and its cell object 14 (CELL_K 0xa1338), the side-stack flag's GOT word object 0 (GOT_UAR 0x99340) and its cell object 15 (UAR 0xa1340); the two cells are one object later than image A's 13 and 14 because image B's slots load one more object (object 13, 0x103c8); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/DgnTransportBPaLib.v; 9 of its 34 lines of code are new or changed and 475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/TransportGRunB.v, with its module paths and module names changed; 398 of its 427 lines of code are new or changed and 5 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_lib.v, with its module paths and module names changed; 367 of its 442 lines of code are new or changed and 352 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/notice_seg_desk.v; 263 of its 361 lines of code are new or changed and 344 lines of the source are left out. *)
(* notice_seg_lost: the arm of notice for a notice of kind N_ACK_LOST (0x835e8), which calls check_inflight_lost and
   clears M.fly.on:
     +0x70 .. +0x74    a0 = p (`mv a0, a1`), `jal check_inflight_lost` (0x852e4) from sp - 16, return address +0x78;
     the call          check_inflight_lost is a leaf (check_inflight_lost_cg.v, read through DgnTransportCg.v
                       transport_leaf_at): its premises at the call memory (the notice's counter and retry bytes, the
                       world relation at the raw memory, its frame, the runtime cells, its footprint), its post turned
                       into the donor journal at the return by DgnTransportLeafb.v decode_leafb_journal, inside the G
                       journal by TransportGCg.v gx_call_leaf; the symbolic state rebuilt after it (jafter_call_keep_pi,
                       the frame kept);
     +0x78 .. +0x80    a0 = the auipc value of M.fly.on (A_HI 73), `sw zero, -1072(a0)`, `j` to the epilogue;
     +0x1b4 .. +0x1bc  the epilogue (ra restored, sp + 16) and `ret`.
   The world's only change is M.fly.on = 0 (notice_m's N_ACK_LOST case, nt_m_lost). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base notice_seg_lib notice_seg_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  DgnTransportLeafb DgnTransportCgRun LeafCgKit AsanKA check_state_wake_c check_inflight_lost_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module NtlLB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
Module NtlCR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportCgRun.
Module NtlCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module NtlKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module NtlCW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_c.
Module NtlLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_lost_c.
Module NtlAC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module NtlEF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The bytes a notice of kind N_ACK_LOST writes: M.fly.on's four. *)
Lemma ntl_wr_lost : forall Bw n a, TI.n_kind n = TC.N_ACK_LOST -> notice_wr Bw n a -> TA_M + 96 <= a < TA_M + 100.
Proof.
  intros Bw n a Hk Hw.
  unfold notice_wr, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hk, Hw.
  unfold twa_fld, TW.A_M_fly_on, TW.OFF_M in Hw.
  destruct Hw as [(E & _) | [(E & _) | [(E & Ha) | [(E & _) | [(E & _) | (E & _)]]]]]; lia.
Qed.

Lemma ntl_le_byte_small : forall v (m j : nat), 0 <= YO0f.le_byte v m j < 256.
Proof. intros v m j. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

(* w bytes of the notice at p + k, read from its garr8 array: u_at NB k w. *)
Lemma ntl_valw : forall (mm : word -> option byte) p (NB : list byte) k (w : nat),
  garr8 tfibsegs mm p (map DSpec.bz NB) -> length NB = 72%nat -> 0 <= k -> k + Z.of_nat w <= 72 ->
  val_mem tfibsegs mm (p + k) w (TW.u_at NB k w).
Proof.
  intros mm p NB k w HG HL Hk Hkw j Hj.
  assert (Hjl : (Z.to_nat k + j < length (map DSpec.bz NB))%nat) by (rewrite length_map; lia).
  pose proof (garr8_mbyte tfibsegs mm p (map DSpec.bz NB) (Z.to_nat k + j) HG Hjl) as Hb.
  replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hb. f_equal. f_equal.
  assert (Hls : length (TW.sub NB k w) = w) by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
  unfold TW.u_at. rewrite <- Hls at 2.
  rewrite (tw_le_byte_ble (TW.sub NB k w) j (Z_to_bv 8 0)) by lia.
  rewrite (tw_nth_sub NB k w j (Z_to_bv 8 0)) by lia.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

(* Every payload byte of the harness globals lies in a loaded segment, so no world hides it. *)
Lemma ntl_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. apply (NtlCR.decode_vis_seg W).
  apply (NtlCR.decode_covers_img TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) x); [vm_compute; reflexivity | lia].
Qed.

(* The world relation at the view is the world relation at the raw memory (the leaf's csw_view). *)
Lemma ntl_tw_csw : forall (W : world tfibsegs) mem Bw,
  tw_at TMAP_A (aview tfibsegs (w_H W) mem) Bw -> tw_at TMAP_A (NtlCW.csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  unfold NtlCW.csw_view. rewrite (NtlCR.decode_aview_mrd W mem x (ntl_hull_vis W x (TMAP_A_hull x Hx))).
  reflexivity.
Qed.

(* RNG_W W holds on a range of the hull. *)
Lemma ntl_rng_hull : forall (W : world tfibsegs) lo len, TG.G_HARNESS_LO <= lo -> lo + len <= TG.G_HARNESS_HI ->
  NtlEF.rng (NtlCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2.
  apply (NtlCR.decode_rng W); [unfold TG.G_HARNESS_LO in *; lia | unfold TG.G_HARNESS_HI in *; lia |].
  intros b Hb. apply ntl_hull_vis. lia.
Qed.

(* The shadow of n bytes at p + k inside one granule is one byte. *)
Lemma ntl_sh1 : forall p k n, p mod 8 = 0 -> 0 <= k -> 0 < n -> k mod 8 + n <= 8 ->
  NtlAC.shadow_addr (p + k + n - 1) - NtlAC.shadow_addr (p + k) + 1 = 1.
Proof.
  intros p k n Hp Hk Hn Hkn. unfold NtlAC.shadow_addr.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.div_mod k 8 ltac:(lia)) as Dk.
  pose proof (Z.mod_pos_bound k 8 ltac:(lia)) as Mk.
  assert (E1 : (p + k + n - 1) / 8 = (p + k) / 8).
  { replace (p + k + n - 1) with ((p / 8 + k / 8) * 8 + (k mod 8 + n - 1)) by lia.
    replace (p + k) with ((p / 8 + k / 8) * 8 + k mod 8) by lia.
    rewrite !Z.div_add_l by lia.
    rewrite (Z.div_small (k mod 8 + n - 1) 8) by lia. rewrite (Z.div_small (k mod 8) 8) by lia. reflexivity. }
  lia.
Qed.

(* M.fly.on's region (write-only, based at the auipc value A_HI 73): its 4 bytes are writable bytes of G. *)
Lemma ntl_fly_ok : forall (W : world tfibsegs) m E,
  bv_unsigned (ew E (A_HI 73)) = TA_M + 96 + 1072 ->
  region_ok tfibsegs E (mrestrict (w_H W) m) nt_reg_fly.
Proof.
  intros W m E Uo.
  unfold nt_reg_fly, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Uo. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|].
  split; [|apply Forall_nil].
  intros o Ho. apply (gx_rw_writable tfibsegs TG.G_HARNESS (TA_M + 96 + 1072 + o) G_HARNESS_rw).
  apply nt_inG_M. lia.
Qed.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma nt_path_lost : @nt_path fx rc B MT TC.N_ACK_LOST NT_LOST.
Proof.
unfold nt_path.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI HElo HEd SHOK HJ KA.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ0 Hra Hra4 Hgp Htp H11 Hsp16
  Hlo Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_lost timg_A Fr Bw n Bw' Ek Hm) as [HML HBw].
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (HElo 2%nat ltac:(lia)); rewrite (nt_E_reg regs NB Bw 2%nat 2%bv eq_refl); reflexivity).
pose proof (nt_E_atom regs NB Bw 0%nat ltac:(lia)) as E32q. cbn [Nat.add nth nt_vals] in E32q.
assert (E32e : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HElo 32%nat ltac:(lia)); exact E32q).
assert (U11e : bv_unsigned (ew E 11) = p).
{ rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), H11.
  apply unsigned_lit_small. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
(* run 1, +0x70 .. +0x74: a0 = p, `jal check_inflight_lost` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with context [restrict _ ?mz] =>
  assert (KA1 : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA HFr HG);
     intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
     nt_win Hin Hx ltac:(rewrite ?Usp in Hx; lia));
  rename mz into ms0 end.
clear HF HFr HG.
(* the notice and the facts at the call memory *)
pose proof Hrd as (Hv & HRA & Hhull & Ham & Hq0 & Hq63).
assert (Hvis : forall a, p <= a < p + 72 -> w_H W (Z_to_bv 64 a) = false).
{ intros a Ha. specialize (Hv a Ha). destruct (aview segs (w_H W) memc a) as [z|] eqn:Ez; [|contradiction].
  exact (NtlLB.decode_leafb_aview_vis W memc a z Ez). }
assert (Happ : forall a, p <= a < p + 72 -> NtlAC.app_mem a).
{ intros a Ha. unfold NtlAC.app_mem, NtlAC.LOWMEM_END, NtlAC.HIGHMEM_BEG, NtlAC.APPMEM_END.
  unfold amem_range in Ham. destruct Ham as [Hm1 | Hm1]; [left | right]; lia. }
assert (HNB1 : garr8 segs (mrestrict (w_H W) (ms_mem ms0)) p (map DSpec.bz NB)) by
  (apply (nt_garr8_keep W memc _ (nt_Wn regs) p _ KA1 HNB);
   intros a Ha; rewrite length_map, HNBL in Ha; split;
   [lia | unfold nt_Wn, decode_off_win, NTC_SIZE in *; lia]).
assert (HSH : forall x, p <= x < p + 72 -> 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ nt_Wn regs (SHADOW_OFF + x / 8)).
{ intros x Hx. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  unfold nt_Wn, SHADOW_OFF. split; lia. }
pose proof (nt_ra_kept W memc (ms_mem ms0) p 72 (nt_Wn regs) HRA KA1 HSH) as HRA1.
assert (HtwM : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms0)) Bw).
{ apply (nt_tw_keep W memc (ms_mem ms0) Bw (nt_Wn regs) Htw KA1).
  intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
(* the registers at the call *)
nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 p) Q10 ltac:(cbn [sv_denot]; rewrite U11e, Z.add_0_r; reflexivity).
nt_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 16)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
nt_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9100)) R1 ltac:(apply codeptr_val; exact HEI).
nt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (HElo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3%nat 3%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Hgp).
nt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (HElo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4%nat 4%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Htp).
assert (SPU : bv_unsigned (YK11.getr (ms_regs ms0) (Z_to_bv 5 2)) = spZ regs - 16)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (GSP : spZ (ms_regs ms0) = spZ regs - 16) by exact SPU.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 NtlLC.CHECK_INFLIGHT_LOST) mm rom) mdx) Q) end.
(* the call of check_inflight_lost (a leaf), in the G journal *)
eapply SRr_bind.
{ eapply (gx_call_leaf (fx := fx) (rc := rc) (SK := tfib_sink_head) segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0
    own lyc Sc W (ms_mem ms0) md1 k _ (YK11.getr (ms_regs ms0) 1) _ HJ).
  intros memS HJS.
  eapply (NtlLB.decode_leafb_journal (fx := fx) (SK := tfib_sink_head) B LAWS W (ms_regs ms0) (ms_mem ms0) STK sp0
    FP ly S W0 memS md0 own lyc Sc md1 k (spZ regs - 16 - sp0) NtlLC.CHECK_INFLIGHT_LOST None []
    (fun _ => Bw = Bw) HJS).
  - rewrite GSP. lia.
  - exact Hm16.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - exact R3.
  - exact R4.
  - intros a Ha. unfold NtlLB.LCK.in_wr in Ha. inversion Ha.
  - intros HPRE.
    pose proof (HLOST fx) as LF.
    unfold transport_leaf_at, LIL.transport_check_inflight_lost_cg in LF.
    specialize (LF lyc Sc W (ms_regs ms0) (ms_mem ms0) md1 p (spZ regs - 32) n Bw Bw HPRE).
    cbv zeta in LF.
    pose proof Hoffp as Hof. unfold decode_off_win in Hof.
    apply LF; clear LF.
    + exact Q10.
    + lia.
    + exact Hp8.
    + rewrite <- HK68. pose proof (TWL.u_at_range NB 68 2) as R. change (8 * Z.of_nat 2) with 16 in R. exact R.
    + rewrite <- HK64. unfold TW.put.
      apply (NtlLB.decode_leafb_bytes_le W (ms_mem ms0) (p + 64) 4 (TW.u_at NB 64 4) (TW.u_at NB 64 4));
        [exact (ntl_valw _ p NB 64 4 HNB1 HNBL ltac:(lia) ltac:(lia)) | reflexivity | lia | lia].
    + rewrite <- HK68. unfold TW.put.
      apply (NtlLB.decode_leafb_bytes_le W (ms_mem ms0) (p + 68) 2 (TW.u_at NB 68 2) (TW.u_at NB 68 2));
        [exact (ntl_valw _ p NB 68 2 HNB1 HNBL ltac:(lia) ltac:(lia)) | reflexivity | lia | lia].
    + exact (ntl_tw_csw W (ms_mem ms0) Bw HtwM).
    + exact HML.
    + rewrite SPU. eapply (NtlLB.decode_leafb_stk_journal B); [exact HJS | lia | lia].
    + rewrite SPU. unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME. lia.
    + unfold NtlKA.off_stk. rewrite SPU. left.
      unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    + exact (NtlLB.decode_leafb_asan_cells B HCELLS lyc Sc W (ms_mem ms0) md1 (proj1 HJS)).
    + rewrite SPU. apply NtlLB.decode_leafb_app_stack. unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME. lia.
    + rewrite SPU. apply NtlLB.decode_leafb_app_stack. lia.
    + unfold NtlKA.off_stk. rewrite SPU. left. unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME, NtlAC.GOT_CELL_K. lia.
    + unfold NtlKA.off_stk. rewrite SPU. left. unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME, NtlAC.CELL_K. lia.
    + unfold NtlKA.off_stk. rewrite SPU. unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME.
      destruct Hof as [Ho | Ho]; [left | right]; lia.
    + apply (NtlLB.decode_leafb_addressable W (ms_mem ms0) (p + 64) 4 (fun x Hx => HRA1 x ltac:(lia)));
        [lia | lia | unfold NtlAC.APPMEM_END; lia | intros i Hi; apply Happ; lia].
    + unfold NtlKA.off_stk. rewrite SPU. unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME.
      destruct Hof as [Ho | Ho]; [left | right]; lia.
    + apply (NtlLB.decode_leafb_addressable W (ms_mem ms0) (p + 68) 2 (fun x Hx => HRA1 x ltac:(lia)));
        [lia | lia | unfold NtlAC.APPMEM_END; lia | intros i Hi; apply Happ; lia].
    + rewrite SPU. eapply (NtlLB.decode_leafb_rng_journal B);
        [exact HJS | unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME; lia | unfold NtlLC.CHECK_INFLIGHT_LOST_FRAME; lia].
    + apply ntl_rng_hull; rewrite NtlLC.check_inflight_lost_fly_on_at; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + exact (proj1 (NtlLB.decode_leafb_rng_cells W)).
    + exact (proj2 (NtlLB.decode_leafb_rng_cells W)).
    + pose proof (NtlLB.decode_leafb_rng_shadow W memc (p + 64) 4 (fun x Hx => HRA x ltac:(lia))
        ltac:(lia) ltac:(lia) ltac:(lia)) as RS.
      rewrite (ntl_sh1 p 64 4 Hp8 ltac:(lia) ltac:(lia) ltac:(apply Z.leb_le; reflexivity)) in RS. exact RS.
    + apply (NtlLB.decode_leafb_rng W); [lia | lia | intros a Ha; apply Hvis; lia].
    + apply ntl_rng_hull; rewrite NtlLC.check_inflight_lost_fly_counter_at; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + apply ntl_rng_hull; rewrite NtlLC.check_inflight_lost_fly_retries_at; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + apply ntl_rng_hull; rewrite NtlLC.check_inflight_lost_max_retries_at; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + pose proof (NtlLB.decode_leafb_rng_shadow W memc (p + 68) 2 (fun x Hx => HRA x ltac:(lia))
        ltac:(lia) ltac:(lia) ltac:(lia)) as RS.
      rewrite (ntl_sh1 p 68 2 Hp8 ltac:(lia) ltac:(lia) ltac:(apply Z.leb_le; reflexivity)) in RS. exact RS.
    + apply (NtlLB.decode_leafb_rng W); [lia | lia | intros a Ha; apply Hvis; lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff2 & Hgr2 & _).
(* what the call kept *)
assert (KA2 : nt_KA W memc mem2 (nt_Wn regs)).
{ apply (nt_KA_step W memc (ms_mem ms0) mem2 (nt_Wn regs) (fun a => spZ regs - 16 - 4096 <= a < spZ regs - 16) KA1).
  - intros a Ha Hn. apply Heff2; [exact Ha | rewrite GSP; intros C; apply Hn; exact C |].
    intros Hw. unfold NtlLB.LCK.in_wr in Hw. inversion Hw.
  - exact Hgr2.
  - intros a Ha. cbv beta in Ha. unfold nt_Wn. lia. }
jafter_call_keep_pi HS 200%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  apply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [exact Usp | | exact Hgr2].
  intros a Ha. apply Heff2; [lia | rewrite GSP; unfold ESTACK; lia |].
  intros Hw. unfold NtlLB.LCK.in_wr in Hw. inversion Hw. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite R1.
set (E1 := havoc E 200 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (E1lo : forall j, (j < 200)%nat -> ew E1 j = ew E j) by (intros j Hj; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (U11_1 : bv_unsigned (ew E1 11) = p) by (rewrite E1lo by lia; exact U11e).
assert (E11_1 : ew E1 11 = Z_to_bv 64 p).
{ rewrite E1lo, (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), H11 by lia. reflexivity. }
assert (E32_1 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite E1lo by lia; exact E32e).
assert (U473 : bv_unsigned (ew E1 (A_HI 73)) = TA_M + 96 + 1072)
  by (rewrite (HEI1 (A_HI 73) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)); vm_compute; reflexivity).
assert (U473n : bv_unsigned (ew E1 473%nat) = TA_M + 96 + 1072) by exact U473.
pose proof (nt_ra_kept W memc mem2 p 72 (nt_Wn regs) HRA KA2 HSH) as HRA2.
pose proof (nt_shok W mem2 E1 p HRA2 Ham ltac:(lia) E11_1 E32_1 Hp47) as SHOK1.
clear dependent ms0.
(* M.fly.on's region added, its address in the facts *)
pose proof (nt_add E1 _ _ nt_reg_fly HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict]; exact (ntl_fly_ok W mem2 E1 U473))).
specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fly, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U473, ?U473n, ?Usp1; unfold TA_M; lia)).
rename HSq into HS.
pose proof (nt_facts_set E1 _ _ (nt_facts_f 473%nat (TA_M + 96 + 1072)) HS
  ltac:(apply (nt_facts_f_ok E1 (spZ regs) p 473%nat (TA_M + 96 + 1072));
        first [exact Usp1 | exact U11_1 | exact E32_1 | exact U473n | lia])) as HSq.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
pose proof (nt_KA_mono W memc mem2 (nt_Wn regs) (nt_Zs regs Bw n)
  (fun a Ha => nt_Wn_Zs regs Bw n a Ha) KA2) as KA2z.
(* run 2, +0x78 .. +0x80 and the epilogue: `sw zero, -1072(a0)` (M.fly.on = 0), `j`, ra and sp restored, `ret` *)
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md3 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md3; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA3 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA2z HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp1, ?U473n in Hx;
       first [ left; lia
             | right; unfold notice_wr, twa_fld, TW.A_M_fly_on, TW.OFF_M;
               do 2 right; left; split; [exact Ek | unfold TA_M in *; lia] ])) end.
clear HF HFr HG KA2z.
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) => set (EX := EF) in HS; rename mz into msF end.
assert (HEX : forall j, (j < 200)%nat -> ew EX j = ew E j).
{ intros j Hj. unfold EX. repeat rewrite ew_ewset_other by lia. apply E1lo. exact Hj. }
assert (U473X : bv_unsigned (ew EX 473%nat) = TA_M + 96 + 1072).
{ unfold EX. repeat rewrite ew_ewset_other by lia. exact U473n. }
(* M.fly.on's new value, read back from its region *)
assert (HVAL : val_mem segs (mrestrict (w_H W) (ms_mem msF)) (TA_M + 96 + 1072 + -1072) 4
  (bv_unsigned (sv_denot EX (SLit 0)) mod 2 ^ (8 * Z.of_N 4))).
{ eapply (field_of_region_any EX _ 473%nat (TA_M + 96 + 1072) _ (-1072) (-1068) (-1072) (-1068) (-1072) 4%N
    (SLit 0)).
  - exact (st_ok_pi_region_nth EX _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)).
  - exact U473X.
  - cbn [In]. left. reflexivity.
  - lia. }
replace (bv_unsigned (sv_denot EX (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in HVAL
  by (cbn [sv_denot]; rewrite unsigned_lit_small by lia; reflexivity).
(* the return *)
nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite (HEX 1%nat ltac:(lia)), (HElo 1%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W) EX _ msF regs (nt_vals NB Bw) HS).
  - apply nt_agree; [intros j Hj; rewrite (HEX j ltac:(lia)); apply HElo; lia | exact HEd].
  - vm_compute. reflexivity. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
refine (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
  (ms_regs msF) (ms_mem msF) md3 HC HJ2 KA3 _ HPF RF1 mat').
(* the world after the store: M.fly.on = 0 *)
rewrite HBw. unfold TW.set_M_fly_on, TW.A_M_fly_on.
change (TW.OFF_M + 96 + 0) with (TW.OFF_M + 96).
apply (tw_write TMAP_A (aview segs (w_H W) memc) _ Bw TW.OFF_M TA_M TW.SZ_M 96 4 0 TMAP_A_ok Htw TMAP_A_M
  ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
- intros j Hj. unfold aview.
  replace (TA_M + 96 + Z.of_nat j) with (TA_M + 96 + 1072 + -1072 + Z.of_nat j) by lia.
  rewrite (HVAL j Hj). cbn [option_map]. f_equal.
  rewrite AF0x.unsigned_lit_small8 by (pose proof (ntl_le_byte_small 0 4 j); lia).
  reflexivity.
- intros x Hx Hout. destruct KA3 as [KA3v _]. apply KA3v.
  + pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
  + intros [Hz | Hz].
    * pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
    * pose proof (ntl_wr_lost Bw n x Ek Hz) as Hr. lia.
Qed.
End l.
