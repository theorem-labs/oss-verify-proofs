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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/notice_seg_desk.v; 621 of its 724 lines of code are new or changed and 339 lines of the source are left out. *)
(* notice_seg_state: the N_STATE arm of notice's walk on fuzz_transport.asan (lib/A/Prog/notice_cgW.v), from the
   jump `jr a0` (0x835c4) with a0 = 0x83638:
     0x83638 - 0x8364c  a6 = GOT; a7 = GOT.n (4-byte signed load at GOT + 0, read from that field's region, its value
                        the world's u32); a0 = p + 4; `blt 15, a7` to the join 0x836ec: taken exactly when GOT.n >= 16
                        (nts_br_got), where the model writes no record (nt_B1 Bw n = Bw);
     0x83650 - 0x836e8  (0 <= GOT.n <= 15: the model's None at GOT.n < 0) x = GOT + 12 GOT.n, pinned to atom 42; the
                        record's region (bytes 4 .. 16 of x, a shadow entry for them: GOT's shadow is 0,
                        trans_notice_cells); the checks of the loads at p + 4, p + 8, p + 12 (the notice's shadow
                        entry) and of the stores at x + 4, x + 8, x + 12; the three stores of n->state, n->old_state,
                        n->reason;
     0x836ec - 0x836f0  GOT.n + 1 stored back;
     0x836f4 - 0x83708  the check of the load at p + 4; `bne n->state, 2` to the epilogue 0x8372c (nts_br_state);
     0x8370c - 0x83718  ra loaded back, sp = sp + 16, the tail jump to check_state_online (0x8520c), a leaf: its
                        statement (check_state_online_cg.v, read through DgnTransportCg.v transport_leaf_at) is applied
                        at the jump's state through TransportGCg.v gx_call_leaf and DgnTransportLeafb.v
                        decode_leafb_journal (nts_online_call), its model call notice_m's (nt_m_state: at the world
                        nt_B2 Bw n). The leaf returns to notice's caller with every byte outside its ESTACK window kept.
   The world after the stores is nt_B2 Bw n (nts_tw_step / nts_tw_rec: one tw_write per stored field). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base notice_seg_lib
  notice_seg_disp notice_seg_state_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  DgnTransportLeafb DgnTransportCgRun AsanKA check_state_wake_c check_state_online_c check_state_online_cg.
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
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_c.
Module LSOc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_online_c.
Module LSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_online_cg.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The leaf entered by the tail jump                                   *)
(* ------------------------------------------------------------------ *)

(* Every byte of the harness globals' hull lies in one loaded segment of image A, so no world hides it. *)
Lemma nts_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. replace x with (TG.G_HARNESS_LO + (x - TG.G_HARNESS_LO)) by lia.
  apply (LB.decode_leafb_covers_visible (w_H W) TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO));
    [exact (w_Hoff W) | vm_compute; reflexivity | lia | unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory (the leaf's csw_view). *)
Lemma nts_tw_csw : forall (W : world tfibsegs) m Bw,
  tw_at TMAP_A (aview tfibsegs (w_H W) m) Bw -> tw_at TMAP_A (CSW.csw_view m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  unfold CSW.csw_view. rewrite (DgnTransportCgRun.decode_aview_mrd W m x (nts_hull_vis W x (TMAP_A_hull x Hx))). reflexivity.
Qed.

(* The leaf's footprint holds every range of the hull. *)
Lemma nts_rng_hull : forall (W : world tfibsegs) lo len,
  TG.G_HARNESS_LO <= lo -> lo + len <= TG.G_HARNESS_HI ->
  LB.LExecF.rng (LB.LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2. apply LB.decode_leafb_rng;
    [unfold TG.G_HARNESS_LO in H1; lia | unfold TG.G_HARNESS_HI in H2; lia |].
  intros a Ha. apply nts_hull_vis. lia.
Qed.

(* The walk's kept bytes across a leaf entered at notice's entry sp: the leaf's window lies in notice's. *)
Lemma nts_KA_leaf : forall (W : world tfibsegs) memc (mT m2 : word -> option byte) regs Bw n spT,
  nt_KA W memc mT (nt_Zs regs Bw n) -> spT = spZ regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ LB.LCK.in_wr [] a ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) mT a) ->
  (forall a, apresent (w_H W) mT a -> apresent (w_H W) m2 a) ->
  nt_KA W memc m2 (nt_Zs regs Bw n).
Proof.
  intros W memc mT m2 regs Bw n spT HKA Hsp Hk Hg.
  apply (nt_KA_step W memc mT m2 _ (fun a => spT - ESTACK <= a < spT) HKA); [| exact Hg |].
  - intros a Ha Hn. apply Hk; [exact Ha | exact Hn | intros Hw; inversion Hw].
  - intros a Ha. left. subst spT. assert (FS : NOTICE_STK = 8240) by reflexivity. unfold ESTACK in Ha. lia.
Qed.

(* The world relation across a leaf whose window lies above the hull. *)
Lemma nts_tw_leaf : forall (W : world tfibsegs) (mT m2 : word -> option byte) Bw spT,
  tw_at TMAP_A (aview tfibsegs (w_H W) mT) Bw -> TG.G_HARNESS_HI <= spT - ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ LB.LCK.in_wr [] a ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) mT a) ->
  tw_at TMAP_A (aview tfibsegs (w_H W) m2) Bw.
Proof.
  intros W mT m2 Bw spT H Hs Hk. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in *.
  apply Hk; [lia | lia | intros Hw; inversion Hw].
Qed.

(* ------------------------------------------------------------------ *)
(* The world after the stores                                          *)
(* ------------------------------------------------------------------ *)

(* One 4-byte store into G, the view a mix of the new memory (on the set S) and the old. *)
Lemma nts_tw_step : forall (rdm rdc : Z -> option Z) (S : Z -> bool) Bw o b nn k v,
  tw_at TMAP_A (fun x => if S x then rdm x else rdc x) Bw -> In (o, b, nn) TMAP_A -> 0 <= k -> k + 4 <= nn ->
  (forall j, (j < 4)%nat -> rdm (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_A (fun x => if (S x || ((b + k <=? x) && (x <? b + k + 4)))%bool then rdm x else rdc x)
    (TW.upd Bw (o + k) (TW.put 4 v)).
Proof.
  intros rdm rdc S Bw o b nn k v H Hin Hk Hkn Hnew.
  apply (tw_write TMAP_A _ _ Bw o b nn k 4 v TMAP_A_ok H Hin Hk ltac:(lia)).
  - intros j Hj. replace ((b + k <=? b + k + Z.of_nat j) && (b + k + Z.of_nat j <? b + k + 4))%bool with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite orb_true_r. exact (Hnew j Hj).
  - intros x _ Hx. replace ((b + k <=? x) && (x <? b + k + 4))%bool with false.
    + rewrite orb_false_r. reflexivity.
    + symmetry. apply andb_false_iff.
      destruct (Z_lt_le_dec x (b + k)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

(* GOT.n alone (GOT.n >= 16: no record). *)
Lemma nts_tw_n : forall (W : world tfibsegs) memc mF Bw v,
  tw_at TMAP_A (aview tfibsegs (w_H W) memc) Bw ->
  (forall j, (j < 4)%nat -> aview tfibsegs (w_H W) mF (TA_GOT + 0 + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_GOT <= x < TA_GOT + 4) -> aview tfibsegs (w_H W) mF x = aview tfibsegs (w_H W) memc x) ->
  tw_at TMAP_A (aview tfibsegs (w_H W) mF) (TW.set_GOT_n Bw v).
Proof.
  intros W memc mF Bw v H H4 Hout. unfold TW.set_GOT_n, TW.A_GOT_n.
  apply (tw_write TMAP_A _ _ Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 0 4 v TMAP_A_ok H TMAP_A_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)); [exact H4|].
  intros x Hx Hn. apply Hout; [exact Hx | lia].
Qed.

(* The record and GOT.n (0 <= GOT.n <= 15). *)
Lemma nts_tw_rec : forall (W : world tfibsegs) memc mF Bw g s o r v,
  tw_at TMAP_A (aview tfibsegs (w_H W) memc) Bw -> 0 <= g <= 15 ->
  (forall j, (j < 4)%nat -> aview tfibsegs (w_H W) mF (TA_GOT + (4 + 12 * g) + Z.of_nat j) = Some (YO0f.le_byte s 4 j)) ->
  (forall j, (j < 4)%nat -> aview tfibsegs (w_H W) mF (TA_GOT + (8 + 12 * g) + Z.of_nat j) = Some (YO0f.le_byte o 4 j)) ->
  (forall j, (j < 4)%nat -> aview tfibsegs (w_H W) mF (TA_GOT + (12 + 12 * g) + Z.of_nat j) = Some (YO0f.le_byte r 4 j)) ->
  (forall j, (j < 4)%nat -> aview tfibsegs (w_H W) mF (TA_GOT + 0 + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_GOT <= x < TA_GOT + 4) -> ~ (TA_GOT + 12 * g + 4 <= x < TA_GOT + 12 * g + 16) ->
     aview tfibsegs (w_H W) mF x = aview tfibsegs (w_H W) memc x) ->
  tw_at TMAP_A (aview tfibsegs (w_H W) mF)
    (TW.set_GOT_n (TW.set_GOT_t_reason (TW.set_GOT_t_old (TW.set_GOT_t_state Bw g s) g o) g r) v).
Proof.
  intros W memc mF Bw g s o r v H Hg H1 H2 H3 H4 Hout.
  pose (rdm := aview tfibsegs (w_H W) mF). pose (rdc := aview tfibsegs (w_H W) memc).
  pose (S0 := fun _ : Z => false).
  pose (S1 := fun x => (S0 x || ((TA_GOT + (4 + 12 * g) <=? x) && (x <? TA_GOT + (4 + 12 * g) + 4)))%bool).
  pose (S2 := fun x => (S1 x || ((TA_GOT + (8 + 12 * g) <=? x) && (x <? TA_GOT + (8 + 12 * g) + 4)))%bool).
  pose (S3 := fun x => (S2 x || ((TA_GOT + (12 + 12 * g) <=? x) && (x <? TA_GOT + (12 + 12 * g) + 4)))%bool).
  assert (H0 : tw_at TMAP_A (fun x => if S0 x then rdm x else rdc x) Bw) by exact H.
  pose proof (nts_tw_step rdm rdc S0 Bw TW.OFF_GOT TA_GOT TW.SZ_GOT (4 + 12 * g) s H0 TMAP_A_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) H1) as K1.
  pose proof (nts_tw_step rdm rdc S1 _ TW.OFF_GOT TA_GOT TW.SZ_GOT (8 + 12 * g) o K1 TMAP_A_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) H2) as K2.
  pose proof (nts_tw_step rdm rdc S2 _ TW.OFF_GOT TA_GOT TW.SZ_GOT (12 + 12 * g) r K2 TMAP_A_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) H3) as K3.
  pose proof (nts_tw_step rdm rdc S3 _ TW.OFF_GOT TA_GOT TW.SZ_GOT 0 v K3 TMAP_A_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) H4) as K4.
  unfold TW.set_GOT_n, TW.set_GOT_t_reason, TW.set_GOT_t_old, TW.set_GOT_t_state, TW.A_GOT_n, TW.A_GOT_t_state,
    TW.A_GOT_t_old, TW.A_GOT_t_reason.
  replace (TW.OFF_GOT + 4 + 12 * g + 0) with (TW.OFF_GOT + (4 + 12 * g)) by lia.
  replace (TW.OFF_GOT + 4 + 12 * g + 4) with (TW.OFF_GOT + (8 + 12 * g)) by lia.
  replace (TW.OFF_GOT + 4 + 12 * g + 8) with (TW.OFF_GOT + (12 + 12 * g)) by lia.
  apply (tw_kept TMAP_A _ _ _ K4). intros x Hx. unfold S3, S2, S1, S0. cbv beta.
  match goal with |- _ = (if ?c then _ else _) => destruct c eqn:Ec; [reflexivity|] end.
  apply orb_false_iff in Ec as [Ec E4]. apply orb_false_iff in Ec as [Ec E3].
  apply orb_false_iff in Ec as [Ec E2]. apply orb_false_iff in Ec as [_ E1].
  rewrite andb_false_iff, Z.leb_gt, Z.ltb_ge in E1, E2, E3, E4.
  apply Hout; [exact Hx | lia | lia].
Qed.

(* A 4-byte value read back from a region's chunk, as view bytes. *)
Lemma nts_val_aview : forall (W : world tfibsegs) m a v (j : nat),
  val_mem tfibsegs (mrestrict (w_H W) m) a 4 v -> (j < 4)%nat ->
  aview tfibsegs (w_H W) m (a + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
  intros W m a v j HV Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
  apply AF0x.unsigned_lit_small8. pose proof (nts_le_byte_small v 4 j). lia.
Qed.

(* The stored value of a sign-extended 4-byte load of the u32 u: the bytes of swrap 32 u. *)
Lemma nts_sext_bytes : forall (W : world tfibsegs) m E a u (atom j : nat),
  val_mem tfibsegs (mrestrict (w_H W) m) a 4
    (bv_unsigned (sv_denot E (SExt true 32 (SOff atom 0))) mod 2 ^ (8 * Z.of_N 4)) ->
  ew E atom = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> (j < 4)%nat ->
  aview tfibsegs (w_H W) m (a + Z.of_nat j) = Some (YO0f.le_byte (bv_swrap 32 u) 4 j).
Proof.
  intros W m E a u atom j HV Ea Hu Hj. rewrite (nt_sext32 E atom u Ea Hu) in HV.
  change (8 * Z.of_N 4) with 32 in HV. rewrite (nts_sext_mod32 u Hu) in HV.
  rewrite (nts_val_aview W m a u j HV Hj). f_equal. apply nts_le_byte_swrap. exact Hu.
Qed.

(* The stored value of a sign-extended 4-byte load of the u32 u, plus 1. *)
Lemma nts_inc_bytes : forall (W : world tfibsegs) m E a u (atom j : nat),
  val_mem tfibsegs (mrestrict (w_H W) m) a 4
    (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff atom 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4)) ->
  ew E atom = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> (j < 4)%nat ->
  aview tfibsegs (w_H W) m (a + Z.of_nat j) = Some (YO0f.le_byte (bv_swrap 32 u + 1) 4 j).
Proof.
  intros W m E a u atom j HV Ea Hu Hj.
  change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff atom 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff atom 0))) (Z_to_bv 64 1)) in HV.
  rewrite (nt_sext32 E atom u Ea Hu), nt_add_lit in HV. change (8 * Z.of_N 4) with 32 in HV.
  rewrite nts_mod_64_32 in HV. rewrite (nts_val_aview W m a _ j HV Hj). f_equal. apply nts_le_byte_mod32.
Qed.

(* A region's chunk, read back. *)
Lemma nts_chunk : forall {fx : YK11.FPState} {rc : YM05.RunCeil} E ss ms (i : nat) n b lo hi wlo whi cs od e,
  st_ok_pi tfibsegs (@pa_val _ transport_listing PI_transport) E ss ms ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (YP09.CVal 4 e)) cs ->
  val_mem tfibsegs (ms_mem ms) (b + od) 4 (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N 4)).
Proof.
  intros fx rc E ss ms i n b lo hi wlo whi cs od e HS Hi Hb Hc.
  exact (field_of_region_any E _ n b cs lo hi wlo whi od 4%N e (st_ok_pi_region_nth E ss ms i _ HS Hi) Hb Hc
    ltac:(lia)).
Qed.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The post at a leaf's return to notice's caller (a tail jump: the leaf ran from notice's entry sp with notice's
   entry ra, so it returns to raw = the entry ra), from the walk's last facts. *)
Lemma nts_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    regsF (raw : word) mF mdF,
  @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    mF mdF k ->
  nt_KA W memc mF (nt_Zs regs Bw n) ->
  tw_at TMAP_A (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> raw = YK11.getr regs 1 ->
  @transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw' W
    (mkCfg (@YK11.mkst fx regsF raw mF (YK11.seg_rom segs)) mdF).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regsF raw mF mdF HC HJF
    [KA GA] HtwF HP Hraw.
  destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
    as (HAR & Hwin & Hsp & Hce & _ & _ & _ & _ & _ & _).
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ Hra Hra4 Hgp Htp H11 Hsp16 Hlo
    Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS a -> a < kLowMemEnd).
  { intros a Ha. exact (proj2 (transport_segs_low a (proj1 (HGX a Ha)))). }
  unfold transport_notice_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, mdF, 0.
  split; [rewrite Hraw; reflexivity|].
  split; [unfold NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc mF
      (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) (nt_Zs regs Bw n) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - exact KA.
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a (nt_wr_G _ _ _ Hw)). unfold kLowMemEnd in *. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + exact (HnG (nt_wr_G _ _ _ Hw)).
    - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact HtwF.
Qed.

(* The tail jump to check_state_online at the world B2 (nt_B2 Bw n): its statement through the leaf bridge, lifted
   into the G journal; the leaf returns to notice's caller. *)
Lemma nts_online_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    (msF : machine_state) mdF B2,
  @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    (ms_mem msF) mdF k ->
  nt_KA W memc (ms_mem msF) (nt_Zs regs Bw n) ->
  tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) B2 ->
  TC.check_state_online_m B2 = Some (Bw', tt) ->
  YK11.getr (ms_regs msF) 1 = YK11.getr regs 1 ->
  YK11.getr (ms_regs msF) (Z_to_bv 5 2) = YK11.getr regs (Z_to_bv 5 2) ->
  YK11.getr (ms_regs msF) 3 = YK11.getr regs 3 ->
  YK11.getr (ms_regs msF) 4 = YK11.getr regs 4 ->
  aregs_preserved regs (ms_regs msF) ->
  SRr segs W (mkCfg (@YK11.mkst fx (ms_regs msF) (Z_to_bv 64 LSOc.CHECK_STATE_ONLINE) (ms_mem msF)
      (YK11.seg_rom segs)) mdF)
    (@transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw').
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB msF mdF B2
    HC HJ KAF HtwF HMo RT1 RT2 RT3 RT4 HPT.
  destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
    as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo
    Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  assert (Hsp1 : spZ (ms_regs msF) = spZ regs) by exact (f_equal bv_unsigned RT2).
  assert (Hsp2 : bv_unsigned (YK11.getr (ms_regs msF) (Z_to_bv 5 2)) = spZ regs) by exact (f_equal bv_unsigned RT2).
  eapply SRr_mono.
  { eapply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
      (ms_mem msF) mdF k _ _ _ HJ).
    intros memS HJS.
    apply (@LB.decode_leafb_journal fx rc tfib_sink_head B LAWS W (ms_regs msF) (ms_mem msF) STK sp0 FP ly S W0 memS
      md0 own lyc Sc mdF k (spZ regs - sp0) LSOc.CHECK_STATE_ONLINE None [] (fun _ => Bw' = B2) HJS).
    - rewrite Hsp1. lia.
    - replace (spZ regs - sp0) with (spZ regs - 16 - sp0 + 1 * 16) by lia. rewrite Z_mod_plus_full. exact Hm16.
    - lia.
    - unfold ESTACK. lia.
    - exact (eq_ind_r YK0s.ret_ok Hra RT1).
    - exact (eq_trans RT3 Hgp).
    - exact (eq_trans RT4 Htp).
    - intros a Ha. inversion Ha.
    - intros HPRE.
      pose proof (HONL fx) as LF.
      unfold transport_leaf_at, LSO.transport_check_state_online_cg in LF.
      specialize (LF lyc Sc W (ms_regs msF) (ms_mem msF) mdF (spZ regs - NOTICE_STK) B2 Bw' HPRE).
      cbv zeta in LF. unfold AKA.off_stk in LF. rewrite Hsp2 in LF.
      apply LF; clear LF.
      + exact (nts_tw_csw W (ms_mem msF) _ HtwF).
      + exact HMo.
      + exact (@LB.decode_leafb_stk_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem msF)
          mdF k (spZ regs - NOTICE_STK) (spZ regs) HJS ltac:(lia) ltac:(lia)).
      + unfold LSOc.CHECK_STATE_ONLINE_FRAME. lia.
      + left. unfold LSOc.CHECK_STATE_ONLINE_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
      + exact (@LB.decode_leafb_rng_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem msF)
          mdF k (spZ regs - LSOc.CHECK_STATE_ONLINE_FRAME) LSOc.CHECK_STATE_ONLINE_FRAME HJS
          ltac:(unfold LSOc.CHECK_STATE_ONLINE_FRAME; lia) ltac:(lia)).
      + rewrite LSOc.check_state_online_e2_at.
        apply nts_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
      + rewrite LSOc.check_state_online_e1_at.
        apply nts_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HK2 & HG2 & HX).
  assert (Htw2 : tw_at TMAP_A (aview segs (w_H W) mem2) Bw').
  { rewrite HX. apply (nts_tw_leaf W (ms_mem msF) mem2 _ (spZ (ms_regs msF)) HtwF); [|exact HK2].
    rewrite Hsp1. unfold TG.G_HARNESS_HI, ESTACK. lia. }
  exact (nts_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regs2 _ mem2 md2
    HC HJ2 (nts_KA_leaf W memc (ms_mem msF) mem2 regs Bw n _ KAF Hsp1 HK2 HG2) Htw2
    (aregs_preserved_trans regs (ms_regs msF) regs2 HPT HP2) RT1).
Qed.

(* ------------------------------------------------------------------ *)
(* The arm                                                             *)
(* ------------------------------------------------------------------ *)

Lemma nt_path_state : @nt_path fx rc B MT TC.N_STATE NT_STATE.
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
destruct (nt_m_state timg_A Fr Bw n Bw' Ek Hm) as (Hmax & Hnn & Hon & Hoff).
(* the valuation at the arm *)
pose proof (nt_E_atom regs NB Bw 0%nat ltac:(lia)) as E32q. pose proof (nt_E_atom regs NB Bw 1%nat ltac:(lia)) as E33q.
pose proof (nt_E_atom regs NB Bw 2%nat ltac:(lia)) as E34q. pose proof (nt_E_atom regs NB Bw 3%nat ltac:(lia)) as E35q.
pose proof (nt_E_atom regs NB Bw 4%nat ltac:(lia)) as E36q. pose proof (nt_E_atom regs NB Bw 5%nat ltac:(lia)) as E37q.
pose proof (nt_E_atom regs NB Bw 10%nat ltac:(lia)) as E42q.
cbn [Nat.add nth nt_vals] in E32q, E33q, E34q, E35q, E36q, E37q, E42q.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HElo 32%nat ltac:(lia)); exact E32q).
assert (E33 : ew E 33 = Z_to_bv 64 (TW.u_at NB 0 4)) by (rewrite (HElo 33%nat ltac:(lia)); exact E33q).
assert (E34 : ew E 34 = Z_to_bv 64 (TW.u_at NB 4 4)) by (rewrite (HElo 34%nat ltac:(lia)); exact E34q).
assert (E35 : ew E 35 = Z_to_bv 64 (TW.u_at NB 8 4)) by (rewrite (HElo 35%nat ltac:(lia)); exact E35q).
assert (E36 : ew E 36 = Z_to_bv 64 (TW.u_at NB 12 4)) by (rewrite (HElo 36%nat ltac:(lia)); exact E36q).
assert (E37 : ew E 37 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_n 4)) by (rewrite (HElo 37%nat ltac:(lia)); exact E37q).
assert (E42 : ew E 42 = Z_to_bv 64 (TA_GOT + 12 * TW.GOT_n Bw)) by (rewrite (HElo 42%nat ltac:(lia)); exact E42q).
assert (E11 : ew E 11 = Z_to_bv 64 p)
  by (rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl); exact H11).
assert (U11 : bv_unsigned (ew E 11) = p) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (HElo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2%nat 2%bv eq_refl); reflexivity).
assert (U13 : bv_unsigned (ew E (A_OBJ 13)) = TA_GOT)
  by (rewrite (HEI (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); vm_compute; reflexivity).
assert (U13n : bv_unsigned (ew E 254%nat) = TA_GOT) by exact U13.
pose proof (TWL.u_at_range Bw TW.A_GOT_n 4) as R37. change (8 * Z.of_nat 4) with 32 in R37.
pose proof (nt_s32_range Bw TW.A_GOT_n) as Rg. change (TW.s32_at Bw TW.A_GOT_n) with (TW.GOT_n Bw) in Rg.
(* the world and the notice's bytes at the arm's memory *)
assert (HtwM : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) Bw).
{ apply (nt_tw_keep W memc (ms_mem ms) Bw (nt_Wn regs) Htw KA).
  intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
assert (HNBM : garr8 segs (mrestrict (w_H W) (ms_mem ms)) p (map DSpec.bz NB)).
{ apply (nt_garr8_keep W memc (ms_mem ms) (nt_Wn regs) p _ KA HNB).
  intros a Ha. rewrite length_map, HNBL in Ha. split; [lia|]. unfold nt_Wn, decode_off_win, NTC_SIZE in *. lia. }
pose proof (nt_KA_mono W memc (ms_mem ms) (nt_Wn regs) (nt_Zs regs Bw n)
  (fun a Ha => nt_Wn_Zs regs Bw n a Ha) KA) as KA0.
(* the bytes notice_wr names for N_STATE are off the notice *)
assert (HAPn : forall x, TA_GOT <= x < TA_GOT + 4 -> ~ (p <= x < p + 72)).
{ intros x Hx. refine (proj1 (HAP x _)).
  unfold notice_wr. left. split; [exact Ek|]. right. unfold twa_fld, TW.A_GOT_n. lia. }
(* the notice's first 16 bytes and GOT.n's field *)
pose proof (nt_add E _ _ nt_reg_p HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts nt_ss_jr] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict];
  exact (nt_preg_ok E _ p NB E11 ltac:(lia) ltac:(lia) E33 E34 E35 E36 HNBM HNBL))).
specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_p, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, U11;
  unfold decode_off_win in Hoffp; lia)).
rename HSq into HS.
pose proof (nt_add E _ _ nts_reg_gotn HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict]; unfold nts_reg_gotn;
  exact (nt_fld_ok W _ E Bw 13%nat 37%nat 0 ltac:(rewrite U13; lia) ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)
    E37 HtwM))).
specialize (HSq ltac:(cbn [all_disjoint]; unfold nts_reg_gotn, nt_reg_fld, extent_disjoint, nt_reg_p, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, U11, U13;
  split; [| split; [| exact I]];
  [ destruct (Z_lt_le_dec (TA_GOT + 3) p) as [L|L]; [left; lia|];
    destruct (Z_le_gt_dec (p + 16) TA_GOT) as [L2|L2]; [right; lia|];
    exfalso; apply (HAPn (Z.max p TA_GOT)); lia
  | unfold TA_GOT; left; lia ])).
rename HSq into HS.
pose proof (nt_facts_set E _ _ nts_facts1 HS
  ltac:(apply (nt_facts_f_ok E (spZ regs) p (A_OBJ 13) TA_GOT); first [exact Usp | exact U11 | exact E32 | exact U13 | lia]))
  as HSq.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
(* run 1, +0xc0 .. +0xd4: a6 = GOT, a7 = GOT.n, a0 = p + 4, the branch on GOT.n *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA1 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA0 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp, ?U13n in Hx;
       first [ left; unfold nt_Wn; lia
             | right; unfold notice_wr; left; split; [exact Ek | right; unfold twa_fld, TW.A_GOT_n; lia] ])) end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.

- (* GOT.n >= 16: no record *)
  rewrite (nts_br_got E Bw E37) in Hc. apply Z.ltb_lt in Hc.
  assert (HB1 : nt_B1 Bw n = Bw).
  { unfold nt_B1. replace (TW.GOT_n Bw <? TC.TRANS_MAX) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. unfold TC.TRANS_MAX. lia. }
  rename Hc into HcG.
  (* run 2: the join (GOT.n + 1 stored back), the check of p + 4, n->state, to the branch *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { nt_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (md2 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md2; clear mt end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
    assert (KA2 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
      (apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG);
       intros b wlo whi x Hin Hx; cbv beta;
       nt_win Hin Hx ltac:(rewrite ?Usp, ?U13n in Hx;
         first [ left; unfold nt_Wn; lia
               | right; unfold notice_wr; left; split; [exact Ek | right; unfold twa_fld, TW.A_GOT_n; lia] ]));
    rename mz into msB end.
  clear HF HFr HG KA1.
  (* GOT.n + 1, read back from its field's region *)
  assert (HVn : forall j, (j < 4)%nat ->
    aview segs (w_H W) (ms_mem msB) (TA_GOT + 0 + Z.of_nat j) = Some (YO0f.le_byte (TW.GOT_n Bw + 1) 4 j)).
  { intros j Hj.
    pose proof (nts_chunk E _ _ 0%nat (A_OBJ 13) TA_GOT 0 4 0 4
      [YP09.mkChunk 0 (YP09.CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)))] 0
      (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) HS ltac:(vm_compute; reflexivity) U13
      ltac:(cbn [In]; left; reflexivity)) as HV.
    cbn [ms_mem restrict] in HV.
    exact (nts_inc_bytes W (ms_mem msB) E (TA_GOT + 0) _ 37 j HV E37 R37 Hj). }
  assert (HtwB2 : tw_at TMAP_A (aview segs (w_H W) (ms_mem msB)) (nt_B2 Bw n)).
  { unfold nt_B2. rewrite HB1. apply (nts_tw_n W memc (ms_mem msB) Bw _ Htw HVn).
    intros x Hx Hn. pose proof KA2 as [KAx _]. apply KAx.
    - pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
    - intros [Hz | Hz].
      + pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
      + unfold notice_wr in Hz.
        unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hz, Ek.
        destruct Hz as [(_ & [(Hg' & Hz) | Hz]) | [(E' & _) | [(E' & _) | [(E' & _) | [(E' & _) | (E' & _)]]]]];
          first [lia | unfold TC.TRANS_MAX in *; lia | unfold twa_fld, TW.A_GOT_n in *; lia
                | unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ in *; lia]. }

  (* the branch on n->state *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* n->state <> S_ONLINE: the epilogue; the world is nt_B2 Bw n *)
    rewrite (nts_br_state E NB (TI.n_state n) E34 HK4) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    pose proof (Hoff Hc) as HBw'.
    nt_keep1.
    pose proof (nt_KA_refl W (ms_mem msB) (nt_Wn regs)) as KAt.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdF := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdF; clear mt end.
    lazymatch type of HS with context [restrict _ ?mz] =>
      assert (KAF : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp in Hx; left; unfold nt_Wn; lia));
      assert (KAtF : nt_KA W (ms_mem msB) (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W (ms_mem msB) _ _ _ KAt HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp in Hx; unfold nt_Wn; lia));
      rename mz into msF end.
    clear HF HFr HG.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1 ltac:(cbn [sv_denot]; rewrite (HElo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
      - apply nt_agree; [intros j Hj; apply HElo; lia | exact HEd].
      - vm_compute. reflexivity. }
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    refine (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
      (ms_regs msF) (ms_mem msF) mdF HC HJ KAF _ HPF RF1 mat').
    rewrite HBw'. apply (nt_tw_keep W (ms_mem msB) (ms_mem msF) _ (nt_Wn regs) HtwB2 KAtF).
    intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
  + (* n->state = S_ONLINE: the tail jump to check_state_online at the world nt_B2 Bw n *)
    rewrite (nts_br_state E NB (TI.n_state n) E34 HK4) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    pose proof (Hon Hc) as HMo.
    nt_keep1.
    pose proof (nt_KA_refl W (ms_mem msB) (nt_Wn regs)) as KAt.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdF := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdF; clear mt end.
    lazymatch type of HS with context [restrict _ ?mz] =>
      assert (KAF : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp in Hx; left; unfold nt_Wn; lia));
      assert (KAtF : nt_KA W (ms_mem msB) (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W (ms_mem msB) _ _ _ KAt HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp in Hx; unfold nt_Wn; lia));
      rename mz into msF end.
    clear HF HFr HG.
    assert (HtwF : tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) (nt_B2 Bw n)).
    { apply (nt_tw_keep W (ms_mem msB) (ms_mem msF) _ (nt_Wn regs) HtwB2 KAtF).
      intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
    pmkst HS.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RT1 ltac:(cbn [sv_denot]; rewrite (HElo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) RT2 ltac:(cbn [sv_denot]; rewrite (HElo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (3%bv : bv 5) (YK11.getr regs 3) RT3 ltac:(cbn [sv_denot]; rewrite (HElo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (4%bv : bv 5) (YK11.getr regs 4) RT4 ltac:(cbn [sv_denot]; rewrite (HElo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPT : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
      - apply nt_agree; [intros j Hj; apply HElo; lia | exact HEd].
      - vm_compute. reflexivity. }
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (?mk ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (mk rg (Z_to_bv 64 LSOc.CHECK_STATE_ONLINE) mm rom) mdx) Q) end.
    exact (nts_online_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB msF mdF
      (nt_B2 Bw n) HC HJ KAF HtwF HMo RT1 RT2 RT3 RT4 HPT).

- (* 0 <= GOT.n <= 15: the record *)
  rewrite (nts_br_got E Bw E37) in Hc. apply Z.ltb_ge in Hc.
  assert (Hg : 0 <= TW.GOT_n Bw <= 15) by (pose proof (Hnn ltac:(unfold TC.TRANS_MAX; lia)); lia).
  rename Hc into HcG.
  (* run 2, to +0xf8: the check of p + 4, a4 = GOT + 12 GOT.n *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan NTS_REC.
  { nt_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (md2 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md2; clear mt end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
    assert (KA2 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
      (apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG);
       intros b wlo whi x Hin Hx; cbv beta;
       nt_win Hin Hx ltac:(rewrite ?Usp, ?U13n in Hx;
         first [ left; unfold nt_Wn; lia
               | right; unfold notice_wr; left; split; [exact Ek | right; unfold twa_fld, TW.A_GOT_n; lia] ]));
    rename mz into msR end.
  clear HF HFr HG KA1.
  (* a4 pinned to the record's base, atom 42 *)
  nt_reg HS (Z_to_bv 5 14) (Z_to_bv 64 (TA_GOT + 12 * TW.GOT_n Bw)) Q14 ltac:(exact (nts_rec_addr E Bw E37 U13 Hg)).
  assert (QD : sv_denot E (SOff 42 0) = Z_to_bv 64 (TA_GOT + 12 * TW.GOT_n Bw))
    by (cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pose proof (nt_pin E _ _ (Z_to_bv 5 14) (SOff 42 0) HS (eq_trans Q14 (eq_sym QD)) ltac:(vm_compute; reflexivity))
    as HSq.
  clear HS Q14. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
  assert (U42 : bv_unsigned (ew E 42) = TA_GOT + 12 * TW.GOT_n Bw)
    by (rewrite E42; apply unsigned_lit_small; unfold TA_GOT; lia).
  assert (HAPr : forall x, TA_GOT + 12 * TW.GOT_n Bw + 4 <= x < TA_GOT + 12 * TW.GOT_n Bw + 16 -> ~ (p <= x < p + 72)).
  { intros x Hx. refine (proj1 (HAP x _)). unfold notice_wr. left. split; [exact Ek|]. left.
    split; [unfold TC.TRANS_MAX; lia | unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ; lia]. }
  (* the record's region, the facts with its range, its shadow entry *)
  pose proof (nt_add E _ _ nt_reg_rec HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
  specialize (HSq ltac:(cbn [ms_mem restrict]; unfold nt_reg_rec, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U42;
    split; [unfold TA_GOT; lia|]; split; [unfold TA_GOT; lia|];
    split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw); apply nt_inG_GOT;
            unfold TA_GOT in *; lia | constructor])).
  specialize (HSq ltac:(cbn [all_disjoint]; unfold nt_reg_rec, extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U42, ?U13n, ?U13, ?U11, ?Usp;
    repeat match goal with |- _ /\ _ => split end; try exact I;
    first [ unfold TA_GOT in *; lia
          | destruct (Z_lt_le_dec (TA_GOT + 12 * TW.GOT_n Bw + 15) p) as [L|L]; [lia|];
            destruct (Z_le_gt_dec (p + 16) (TA_GOT + 12 * TW.GOT_n Bw + 4)) as [L2|L2]; [lia|];
            exfalso; apply (HAPr (Z.max p (TA_GOT + 12 * TW.GOT_n Bw + 4))); lia ])).
  rename HSq into HS.
  pose proof (nt_facts_set E _ _ nts_facts2 HS
    ltac:(apply (nts_facts2_ok E (spZ regs) p (TW.GOT_n Bw));
          first [exact Usp | exact U11 | exact E32 | exact U13 | exact U42 | lia])) as HSq.
  clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
  pose proof HJ as (_ & _ & (memSR & HJiR & _) & _). pose proof HJiR as (HARR & _).
  pose proof (nts_got_ra B lyc Sc W (ms_mem msR) md2 (TA_GOT + 12 * TW.GOT_n Bw + 4) 12 HNCELLS HARR
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as HRAR.
  pose proof (nts_shok2 W (ms_mem msR) E (TW.GOT_n Bw) SHOK HRAR E32 E42 Hg) as SHOK2.
  clear SHOK. rename SHOK2 into SHOK.
  (* run 3, +0xf8 .. +0x194: the record's three stores, GOT.n + 1, the check of p + 4, n->state *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { nt_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (md3 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md3; clear mt end.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in * end.
  assert (E3lo : forall j, (j < 1024)%nat -> ew E3 j = ew E j)
    by (intros j Hj; unfold E3;
        first [ reflexivity | repeat rewrite ew_ewset_other by lia; reflexivity
              | rewrite ew_havoc_old by (cbn; lia); reflexivity ]).
  assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite (E3lo 2%nat ltac:(lia)); exact Usp).
  assert (U13n3 : bv_unsigned (ew E3 254%nat) = TA_GOT) by (rewrite (E3lo 254%nat ltac:(lia)); exact U13n).
  assert (U42_3 : bv_unsigned (ew E3 42) = TA_GOT + 12 * TW.GOT_n Bw) by (rewrite (E3lo 42%nat ltac:(lia)); exact U42).
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
    assert (KA3 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
      (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
       intros b wlo whi x Hin Hx; cbv beta;
       nt_win Hin Hx ltac:(rewrite ?Usp3, ?U13n3, ?U42_3 in Hx;
         first [ left; unfold nt_Wn; lia
               | right; unfold notice_wr; left; split; [exact Ek | right; unfold twa_fld, TW.A_GOT_n; lia]
               | right; unfold notice_wr; left; split; [exact Ek | left];
                 split; [unfold TC.TRANS_MAX; lia | unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ; lia] ]));
    rename mz into msB end.
  clear HF HFr HG KA2.
  (* the record's fields and GOT.n + 1, read back from the regions *)
  pose proof (TWL.u_at_range NB 4 4) as R4. pose proof (TWL.u_at_range NB 8 4) as R8.
  pose proof (TWL.u_at_range NB 12 4) as R12. change (8 * Z.of_nat 4) with 32 in R4, R8, R12.
  assert (HVR : forall (od : Z) (at_ : nat) (u : Z) (j : nat),
    In (YP09.mkChunk od (YP09.CVal 4 (SExt true 32 (SOff at_ 0))))
      [YP09.mkChunk 12 (YP09.CVal 4 (SExt true 32 (SOff 36 0)));
       YP09.mkChunk 8 (YP09.CVal 4 (SExt true 32 (SOff 35 0)));
       YP09.mkChunk 4 (YP09.CVal 4 (SExt true 32 (SOff 34 0)))] ->
    ew E3 at_ = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> (j < 4)%nat ->
    aview segs (w_H W) (ms_mem msB) (TA_GOT + 12 * TW.GOT_n Bw + od + Z.of_nat j) =
      Some (YO0f.le_byte (bv_swrap 32 u) 4 j)).
  { intros od at_ u j Hin Ea Hu Hj.
    pose proof (nts_chunk E3 _ _ 0%nat 42 (TA_GOT + 12 * TW.GOT_n Bw) 4 16 4 16 _ od (SExt true 32 (SOff at_ 0)) HS
      ltac:(vm_compute; reflexivity) U42_3 Hin) as HV.
    cbn [ms_mem restrict] in HV.
    exact (nts_sext_bytes W (ms_mem msB) E3 _ u at_ j HV Ea Hu Hj). }
  assert (HV1 : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem msB) (TA_GOT + (4 + 12 * TW.GOT_n Bw) + Z.of_nat j)
    = Some (YO0f.le_byte (TI.n_state n) 4 j)).
  { intros j Hj. rewrite <- HK4. replace (TA_GOT + (4 + 12 * TW.GOT_n Bw)) with (TA_GOT + 12 * TW.GOT_n Bw + 4) by lia.
    exact (HVR 4 34%nat _ j ltac:(cbn [In]; right; right; left; reflexivity)
      ltac:(rewrite (E3lo 34%nat ltac:(lia)); exact E34) R4 Hj). }
  assert (HV2 : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem msB) (TA_GOT + (8 + 12 * TW.GOT_n Bw) + Z.of_nat j)
    = Some (YO0f.le_byte (TI.n_old n) 4 j)).
  { intros j Hj. rewrite <- HK8. replace (TA_GOT + (8 + 12 * TW.GOT_n Bw)) with (TA_GOT + 12 * TW.GOT_n Bw + 8) by lia.
    exact (HVR 8 35%nat _ j ltac:(cbn [In]; right; left; reflexivity)
      ltac:(rewrite (E3lo 35%nat ltac:(lia)); exact E35) R8 Hj). }
  assert (HV3 : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem msB) (TA_GOT + (12 + 12 * TW.GOT_n Bw) + Z.of_nat j)
    = Some (YO0f.le_byte (TI.n_reason n) 4 j)).
  { intros j Hj. rewrite <- HK12.
    replace (TA_GOT + (12 + 12 * TW.GOT_n Bw)) with (TA_GOT + 12 * TW.GOT_n Bw + 12) by lia.
    exact (HVR 12 36%nat _ j ltac:(cbn [In]; left; reflexivity)
      ltac:(rewrite (E3lo 36%nat ltac:(lia)); exact E36) R12 Hj). }
  assert (HVn : forall j, (j < 4)%nat ->
    aview segs (w_H W) (ms_mem msB) (TA_GOT + 0 + Z.of_nat j) = Some (YO0f.le_byte (TW.GOT_n Bw + 1) 4 j)).
  { intros j Hj.
    pose proof (nts_chunk E3 _ _ 1%nat (A_OBJ 13) TA_GOT 0 4 0 4
      [YP09.mkChunk 0 (YP09.CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)))] 0
      (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) HS ltac:(vm_compute; reflexivity) U13n3
      ltac:(cbn [In]; left; reflexivity)) as HV.
    cbn [ms_mem restrict] in HV.
    exact (nts_inc_bytes W (ms_mem msB) E3 (TA_GOT + 0) _ 37 j HV ltac:(rewrite (E3lo 37%nat ltac:(lia)); exact E37)
      R37 Hj). }
  assert (HtwB2 : tw_at TMAP_A (aview segs (w_H W) (ms_mem msB)) (nt_B2 Bw n)).
  { unfold nt_B2, nt_B1.
    replace (TW.GOT_n Bw <? TC.TRANS_MAX) with true by (symmetry; apply Z.ltb_lt; unfold TC.TRANS_MAX; lia).
    apply (nts_tw_rec W memc (ms_mem msB) Bw (TW.GOT_n Bw) _ _ _ _ Htw Hg HV1 HV2 HV3 HVn).
    intros x Hx Hn1 Hn2. pose proof KA3 as [KAx _]. apply KAx.
    - pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
    - intros [Hz | Hz].
      + pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
      + unfold notice_wr in Hz.
        unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hz, Ek.
        destruct Hz as [(_ & [(Hg' & Hz) | Hz]) | [(E' & _) | [(E' & _) | [(E' & _) | [(E' & _) | (E' & _)]]]]];
          first [lia | unfold TC.TRANS_MAX in *; lia | unfold twa_fld, TW.A_GOT_n in *; lia
                | unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ in *; lia]. }

  (* the branch on n->state *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* n->state <> S_ONLINE: the epilogue; the world is nt_B2 Bw n *)
    rewrite (nts_br_state E3 NB (TI.n_state n) ltac:(rewrite (E3lo 34%nat ltac:(lia)); exact E34) HK4) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    pose proof (Hoff Hc) as HBw'.
    nt_keep1.
    pose proof (nt_KA_refl W (ms_mem msB) (nt_Wn regs)) as KAt.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdF := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdF; clear mt end.
    lazymatch type of HS with context [restrict _ ?mz] =>
      assert (KAF : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA3 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp3 in Hx; left; unfold nt_Wn; lia));
      assert (KAtF : nt_KA W (ms_mem msB) (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W (ms_mem msB) _ _ _ KAt HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp3 in Hx; unfold nt_Wn; lia));
      rename mz into msF end.
    clear HF HFr HG.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1 ltac:(cbn [sv_denot]; rewrite (E3lo 1%nat ltac:(lia)); rewrite (HElo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) E3 _ msF regs (nt_vals NB Bw) HS).
      - apply nt_agree; [intros j Hj; rewrite (E3lo j ltac:(lia)); apply HElo; lia | first [exact HEd | unfold E3; exact HEd | unfold E3; cbn; exact HEd]].
      - vm_compute. reflexivity. }
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    refine (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
      (ms_regs msF) (ms_mem msF) mdF HC HJ KAF _ HPF RF1 mat').
    rewrite HBw'. apply (nt_tw_keep W (ms_mem msB) (ms_mem msF) _ (nt_Wn regs) HtwB2 KAtF).
    intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
  + (* n->state = S_ONLINE: the tail jump to check_state_online at the world nt_B2 Bw n *)
    rewrite (nts_br_state E3 NB (TI.n_state n) ltac:(rewrite (E3lo 34%nat ltac:(lia)); exact E34) HK4) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    pose proof (Hon Hc) as HMo.
    nt_keep1.
    pose proof (nt_KA_refl W (ms_mem msB) (nt_Wn regs)) as KAt.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdF := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdF; clear mt end.
    lazymatch type of HS with context [restrict _ ?mz] =>
      assert (KAF : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA3 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp3 in Hx; left; unfold nt_Wn; lia));
      assert (KAtF : nt_KA W (ms_mem msB) (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W (ms_mem msB) _ _ _ KAt HFr HG);
         intros b wlo whi x Hin Hx; cbv beta;
         nt_win Hin Hx ltac:(rewrite ?Usp3 in Hx; unfold nt_Wn; lia));
      rename mz into msF end.
    clear HF HFr HG.
    assert (HtwF : tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) (nt_B2 Bw n)).
    { apply (nt_tw_keep W (ms_mem msB) (ms_mem msF) _ (nt_Wn regs) HtwB2 KAtF).
      intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
    pmkst HS.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RT1 ltac:(cbn [sv_denot]; rewrite (E3lo 1%nat ltac:(lia)); rewrite (HElo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) RT2 ltac:(cbn [sv_denot]; rewrite (E3lo 2%nat ltac:(lia)); rewrite (HElo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (3%bv : bv 5) (YK11.getr regs 3) RT3 ltac:(cbn [sv_denot]; rewrite (E3lo 3%nat ltac:(lia)); rewrite (HElo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (4%bv : bv 5) (YK11.getr regs 4) RT4 ltac:(cbn [sv_denot]; rewrite (E3lo 4%nat ltac:(lia)); rewrite (HElo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPT : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) E3 _ msF regs (nt_vals NB Bw) HS).
      - apply nt_agree; [intros j Hj; rewrite (E3lo j ltac:(lia)); apply HElo; lia | first [exact HEd | unfold E3; exact HEd | unfold E3; cbn; exact HEd]].
      - vm_compute. reflexivity. }
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (?mk ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (mk rg (Z_to_bv 64 LSOc.CHECK_STATE_ONLINE) mm rom) mdx) Q) end.
    exact (nts_online_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB msF mdF
      (nt_B2 Bw n) HC HJ KAF HtwF HMo RT1 RT2 RT3 RT4 HPT).
Qed.
End st.
