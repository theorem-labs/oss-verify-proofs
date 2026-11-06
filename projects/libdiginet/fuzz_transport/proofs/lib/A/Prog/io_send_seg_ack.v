(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1878 of its 1989 lines of code are new or changed and 815 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_tail.v, with its module names changed; 388 of its 483 lines of code are new or changed and 1894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_csf.v, with its module names changed; 1292 of its 1396 lines of code are new or changed and 379 lines of the source are left out. *)
(* io_send's image-A ASan walk (libdiginet/fuzz_transport, fuzz_transport.asan e89be137db17, entry 0x82d60 =
   TImgA.v ti_io_send timg_A; the frozen statement is lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt):
   the segment from the cut IOS_CSF (0x83088, the return of check_sent_frame) through the dispatch on f.cmd and the
   ACK and E3 arms, 0x83088 .. 0x830e4 (io_send_cg.v header lines 103-110). sp is the walk's sp, the entry sp less
   IOSEND_FRAME = 160; GOT = TA_GOT.

   0x83088 - 0x83098  s5 = f.cmd (lbu at sp + 48, io_send's own frame, no instrumented check); 0xe1 < s5 goes to
                      0x830bc; 0 goes to 0x830e8 = transport_text + IOS_E2DATA; 0xa0 goes on at 0x830a0; any
                      other value goes to 0x83384 = transport_text + IOS_EPI;
   0x830bc - 0x830c8  0xe2 goes to IOS_E2DATA; 0xe3 goes on at 0x830cc; any other value goes to IOS_EPI;
   0x830a0 - 0x830b8  ACK (:833-836): GOT.acks (GOT + 204) + 1 stored back (no instrumented check); a0 = sp + 8;
                      `jal` check_ack_frame (0x8415c) at 0x830b4; `j` to 0x830dc;
   0x830cc - 0x830d8  E3 (:891-893): GOT.e3 (GOT + 200) + 1 stored back; on to 0x830dc;
   0x830dc - 0x830e4  (transport_text + IOS_CTRL) a0 = sp + 8; `jal` check_latest_control (0x8420c) at 0x830e0;
                      `j` to IOS_EPI.

   ios_ack_seg_stmt starts from io_send_seg_cut.v ios_at_csf and ends in one continuation per exit: IOS_E2DATA with
   ios_at_csf at the state there and s5 = f.cmd, and IOS_EPI with what io_send_seg_epi.v ios_epi reads, at the world
   io_send_segs.v ios_arm leaves. The two counters are bytes of G in iosend_wr; each leaf call goes through
   TransportGCg.v gx_call_leaf and DgnTransportLeafb.v decode_leafb_journal. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgRun DgnTransportLeafb CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_cg io_send_segs io_send_seg_frm io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit AsanKA check_state_wake_c
  check_ack_frame_c check_latest_control_c check_ack_frame_cg check_latest_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame ExecF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_c.
Module LAFc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_c.
Module LLCc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_c.
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* Bytes and words                                                     *)
(* ------------------------------------------------------------------ *)

Lemma iak_bow : forall v j, (j < 4)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v 4 j.
Proof.
intros v j Hj. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change (8 * Z.of_nat 4) with 32.
change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma iak_sext_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma iak_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma iak_lts : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). reflexivity.
Qed.

(* put n of the value of n bytes of a list is those n bytes. *)
Lemma iak_put_sub : forall (SB : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  TW.put n (TW.u_at SB k n) = TW.sub SB k n.
Proof.
  intros SB k n Hk Hl. pose proof (TWL.length_sub SB k n Hk Hl) as L. unfold TW.put, TW.u_at.
  remember (TW.sub SB k n) as s eqn:Es. rewrite <- L. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma iak_nth_sub : forall (SB : list byte) k n j, 0 <= k -> (j < n)%nat ->
  k + Z.of_nat n <= Z.of_nat (length SB) ->
  nth j (map DSpec.bz (TW.sub SB k n)) 0 = nth (Z.to_nat k + j) (map DSpec.bz SB) 0.
Proof.
  intros SB k n j Hk Hj Hl.
  destruct (nth_error SB (Z.to_nat k + j)) as [x|] eqn:Ex.
  2: { exfalso. apply nth_error_None in Ex. lia. }
  assert (E1 : nth_error (map DSpec.bz (TW.sub SB k n)) j = Some (DSpec.bz x)).
  { rewrite nth_error_map, (TWL.ne_sub SB k n j Hk).
    replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). rewrite Ex. reflexivity. }
  assert (E2 : nth_error (map DSpec.bz SB) (Z.to_nat k + j) = Some (DSpec.bz x))
    by (rewrite nth_error_map, Ex; reflexivity).
  erewrite (nth_error_nth _ _ _ E1). erewrite (nth_error_nth _ _ _ E2). reflexivity.
Qed.

Lemma iak_garr8_sub : forall (m : word -> option byte) p (SB : list byte) k n,
  garr8 tfibsegs m p (map DSpec.bz SB) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  garr8 tfibsegs m (p + k) (map DSpec.bz (TW.sub SB k n)).
Proof.
  intros m p SB k n HG Hk Hl j Hj.
  rewrite length_map, (TWL.length_sub SB k n Hk Hl) in Hj.
  rewrite (iak_nth_sub SB k n j Hk Hj Hl).
  assert (Hj' : (Z.to_nat k + j < length (map DSpec.bz SB))%nat) by (rewrite length_map; lia).
  replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
  exact (HG _ Hj').
Qed.

(* A field of n bytes at offset k of the struct's byte list, of value v. *)
Lemma iak_field : forall (m : word -> option byte) p (SB : list byte) k n v,
  garr8 tfibsegs m p (map DSpec.bz SB) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  TW.u_at SB k n = v -> garr8 tfibsegs m (p + k) (map DSpec.bz (TW.put n v)).
Proof.
  intros m p SB k n v HG Hk Hl Hv. subst v. rewrite (iak_put_sub SB k n Hk Hl).
  exact (iak_garr8_sub m p SB k n HG Hk Hl).
Qed.

Lemma iak_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) base l,
  (forall a, base <= a < base + Z.of_nat (length l) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m) base l -> garr8 tfibsegs (mrestrict H m') base l.
Proof.
  intros H m m' base l Heq HG. apply (garr8_frame tfibsegs _ _ base l HG).
  intros a Ha. apply (mbyte_of_aview tfibsegs). apply Heq. exact Ha.
Qed.

Lemma iak_sframe_kept : forall (W : world tfibsegs) mem mem' p fa f,
  (forall a, p <= a < p + 80 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  trans_sframe_at W mem p fa f -> trans_sframe_at W mem' p fa f.
Proof.
  intros W mem mem' p fa f Heq (H0 & H8 & SB & HG & HL & R). split; [exact H0|]. split; [exact H8|].
  exists SB. split; [|split; [exact HL | exact R]].
  apply (iak_garr8_kept _ mem mem' p _); [|exact HG].
  intros a Ha. rewrite length_map, HL in Ha. change (Z.of_nat 80) with 80 in Ha. apply Heq. exact Ha.
Qed.

Lemma iak_rdword_eq : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) ->
  rdword r' a = rdword r a.
Proof.
  intros r r' a H. unfold rdword.
  assert (E0 : r' a = r a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma iak_saved_kept : forall (W : world tfibsegs) mem mem' regs,
  (forall a, spZ regs - 72 <= a < spZ regs -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ios_saved W mem regs -> ios_saved W mem' regs.
Proof.
  intros W mem mem' regs Heq HS. unfold ios_saved in *. rewrite Forall_forall in HS |- *.
  intros o Ho. rewrite <- (HS o Ho). apply iak_rdword_eq. intros i Hi. apply Heq.
  unfold IOS_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho.
Qed.

(* A range of n bytes at x + k, x 8-aligned, inside one granule has one shadow byte. *)
Lemma iak_shadow_one : forall x k n, 0 <= x -> x mod 8 = 0 -> 0 <= k -> 0 < n -> k mod 8 + n <= 8 ->
  ACells.shadow_addr (x + k + n - 1) - ACells.shadow_addr (x + k) + 1 = 1.
Proof.
  intros x k n H0 Hx Hk Hn Hm. unfold ACells.shadow_addr.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod k 8 ltac:(lia)) as Dk.
  pose proof (Z.mod_pos_bound k 8 ltac:(lia)) as Mk.
  assert (E1 : x / 8 + k / 8 = (x + k) / 8).
  { apply Z.div_unique with (k mod 8); [left; lia | lia]. }
  assert (E2 : x / 8 + k / 8 = (x + k + n - 1) / 8).
  { apply Z.div_unique with (k mod 8 + n - 1); [left; lia | lia]. }
  rewrite <- E1, <- E2. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The harness globals are visible                                     *)
(* ------------------------------------------------------------------ *)

Lemma iak_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. apply (decode_vis_seg W).
  apply (decode_covers_img TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) x); [vm_compute; reflexivity | lia].
Qed.

Lemma iak_tw_csw : forall (W : world tfibsegs) mem Bw,
  tw_at TMAP_A (aview tfibsegs (w_H W) mem) Bw -> tw_at TMAP_A (CSW.csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  unfold CSW.csw_view. rewrite (decode_aview_mrd W mem x (iak_hull_vis W x (TMAP_A_hull x Hx))). reflexivity.
Qed.

Lemma iak_rng_hull : forall (W : world tfibsegs) lo len, TG.G_HARNESS_LO <= lo -> lo + len <= TG.G_HARNESS_HI ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2. apply (decode_rng W); [unfold TG.G_HARNESS_LO in *; lia | unfold TG.G_HARNESS_HI in *; lia |].
  intros b Hb. apply iak_hull_vis. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

Definition IAK_ACKS : Z := TA_GOT + 204.
Definition IAK_E3 : Z := TA_GOT + 200.
Definition iak_cmd_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 48 49 48 48 [YP09.mkChunk 48 (CVal 1 (SOff 32 0))].
Definition iak_acks_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 25)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition iak_e3_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 26)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
(* The same two words, as the stores after `auipc a0` address them: `sw a1, 0x30c(a0)` (0x830a8, reloc 49) and
   `sw a1, 0x2dc(a0)` (0x830d4, reloc 50). *)
Definition iak_acks_st : YP09.region :=
  YP09.mkRegion (Some (A_HI 49)) 0x30c (0x30c + 4) 0x30c (0x30c + 4) [YP09.mkChunk 0x30c (CVal 4 (SOff 33 0))].
Definition iak_e3_st : YP09.region :=
  YP09.mkRegion (Some (A_HI 50)) 0x2dc (0x2dc + 4) 0x2dc (0x2dc + 4) [YP09.mkChunk 0x2dc (CVal 4 (SOff 34 0))].
Definition iak_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 0 255 0);
           (A_OBJ 25, mkAF IAK_ACKS IAK_ACKS 2); (A_OBJ 26, mkAF IAK_E3 IAK_E3 3);
           (A_HI 49, mkAF (IAK_ACKS - 0x30c) (IAK_ACKS - 0x30c) 2);
           (A_HI 50, mkAF (IAK_E3 - 0x2dc) (IAK_E3 - 0x2dc) 2)] [] [].
Definition ss_iak : sstate := mkSS IOS_CSF sr_atoms [iak_cmd_region] None iak_facts.
Definition IAK_Bx : sv := SOff 20 0.
Definition ss_iak0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* A run whose only region is read-only keeps every byte. *)
Lemma iak_ro_frame : forall E (m m' : word -> option byte), frame_of E [iak_cmd_region] m m' -> forall x, m' x = m x.
Proof.
  intros E m m' H x. apply H. intros (r & Hr & Ha). destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi iak_cmd_region] in Ha. lia.
Qed.

Lemma iak_aview_ext : forall segs0 (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview segs0 H m' a = aview segs0 H m a.
Proof. intros segs0 H m m' a Hx. unfold aview, YP09.mbyte, mrestrict. rewrite Hx. reflexivity. Qed.

Lemma iak_present_ext : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a Hx [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hx. exact Hb. Qed.

Lemma iak_val_mem_ext : forall segs0 (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, m' x = m x) -> val_mem segs0 (mrestrict H m) a n v -> val_mem segs0 (mrestrict H m') a n v.
Proof.
  intros segs0 H m m' a n v Hx HV k Hk. pose proof (HV k Hk) as Hv.
  unfold YP09.mbyte, mrestrict in *. rewrite Hx. exact Hv.
Qed.

(* The registers the dispatch keeps: every callee-saved register but s5, which it loads with f.cmd. *)
Definition IAK_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv.
Definition iak_regs (rg rg2 : bvmap 5 word) (cmd : Z) : Prop :=
  (forall r, In r IAK_KEEP -> YK11.getr rg2 r = YK11.getr rg r) /\ YK11.getr rg2 21%bv = w64 cmd.

Ltac iak_kin := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma iak_ios_regs : forall regs rg rg2 p frame fail,
  ios_regs regs rg p frame fail -> (forall r, In r IAK_KEEP -> YK11.getr rg2 r = YK11.getr rg r) ->
  ios_regs regs rg2 p frame fail.
Proof.
  intros regs rg rg2 p frame fail (R2 & R3 & R4 & R8 & R9 & R19 & R20) HK.
  split; [exact (eq_trans (HK 2%bv ltac:(iak_kin)) R2)|].
  split; [exact (eq_trans (HK 3%bv ltac:(iak_kin)) R3)|].
  split; [exact (eq_trans (HK 4%bv ltac:(iak_kin)) R4)|].
  split; [exact (eq_trans (HK 8%bv ltac:(iak_kin)) R8)|].
  split; [exact (eq_trans (HK 9%bv ltac:(iak_kin)) R9)|].
  split; [exact (eq_trans (HK 19%bv ltac:(iak_kin)) R19)|].
  exact (eq_trans (HK 20%bv ltac:(iak_kin)) R20).
Qed.

(* A register of the callee-saved set, kept by a call (aregs_preserved); decode's dnl4_ap / dnl4_pres_list. *)
Lemma iak_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof. intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma iak_keep_of_pres : forall rg rg2 : bvmap 5 word, aregs_preserved rg rg2 ->
  forall r, In r IAK_KEEP -> YK11.getr rg2 r = YK11.getr rg r.
Proof.
  intros rg rg2 HP r Hr. apply (iak_ap rg rg2 r HP). unfold IAK_KEEP in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
          [unfold acallee_saved;
           lazymatch goal with |- context [bv_unsigned ?x] =>
             let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
           lia |]).
  destruct Hr.
Qed.

Lemma iak_s5_of_pres : forall rg rg2 : bvmap 5 word, aregs_preserved rg rg2 -> YK11.getr rg2 21%bv = YK11.getr rg 21%bv.
Proof.
  intros rg rg2 HP. apply (iak_ap rg rg2 21%bv HP). unfold acallee_saved.
  lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end.
  lia.
Qed.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition iak_E (rg : bvmap 5 word) (cmd ua ue : Z) : env :=
  Eimg (PI := PI_transport) (Ereg rg [Z_to_bv 64 cmd; Z_to_bv 64 ua; Z_to_bv 64 ue]).
Definition iak_E0 (rg : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg rg []).

Lemma iak_E_reg : forall rg l n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (PI := PI_transport) (Ereg rg l)) n = YK11.getr rg r.
Proof. intros rg l n r Hn. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma iak_agree : forall rg l, env_agree 32 (Ereg rg l) (Eimg (PI := PI_transport) (Ereg rg l)).
Proof. intros rg l. split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* The state at the cut IOS_CSF: s5 is about to be loaded with f.cmd at sp + 48 (atom 32); atoms 33 and 34 are the
   world's GOT.acks and GOT.e3 as unsigned ints, used by the regions the ACK and E3 arms add. *)
Lemma iak_entry : forall (W : world segs) rg mem cmd ua ue,
  2 ^ 46 <= spZ rg <= 2 ^ 47 - 160 -> spZ rg mod 16 = 0 -> 0 <= cmd < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (spZ rg + 48) 1 cmd ->
  st_ok_pi segs VAL (iak_E rg cmd ua ue) ss_iak
    (restrict (w_H W) (@YK11.mkst fx rg (Z_to_bv 64 (BASE + IOS_CSF)) mem (YK11.seg_rom segs))).
Proof.
  intros W rg mem cmd ua ue Hsp Hal Hc HV.
  assert (U2 : bv_unsigned (ew (iak_E rg cmd ua ue) 2) = spZ rg)
    by (unfold iak_E; rewrite (iak_E_reg rg _ 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (iak_E rg cmd ua ue) 32 = Z_to_bv 64 cmd)
    by (unfold iak_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rg _ 0)).
  assert (U25 : bv_unsigned (ew (iak_E rg cmd ua ue) (A_OBJ 25)) = IAK_ACKS).
  { unfold iak_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). vm_compute. reflexivity. }
  assert (U26 : bv_unsigned (ew (iak_E rg cmd ua ue) (A_OBJ 26)) = IAK_E3).
  { unfold iak_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). vm_compute. reflexivity. }
  assert (U25' : bv_unsigned (ew (iak_E rg cmd ua ue) 266%nat) = IAK_ACKS) by exact U25.
  assert (U26' : bv_unsigned (ew (iak_E rg cmd ua ue) 267%nat) = IAK_E3) by exact U26.
  assert (U49 : bv_unsigned (ew (iak_E rg cmd ua ue) (A_HI 49)) = IAK_ACKS - 0x30c).
  { unfold iak_E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). vm_compute. reflexivity. }
  assert (U50 : bv_unsigned (ew (iak_E rg cmd ua ue) (A_HI 50)) = IAK_E3 - 0x2dc).
  { unfold iak_E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). vm_compute. reflexivity. }
  assert (U49' : bv_unsigned (ew (iak_E rg cmd ua ue) 449%nat) = IAK_ACKS - 0x30c) by exact U49.
  assert (U50' : bv_unsigned (ew (iak_E rg cmd ua ue) 450%nat) = IAK_E3 - 0x2dc) by exact U50.
  rewrite restrict_mkst_fx. unfold ss_iak.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold iak_cmd_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (spZ rg) 48 1 (SOff 32 0) cmd);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact HV].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold iak_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite ?U2, ?U25, ?U26, ?U25', ?U26', ?U49, ?U50, ?U49', ?U50', E32, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [lia | unfold IAK_ACKS, IAK_E3, TA_GOT; reflexivity].
Qed.

(* A state with no region and no fact, from the concrete registers (after a call). *)
Lemma iak_entry0 : forall (W : world segs) rg mem pc,
  st_ok_pi segs VAL (iak_E0 rg) (ss_iak0 pc)
    (restrict (w_H W) (@YK11.mkst fx rg (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W rg mem pc. rewrite restrict_mkst_fx. unfold ss_iak0, iak_E0.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport);
    [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]].
Qed.

(* What io_send's fixed entry facts give about the stack. *)
Lemma iak_geo : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw,
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  @AR rc segs B lyc Sc W memc mdc /\ alloc_ceiling <= sp0 - STK /\ sp0 - STK <= spZ regs - IOSEND_STK /\
  spZ regs <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ spZ regs mod 16 = 0.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX.
  destruct HFX as (HJ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hhi & _).
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (H16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  split; [exact HAR|]. repeat split; lia.
Qed.

(* A step of the walk that changes only bytes of io_send's stack window or bytes of G in its written range keeps the
   running kept fact. *)
Lemma iak_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi (E Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B G ->
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (slo <= a < shi) \/ (inG G a /\ E a)) ->
  alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transport_segs_low G a HGX Ha)).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia |].
    intros HZa. destruct (HZ a HZa) as [Hs | [Hg _]]; [exact (Hw Hs) | pose proof (GLOW a Hg); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [Hg _]]; [lia | exact (HnG Hg)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Ha Hw Hp. apply Hgr. apply K5; [exact Ha | exact Hw | exact Hp].
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* The running facts at a cut, from those at the previous cut and the bytes the step changed (Zs: bytes of io_send's
   stack window, or bytes of G that some path of the call stores). *)
Lemma iak_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    ly2 S2 (W2 : world segs) mem2 md2 mem3 md3 (Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (spZ regs - IOSEND_STK <= a < spZ regs) \/
                     (inG TG.G_HARNESS a /\ iosend_wr (Z.of_nat (length frame)) a)) ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 mem3 md3 Zs
    LAWS HGX HFX (HJ & HF & HP & HM & HK) HJ3 Hkp Hgr HZ.
  destruct (iak_geo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX)
    as (HAR & Hce & Hlo & Hhi & H47 & _).
  split; [exact HJ3|]. split; [exact HF|]. split; [exact HP|]. split; [exact HM|].
  exact (iak_kept_step _ _ _ _ _ mdc W2 mem2 mem3 _ _ _ Zs LAWS HGX HAR HK Hkp Hgr HZ ltac:(lia) ltac:(lia)).
Qed.

(* A 4-byte region of one chunk, moved to another base atom whose value is d below: the store `sw a1, d(a0)` after
   `auipc a0` addresses the word the load through the listing's object atom read. *)
Lemma iak_rebase : forall E (m : word -> option byte) n1 n2 d (e : sv),
  region_ok segs E m (YP09.mkRegion (Some n1) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 e)]) ->
  bv_unsigned (ew E n1) = bv_unsigned (ew E n2) + d -> 0 <= bv_unsigned (ew E n2) ->
  region_ok segs E m (YP09.mkRegion (Some n2) d (d + 4) d (d + 4) [YP09.mkChunk d (CVal 4 e)]).
Proof.
  intros E m n1 n2 d e (H0 & H1 & HW & HC) Hb Hn2.
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *.
  rewrite Hb in H0, H1, HW, HC.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. replace (bv_unsigned (ew E n2) + o) with (bv_unsigned (ew E n2) + d + (o - d)) by lia.
    apply HW. lia.
  - apply Forall_inv in HC. constructor; [|constructor].
    intros i Hi. destruct (HC i Hi) as (b & Hb1 & Hb2). exists b.
    cbn [YP09.c_off YP09.c_val] in *. rewrite Z.add_0_r in Hb1, Hb2. split; [exact Hb1 | exact Hb2].
Qed.

(* The 4 bytes of the one chunk of a region, read through the view. *)
Lemma iak_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply iak_bow. exact Hj.
Qed.

Lemma iak_region_rd4 : forall E (H : word -> bool) (mm : word -> option byte) n lo hi wlo whi off e v b,
  region_ok segs E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi [YP09.mkChunk off (CVal 4 e)]) ->
  bv_unsigned (ew E n) = b -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview segs H mm (b + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
  intros E H mm n lo hi wlo whi off e v b (_ & _ & _ & HC) Hb Hv.
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite Hb in HC. apply Forall_inv in HC.
  exact (iak_chunk_rd E H mm b off e v HC Hv).
Qed.

(* What a leaf call returns (DgnTransportLeafb.v decode_leafb_journal's facts with RES = None, WR = [] and the
   leaf's X Bx = Bx). *)
Definition iak_lr (regsT : bvmap 5 word) (W2 : world segs) (memT : word -> option byte) (Bx : list byte)
    (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  aregs_preserved regsT regs2 /\ (forall r, None = Some r -> YK11.getr regs2 10 = w64 r) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> ~ LCK.in_wr [] a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W2) memT a) /\
  (forall a, apresent (w_H W2) memT a -> apresent (w_H W2) mem2 a) /\ Bx = Bx.

(* The stack window of a call from io_send's frame: the struct at sp + 8 lies in the caller's journal window, above
   the callee's ESTACK window. *)
Definition iak_call_win (STK sp0 sp : Z) : Prop :=
  sp mod 16 = 0 /\ sp0 - STK <= sp - ESTACK /\ sp + 88 <= sp0.

(* check_latest_control at 0x8420c (calls at 0x830e0 and 0x83134), a0 = sp + 8. *)
Lemma iak_call_clc : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) memT mdT k
    (regsT : bvmap 5 word) (sp p : Z) (fr Bx : list byte),
  transport_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 memT mdT k ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 sp -> YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 (sp + 8) ->
  YK0s.ret_ok (YK11.getr regsT (Z_to_bv 5 1)) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  iak_call_win STK sp0 sp ->
  trans_sframe_at W2 memT (sp + 8) p (TC.rf fr) ->
  tw_at TMAP_A (aview segs (w_H W2) memT) Bx -> TC.check_latest_control_m Bx fr = Some (Bx, tt) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LLCc.CHECK_LATEST_CONTROL) memT (YK11.seg_rom segs)) mdT)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsT (Z_to_bv 5 1)) mem3 (YK11.seg_rom segs)) md3 /\
       @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
         ly2 S2 W2 mem3 md3 k /\
       iak_lr regsT W2 memT Bx regs3 mem3 md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k regsT sp p fr Bx HCELLS LAWS LEAF HJ
    R2 R10 Rra R3 R4 (Hal & Hlo & Hhi) HSF HTW HM.
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (SPu : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp) by (rewrite R2; apply unsigned_lit_small; lia).
  destruct HSF as (Hfp0 & Hfp8 & SB & HG & HLSB & _ & _ & _ & _ & _ & _ & _ & Fsend & _).
  apply (gx_call_leaf segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k _
    (YK11.getr regsT (Z_to_bv 5 1)) (iak_lr regsT W2 memT Bx) HJ).
  intros memS HJS.
  pose proof HJS as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  unfold iak_lr.
  apply (decode_leafb_journal B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0 own ly2 S2 mdT k (sp - sp0)
    LLCc.CHECK_LATEST_CONTROL None [] (fun _ => Bx = Bx) HJS).
  - change (spZ regsT) with (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))). rewrite SPu. lia.
  - rewrite Zminus_mod, Hal, Hsp0al. reflexivity.
  - lia.
  - lia.
  - exact Rra.
  - exact R3.
  - exact R4.
  - intros a Ha. inversion Ha.
  - intros HPRE.
    pose proof (LEAF fx) as LF.
    unfold transport_leaf_at, LLC.transport_check_latest_control_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT mdT (sp - ESTACK) Bx Bx (sp + 8) fr HPRE).
    cbv zeta in LF.
    assert (HRA : range_addressable (aview segs (w_H W2) memT) SHADOW_OFF (sp + 8 + 32) 4)
      by (apply (can_stack_addressable segs B ly2 S2 W2 memT mdT (sp + 8 + 32) 4 HAR); lia).
    apply LF; clear LF.
    + exact R10.
    + lia.
    + exact Hfp8.
    + apply (decode_leafb_bytes_garr8 W2 memT (sp + 8 + 32) (TW.put 4 (DSpec.sf_send (TC.rf fr))));
        [| lia | rewrite TWL.length_put; lia].
      exact (iak_field _ (sp + 8) SB 32 4 _ HG ltac:(lia) ltac:(rewrite HLSB; cbn; lia) Fsend).
    + exact (iak_tw_csw W2 memT Bx HTW).
    + exact HM.
    + rewrite SPu. apply (decode_leafb_stk_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - ESTACK) sp HJS); lia.
    + rewrite SPu. unfold LLCc.CHECK_LATEST_CONTROL_FRAME. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLCc.CHECK_LATEST_CONTROL_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI.
      lia.
    + exact (decode_leafb_asan_cells B HCELLS ly2 S2 W2 memT mdT HAR).
    + rewrite SPu. apply (@decode_leafb_app_stack rc). unfold LLCc.CHECK_LATEST_CONTROL_FRAME. lia.
    + rewrite SPu. apply (@decode_leafb_app_stack rc). lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLCc.CHECK_LATEST_CONTROL_FRAME, ACells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLCc.CHECK_LATEST_CONTROL_FRAME, ACells.CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + apply (decode_leafb_addressable W2 memT (sp + 8 + 32) 4 HRA); [lia | lia | unfold ACells.APPMEM_END; lia |].
      intros i Hi. apply (@decode_leafb_app_stack rc). lia.
    + rewrite SPu. apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - LLCc.CHECK_LATEST_CONTROL_FRAME) LLCc.CHECK_LATEST_CONTROL_FRAME HJS);
        unfold LLCc.CHECK_LATEST_CONTROL_FRAME; lia.
    + exact (proj1 (decode_leafb_rng_cells W2)).
    + exact (proj2 (decode_leafb_rng_cells W2)).
    + pose proof (decode_leafb_rng_shadow W2 memT (sp + 8 + 32) 4 HRA ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
      rewrite (iak_shadow_one (sp + 8) 32 4) in Hr
        by first [exact Hfp8 | lia | (vm_compute; let H := fresh in intro H; discriminate H)].
      exact Hr.
    + apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k (sp + 8 + 32) 4 HJS);
        lia.
    + apply iak_rng_hull; unfold LLCc.CHECK_LATEST_CONTROL_HOST, TA_M, TW.A_M_host_counter, TW.OFF_M,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
Qed.

(* check_ack_frame at 0x8415c (call at 0x830b4), a0 = sp + 8. *)
Lemma iak_call_caf : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) memT mdT k
    (regsT : bvmap 5 word) (sp p : Z) (fr Bx : list byte),
  transport_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LAF.transport_check_ack_frame_cg) fx') ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 memT mdT k ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 sp -> YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 (sp + 8) ->
  YK0s.ret_ok (YK11.getr regsT (Z_to_bv 5 1)) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  iak_call_win STK sp0 sp ->
  trans_sframe_at W2 memT (sp + 8) p (TC.rf fr) ->
  tw_at TMAP_A (aview segs (w_H W2) memT) Bx -> TC.check_ack_frame_m Bx fr = Some (Bx, tt) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LAFc.CHECK_ACK_FRAME) memT (YK11.seg_rom segs)) mdT)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsT (Z_to_bv 5 1)) mem3 (YK11.seg_rom segs)) md3 /\
       @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
         ly2 S2 W2 mem3 md3 k /\
       iak_lr regsT W2 memT Bx regs3 mem3 md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k regsT sp p fr Bx HCELLS LAWS LEAF HJ
    R2 R10 Rra R3 R4 (Hal & Hlo & Hhi) HSF HTW HM.
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (SPu : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp) by (rewrite R2; apply unsigned_lit_small; lia).
  destruct HSF as (Hfp0 & Hfp8 & SB & HG & HLSB & _ & _ & _ & _ & _ & _ & Fretry & _ & Fack & _ & _ & _ & Fblen & _).
  apply (gx_call_leaf segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k _
    (YK11.getr regsT (Z_to_bv 5 1)) (iak_lr regsT W2 memT Bx) HJ).
  intros memS HJS.
  pose proof HJS as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  unfold iak_lr.
  apply (decode_leafb_journal B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0 own ly2 S2 mdT k (sp - sp0)
    LAFc.CHECK_ACK_FRAME None [] (fun _ => Bx = Bx) HJS).
  - change (spZ regsT) with (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))). rewrite SPu. lia.
  - rewrite Zminus_mod, Hal, Hsp0al. reflexivity.
  - lia.
  - lia.
  - exact Rra.
  - exact R3.
  - exact R4.
  - intros a Ha. inversion Ha.
  - intros HPRE.
    pose proof (LEAF fx) as LF.
    unfold transport_leaf_at, LAF.transport_check_ack_frame_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT mdT (sp + 8) (sp - ESTACK) fr Bx Bx HPRE R10).
    cbv zeta in LF.
    assert (HRA : forall o n, 0 <= o -> o + n <= 80 -> 0 <= n ->
      range_addressable (aview segs (w_H W2) memT) SHADOW_OFF (sp + 8 + o) n)
      by (intros o n Ho Hon Hn; apply (can_stack_addressable segs B ly2 S2 W2 memT mdT (sp + 8 + o) n HAR); lia).
    assert (HAD : forall o n, 0 <= o -> o + n <= 80 -> 0 <= n -> ACells.addressable memT (sp + 8 + o) n).
    { intros o n Ho Hon Hn. apply (decode_leafb_addressable W2 memT (sp + 8 + o) n (HRA o n Ho Hon Hn));
        [lia | lia | unfold ACells.APPMEM_END; lia |].
      intros i Hi. apply (@decode_leafb_app_stack rc). lia. }
    assert (HRS : forall o n, 0 <= o -> 0 < n -> o mod 8 + n <= 8 -> o + n <= 80 ->
      ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W2) (ACells.shadow_addr (sp + 8 + o)) 1).
    { intros o n Ho Hn Hm Hon.
      pose proof (decode_leafb_rng_shadow W2 memT (sp + 8 + o) n (HRA o n Ho Hon ltac:(lia)) ltac:(lia) ltac:(lia)
        ltac:(lia)) as Hr.
      rewrite (iak_shadow_one (sp + 8) o n) in Hr by first [exact Hfp8 | lia]. exact Hr. }
    assert (HRJ : forall o n, 0 <= o -> o + n <= 80 -> ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W2) (sp + 8 + o) n)
      by (intros o n Ho Hon;
          apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k (sp + 8 + o) n HJS);
          lia).
    assert (HBY : forall k0 (n : nat) v, 0 <= k0 -> k0 + Z.of_nat n <= 80 -> TW.u_at SB k0 n = v ->
      LMem.bytes_at segs memT (sp + 8 + k0) (TW.put n v)).
    { intros k0 n v Hk Hkn Hv.
      apply (decode_leafb_bytes_garr8 W2 memT (sp + 8 + k0) (TW.put n v)); [| lia | rewrite TWL.length_put; lia].
      exact (iak_field _ (sp + 8) SB k0 n v HG Hk ltac:(rewrite HLSB; exact Hkn) Hv). }
    apply LF; clear LF.
    + lia.
    + exact Hfp8.
    + exact (HBY 36 4%nat _ ltac:(lia) ltac:(cbn; lia) Fack).
    + exact (HBY 56 8%nat _ ltac:(lia) ltac:(cbn; lia) Fblen).
    + exact (HBY 30 2%nat _ ltac:(lia) ltac:(cbn; lia) Fretry).
    + exact (iak_tw_csw W2 memT Bx HTW).
    + exact HM.
    + rewrite SPu. apply (decode_leafb_stk_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - ESTACK) sp HJS); lia.
    + rewrite SPu. unfold LAFc.CHECK_ACK_FRAME_FRAME. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LAFc.CHECK_ACK_FRAME_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    + exact (decode_leafb_asan_cells B HCELLS ly2 S2 W2 memT mdT HAR).
    + rewrite SPu. apply (@decode_leafb_app_stack rc). unfold LAFc.CHECK_ACK_FRAME_FRAME. lia.
    + rewrite SPu. apply (@decode_leafb_app_stack rc). lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LAFc.CHECK_ACK_FRAME_FRAME, ACells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LAFc.CHECK_ACK_FRAME_FRAME, ACells.CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 36 4 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 56 8 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 30 2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite SPu. apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - LAFc.CHECK_ACK_FRAME_FRAME) LAFc.CHECK_ACK_FRAME_FRAME HJS); unfold LAFc.CHECK_ACK_FRAME_FRAME; lia.
    + exact (proj1 (decode_leafb_rng_cells W2)).
    + exact (proj2 (decode_leafb_rng_cells W2)).
    + exact (HRS 36 4 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + exact (HRJ 36 4 ltac:(lia) ltac:(lia)).
    + apply iak_rng_hull; unfold LAFc.CHECK_ACK_FRAME_RX_SEND, TA_g_rx_send, TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + exact (HRS 56 8 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + exact (HRJ 56 8 ltac:(lia) ltac:(lia)).
    + exact (HRS 30 2 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + exact (HRJ 30 2 ltac:(lia) ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics and small facts of the runs                                 *)
(* ------------------------------------------------------------------ *)

(* The model term after a run, named and opaque. *)
Ltac iak_md := lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
  let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv end.

(* The symbolic state of HS, computed. *)
Ltac iak_rw HS := lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.

(* The value v of register r in the machine state of HS, from its symbolic value, closed by tac. *)
Ltac iak_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg sg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The write rights of a run: the read-only cmd region, and the words of GOT (bytes of G). *)
Ltac iak_awr U1 U2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite U1 in Ha; apply (ios_inG_row _ _ _ a TMAP_A_GOT); unfold IAK_ACKS, IAK_E3, TW.SZ_GOT in *; lia
            | rewrite U2 in Ha; apply (ios_inG_row _ _ _ a TMAP_A_GOT); unfold IAK_ACKS, IAK_E3, TW.SZ_GOT in *; lia ]
    |]);
  apply awr_ok_x_nil.

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac iak_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Lemma iak_E32 : forall rg cmd ua ue, ew (iak_E rg cmd ua ue) 32 = Z_to_bv 64 cmd.
Proof. intros. unfold iak_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rg _ 0). Qed.
Lemma iak_E33 : forall rg cmd ua ue, ew (iak_E rg cmd ua ue) 33 = Z_to_bv 64 ua.
Proof. intros. unfold iak_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rg _ 1). Qed.
Lemma iak_E34 : forall rg cmd ua ue, ew (iak_E rg cmd ua ue) 34 = Z_to_bv 64 ue.
Proof. intros. unfold iak_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rg _ 2). Qed.

Lemma iak_br_lt : forall rg cmd ua ue, 0 <= cmd < 256 ->
  branch_taken BC_LT (sv_denot (iak_E rg cmd ua ue) (SLit 225)) (sv_denot (iak_E rg cmd ua ue) (SOff 32 0)) =
  (225 <? cmd).
Proof.
  intros rg cmd ua ue Hc. cbn [branch_taken sv_denot].
  rewrite iak_E32, Z.add_0_r, Z_to_bv_bv_unsigned. apply iak_lts; lia.
Qed.
Lemma iak_br_eq : forall rg cmd ua ue z, 0 <= cmd < 256 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot (iak_E rg cmd ua ue) (SOff 32 0)) (sv_denot (iak_E rg cmd ua ue) (SLit z)) =
  (cmd =? z).
Proof.
  intros rg cmd ua ue z Hc Hz. rewrite branch_eq_U, (U_atom _ 32 cmd (iak_E32 rg cmd ua ue)) by lia.
  rewrite U_lit by exact Hz. reflexivity.
Qed.
Lemma iak_br_ne : forall rg cmd ua ue z, 0 <= cmd < 256 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot (iak_E rg cmd ua ue) (SOff 32 0)) (sv_denot (iak_E rg cmd ua ue) (SLit z)) =
  negb (cmd =? z).
Proof.
  intros rg cmd ua ue z Hc Hz. rewrite branch_ne_U, (U_atom _ 32 cmd (iak_E32 rg cmd ua ue)) by lia.
  rewrite U_lit by exact Hz. reflexivity.
Qed.

(* sp + c, from a state whose sp register is the atom 2. *)
Lemma iak_den_sp : forall rg l sp c, YK11.getr rg (Z_to_bv 5 2) = Z_to_bv 64 sp -> 0 <= sp < 2 ^ 64 ->
  sv_denot (Eimg (PI := PI_transport) (Ereg rg l)) (SOff 2 c) = Z_to_bv 64 (sp + c).
Proof.
  intros rg l sp c H2 Hsp. cbn [sv_denot]. rewrite (iak_E_reg rg l 2 (Z_to_bv 5 2) eq_refl), H2.
  rewrite unsigned_lit_small by exact Hsp. reflexivity.
Qed.

(* The incremented counter the stores write. *)
Lemma iak_inc_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)) = Z_to_bv 64 (bv_swrap 32 u + 1).
Proof.
  intros E n u Hn Hu.
  change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 1))).
  rewrite (iak_sext_den E n u Hn Hu). exact (iak_add_den (bv_swrap 32 u) 1).
Qed.

Lemma iak_int_inc : forall x y, TC.int_inc x = Some y -> y = x + 1.
Proof. intros x y H. unfold TC.int_inc in H. destruct (x =? TC.INT_MAX); [discriminate H|]. injection H as <-. reflexivity. Qed.
Lemma iak_got_acks : forall Bx, TW.GOT_acks Bx = bv_swrap 32 (TW.u_at Bx (TW.OFF_GOT + 204) 4).
Proof. reflexivity. Qed.
Lemma iak_got_e3 : forall Bx, TW.GOT_e3 Bx = bv_swrap 32 (TW.u_at Bx (TW.OFF_GOT + 200) 4).
Proof. reflexivity. Qed.
Lemma iak_set_acks : forall Bx v, TW.set_GOT_acks Bx v = TW.upd Bx (TW.OFF_GOT + 204) (TW.put 4 v).
Proof. reflexivity. Qed.
Lemma iak_set_e3 : forall Bx v, TW.set_GOT_e3 Bx v = TW.upd Bx (TW.OFF_GOT + 200) (TW.put 4 v).
Proof. reflexivity. Qed.

Lemma iak_put1 : forall v, 0 <= v < 256 -> nth 0 (map DSpec.bz (TW.put 1 v)) 0 = v.
Proof.
  intros v Hv. unfold TW.put.
  assert (E : nth_error (map DSpec.bz (Z_to_le_bytes 1 v)) 0 = Some v).
  { rewrite nth_error_map, (decode_leafb_nth_le_bytes 1 v 0 ltac:(lia)). cbn [option_map]. f_equal.
    unfold DSpec.bz. rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv. }
  erewrite (nth_error_nth _ _ _ E). reflexivity.
Qed.

(* s8 .. s11, which io_send never saves: kept from the entry registers. *)
Definition iak_hi (regs rg : bvmap 5 word) : Prop :=
  forall r, 24 <= r <= 27 -> YK11.getr rg (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r).

Lemma iak_hi_step : forall regs rg rg2 cmd, iak_hi regs rg -> iak_regs rg rg2 cmd -> iak_hi regs rg2.
Proof.
  intros regs rg rg2 cmd HH (HK & _) r Hr. rewrite <- (HH r Hr). apply HK.
  assert (E : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. unfold IAK_KEEP.
  destruct E as [-> | [-> | [-> | ->]]]; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

Lemma iak_regs_pres : forall rg rg2 rg3 cmd, iak_regs rg rg2 cmd -> aregs_preserved rg2 rg3 -> iak_regs rg rg3 cmd.
Proof.
  intros rg rg2 rg3 cmd (HK & H21) HP. split.
  - intros r Hr. rewrite (iak_keep_of_pres rg2 rg3 HP r Hr). exact (HK r Hr).
  - rewrite (iak_s5_of_pres rg2 rg3 HP). exact H21.
Qed.

(* The registers at the end of a run from the cut's state. *)
Lemma iak_regs_run : forall rg cmd ua ue ss (ms : machine_state) (Hh : word -> bool),
  st_ok_pi segs VAL (iak_E rg cmd ua ue) ss (restrict Hh ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) IAK_KEEP = true ->
  sr_get (ss_regs ss) 21%bv = SOff 32 0 ->
  iak_regs rg (ms_regs ms) cmd.
Proof.
  intros rg cmd ua ue ss ms Hh HS Hk H21. split.
  - intros r Hr. exact (regs_kept_of_st_ok_pi (iak_E rg cmd ua ue) ss (restrict Hh ms) rg
      [Z_to_bv 64 cmd; Z_to_bv 64 ua; Z_to_bv 64 ue] IAK_KEEP HS (iak_agree rg _) Hk r Hr).
  - rewrite (st_ok_pi_restrict_reg Hh _ ss ms 21%bv HS), H21. cbn [sv_denot].
    rewrite iak_E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma iak_regs_call : forall rg cmd ua ue ss (ms : machine_state) (Hh : word -> bool),
  YP0l.st_ok segs (iak_E rg cmd ua ue) ss (restrict Hh ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) IAK_KEEP = true ->
  sr_get (ss_regs ss) 21%bv = SOff 32 0 ->
  iak_regs rg (ms_regs ms) cmd.
Proof.
  intros rg cmd ua ue ss ms Hh HS Hk H21. split.
  - intros r Hr. exact (regs_kept_of_st_ok segs (iak_E rg cmd ua ue) ss (restrict Hh ms) rg
      [Z_to_bv 64 cmd; Z_to_bv 64 ua; Z_to_bv 64 ue] IAK_KEEP HS (iak_agree rg _) Hk r Hr).
  - rewrite (st_ok_restrict_reg segs Hh _ ss ms 21%bv HS), H21. cbn [sv_denot].
    rewrite iak_E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* What the exits hand on: the running facts at the cut, the saved words and the registers, from those at IOS_CSF
   and the bytes the stretch changed (Zs: below io_send's frame in its stack window, or bytes of G it stores). *)
Lemma iak_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p fail frame Bw
    ly2 S2 (W2 : world segs) mem2 md2 mem4 md4 rg rg4 cmd (Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 ->
  ios_saved W2 mem2 regs -> ios_regs regs rg p frame fail -> iak_hi regs rg ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem4 md4 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem4 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem4 a) ->
  (forall a, Zs a -> (spZ regs - IOSEND_STK <= a < spZ regs - IOSEND_FRAME) \/
                     (inG TG.G_HARNESS a /\ iosend_wr (Z.of_nat (length frame)) a)) ->
  iak_regs rg rg4 cmd ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem4 md4 /\
  ios_saved W2 mem4 regs /\ ios_regs regs rg4 p frame fail /\ iak_hi regs rg4.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p fail frame Bw ly2 S2 W2 mem2 md2 mem4 md4
    rg rg4 cmd Zs LAWS HGX HFX HCUR HSV HRG HHI HJ4 Hkp Hgr HZ Hregs.
  destruct (iak_geo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX)
    as (HAR & Hce & Hlo & Hhi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FR : IOSEND_FRAME = 160) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha)).
  assert (IS : 160 + 4096 <= IOSEND_STK) by (apply Z.leb_le; vm_compute; reflexivity).
  split.
  { apply (iak_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2
      mem4 md4 Zs LAWS HGX HFX HCUR HJ4 Hkp Hgr).
    intros a Ha. destruct (HZ a Ha) as [Hw | Hw]; [left; lia | right; exact Hw]. }
  split.
  { apply (iak_saved_kept W2 mem2 mem4 regs); [|exact HSV]. intros a Ha. apply Hkp; [lia|].
    intros HZa. destruct (HZ a HZa) as [Hw | [Hg _]]; [lia | pose proof (GLOW a Hg); lia]. }
  split; [exact (iak_ios_regs regs rg rg4 p frame fail HRG (proj1 Hregs)) |].
  exact (iak_hi_step regs rg rg4 cmd HHI Hregs).
Qed.

(* ------------------------------------------------------------------ *)
(* From IOS_CTRL: a0 = sp + 8, check_latest_control, `j` to IOS_EPI    *)
(* ------------------------------------------------------------------ *)

Lemma iak_ctrl : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) mem3 md3 k
    (rg3 : bvmap 5 word) (sp p : Z) (fr Bx : list byte) (Q : world segs -> config -> Prop),
  transport_cells B -> AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 k ->
  YK11.getr rg3 (Z_to_bv 5 2) = Z_to_bv 64 sp ->
  YK11.getr rg3 (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr rg3 (Z_to_bv 5 4) = w64 (as_tp B) ->
  iak_call_win STK sp0 sp ->
  trans_sframe_at W2 mem3 (sp + 8) p (TC.rf fr) ->
  tw_at TMAP_A (aview segs (w_H W2) mem3) Bx -> TC.check_latest_control_m Bx fr = Some (Bx, tt) ->
  (forall rg4 mem4 md4,
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly2 S2 W2 mem4 md4 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
        aview segs (w_H W2) mem4 a = aview segs (w_H W2) mem3 a) ->
     (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem4 a) ->
     aregs_preserved rg3 rg4 ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_EPI) rg4 mem4 md4) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CTRL) rg3 mem3 md3) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem3 md3 k rg3 sp p fr Bx Q HCELLS LAWS HGX LCLC HJ
    R2 R3 R4 HWIN HSF HTW HM HK.
  pose proof HWIN as (Hal & Hlo & Hhi).
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  clear HJ0 memS0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  pose proof (@paj_run_x fx rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
    HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
    HGX 0 []) as RUNTO.
  pose proof (iak_entry0 W2 rg3 mem3 IOS_CTRL) as HS.
  assert (HEI : img_env VAL A_LIM (iak_E0 rg3)) by (unfold iak_E0; apply Eimg_env).
  assert (SHOK : sh_ok segs IAK_Bx (@nil shent) (iak_E0 rg3) (mrestrict (w_H W2) mem3)) by constructor.
  unfold cfg_at.
  change (SRr segs W2 (mkCfg (@YK11.mkst fx rg3 (Z_to_bv 64 (BASE + IOS_CTRL)) mem3 (YK11.seg_rom segs)) md3) Q).
  (* 0x830dc: a0 = sp + 8; 0x830e0: jal check_latest_control *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { apply awr_ok_x_nil. }
  iak_md. rename ms into ms1.
  assert (K1 : forall x, ms_mem ms1 x = mem3 x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
  clear HF HFr HG.
  pose proof (aregs_preserved_of_st_ok segs (w_H W2) (iak_E0 rg3) _ ms1 rg3 [] HS (iak_agree rg3 [])
    ltac:(vm_compute; reflexivity)) as P1.
  iak_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 0x1e80)) Q1 ltac:(apply codeptr_val; assumption).
  iak_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (sp + 8)) Q10 ltac:(unfold iak_E0; apply iak_den_sp; [exact R2 | lia]).
  assert (Q2 : YK11.getr (ms_regs ms1) (Z_to_bv 5 2) = Z_to_bv 64 sp)
    by (rewrite (P1 2 ltac:(unfold acallee_saved; lia)); exact R2).
  assert (Q3 : YK11.getr (ms_regs ms1) (Z_to_bv 5 3) = w64 (as_gp B))
    by (rewrite (P1 3 ltac:(unfold acallee_saved; lia)); exact R3).
  assert (Q4 : YK11.getr (ms_regs ms1) (Z_to_bv 5 4) = w64 (as_tp B))
    by (rewrite (P1 4 ltac:(unfold acallee_saved; lia)); exact R4).
  assert (Qra : YK0s.ret_ok (YK11.getr (ms_regs ms1) (Z_to_bv 5 1)))
    by (rewrite Q1; apply (@ret_ok_codeptr_v rc transport_listing PI_transport); [lia | reflexivity]).
  assert (HSF1 : trans_sframe_at W2 (ms_mem ms1) (sp + 8) p (TC.rf fr))
    by (apply (iak_sframe_kept W2 mem3 (ms_mem ms1) (sp + 8) p (TC.rf fr));
        [intros a _; apply iak_aview_ext; exact K1 | exact HSF]).
  assert (HTW1 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms1)) Bx)
    by (apply (tw_kept TMAP_A _ _ Bx HTW); intros x _; apply iak_aview_ext; exact K1).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (YK11.mkst rgx (Z_to_bv 64 LLCc.CHECK_LATEST_CONTROL) mm rom) mdx) Qx) end.
  eapply SRr_bind.
  { exact (iak_call_clc STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms1) _ k (ms_regs ms1) sp p fr Bx
      HCELLS LAWS LCLC HJ Q2 Q10 Qra Q3 Q4 HWIN HSF1 HTW1 HM). }
  intros W3 c3 _ (-> & rg4 & mem4 & md4 & -> & HJ4 & HP4 & _ & HK4 & HG4 & _).
  rewrite Q1.
  (* 0x830e4: `j` to IOS_EPI *)
  pose proof (iak_entry0 W2 rg4 mem4 0x1e80) as HS2.
  assert (HEI2 : img_env VAL A_LIM (iak_E0 rg4)) by (unfold iak_E0; apply Eimg_env).
  assert (SHOK2 : sh_ok segs IAK_Bx (@nil shent) (iak_E0 rg4) (mrestrict (w_H W2) mem4)) by constructor.
  paj_run_to_tok RUNTO HS2 HJ4 SHOK2 YC4b.Bspan 0x2120.
  { apply awr_ok_x_nil. }
  iak_md. rename ms into ms5.
  assert (K5 : forall x, ms_mem ms5 x = mem4 x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
  clear HF HFr HG.
  pose proof (aregs_preserved_of_st_ok segs (w_H W2) (iak_E0 rg4) _ ms5 rg4 [] HS2 (iak_agree rg4 [])
    ltac:(vm_compute; reflexivity)) as P5.
  pmkst HS2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_EPI) (ms_regs ms5) (ms_mem ms5) mdx) Q) end.
  assert (SP1 : spZ (ms_regs ms1) = sp)
    by (change (spZ (ms_regs ms1)) with (bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2))); rewrite Q2;
        apply unsigned_lit_small; lia).
  apply HK.
  - exact HJ4.
  - intros a Ha Hn. rewrite (iak_aview_ext _ _ _ _ a K5).
    rewrite (HK4 a Ha ltac:(rewrite SP1; exact Hn) ltac:(intros X; inversion X)).
    apply iak_aview_ext. exact K1.
  - intros a Hp. apply (iak_present_ext _ _ _ a K5). apply HG4.
    apply (iak_present_ext _ _ _ a K1). exact Hp.
  - intros r Hr. rewrite (P5 r Hr), (HP4 r Hr), (P1 r Hr). reflexivity.
Qed.

(* The cut IOS_CSF's facts, at a memory equal to the cut's byte by byte (the dispatch's runs to IOS_E2DATA store
   nothing) and at the registers those runs leave. *)
Lemma iak_at_csf_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    ly2 S2 (W2 : world segs) mem2 md2 rg mem3 md3 rg2 cmd,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 rg ->
  0 < Z.of_nat (length frame) ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 (k + 0) ->
  (forall x, mem3 x = mem2 x) -> iak_regs rg rg2 cmd ->
  ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 rg2.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 rg mem3 md3 rg2
    cmd LAWS HGX HFX HAT Hlen HJ3 KM Hregs.
  pose proof HAT as (HCUR & HSV & HRG & HHI & HSF & HSRCS & HGA & HSRCF & HTW).
  destruct (iak_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p (TW.g_fail_next Bw) frame Bw
    ly2 S2 W2 mem2 md2 mem3 md3 rg rg2 cmd (fun _ => False) LAWS HGX HFX HCUR HSV HRG HHI HJ3
    (fun a _ _ => iak_aview_ext _ _ _ _ a KM) (fun a h => iak_present_ext _ _ _ a KM h)
    (fun a f => False_ind _ f) Hregs) as (HC3 & HS3 & HR3 & HH3).
  pose proof HCUR as (HJ2 & _).
  pose proof HJ2 as (_ & _ & (memA & HJa & _) & _). rewrite !Z.add_0_r in HJa. pose proof (proj1 HJa) as HAR2.
  pose proof HJ3 as (_ & _ & (memB & HJb & _) & _). rewrite !Z.add_0_r in HJb. pose proof (proj1 HJb) as HAR3.
  assert (KV : forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a)
    by (intros a; exact (iak_aview_ext _ _ _ _ a KM)).
  assert (ES : SF_SIZE = 80) by reflexivity.
  split; [exact HC3|]. split; [exact HS3|]. split; [exact HR3|]. split; [exact HH3|].
  split.
  { apply (iak_sframe_kept W2 mem2 mem3 _ p (TC.rf frame)); [intros a _; exact (KV a) | exact HSF]. }
  split.
  { exact (trans_src_ok_kept B LAWS ly2 S2 W2 mem2 md2 ly2 S2 W2 mem3 md3 _ SF_SIZE HAR2 HAR3
      (Permutation_refl _) eq_refl (fun c q => eq_refl) eq_refl eq_refl (fun a _ => KV a) (fun _ _ s _ _ => KV s)
      HSRCS ltac:(lia)). }
  split.
  { apply (iak_garr8_kept _ mem2 mem3 p _); [intros a _; exact (KV a) | exact HGA]. }
  split.
  { exact (trans_src_ok_kept B LAWS ly2 S2 W2 mem2 md2 ly2 S2 W2 mem3 md3 p (Z.of_nat (length frame)) HAR2 HAR3
      (Permutation_refl _) eq_refl (fun c q => eq_refl) eq_refl eq_refl (fun a _ => KV a) (fun _ _ s _ _ => KV s)
      HSRCF Hlen). }
  apply (tw_kept TMAP_A _ _ _ HTW). intros x _. exact (KV x).
Qed.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

(* From the cut IOS_CSF (io_send_seg_cut.v ios_at_csf, the return of check_sent_frame) to the exits of the dispatch
   on f.cmd:
   - f.cmd = 0 or 0xe2: transport_text + IOS_E2DATA, the cut's facts at a memory equal to the cut's, s5 = f.cmd;
   - f.cmd = 0xa0 (ACK: GOT.acks + 1, check_ack_frame, check_latest_control), 0xe3 (E3: GOT.e3 + 1,
     check_latest_control) or any other value: transport_text + IOS_EPI with what io_send_seg_epi.v ios_epi reads,
     at the world ios_arm leaves. *)
Definition ios_ack_seg_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw Bw' : list byte)
         ly2 S2 (W2 : world segs) mem2 md2 (rg : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_laws B MT ->
    ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 rg ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    ios_arm Bw frame = Some (Bw', tt) ->
    (* f.cmd = 0 or 0xe2: the E2 / DATA arm's head (another segment's) *)
    (forall rg2 mem3 md3,
       (DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2 \/ DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA) ->
       ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 rg2 ->
       YK11.getr rg2 21 = w64 (DSpec.sf_cmd (TC.rf frame)) ->
       (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
       (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
       SRr segs W2 (@cfg_at fx segs (transport_text + IOS_E2DATA) rg2 mem3 md3) Q) ->
    (* f.cmd = 0xa0, 0xe3 or any other value: the epilogue *)
    (forall rg2 mem3 md3,
       ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3 ->
       ios_saved W2 mem3 regs ->
       ios_regs regs rg2 p frame (TW.g_fail_next Bw) ->
       (forall r, 24 <= r <= 27 -> YK11.getr rg2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
       tw_at TMAP_A (aview segs (w_H W2) mem3) Bw' ->
       SRr segs W2 (@cfg_at fx segs (transport_text + IOS_EPI) rg2 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CSF) rg mem2 md2) Q.

Lemma ios_ack_seg : ios_ack_seg_stmt.
Proof.
  unfold ios_ack_seg_stmt.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' ly2 S2 W2 mem2 md2 rg Q
    HL HFX HAT HCSF HARM HE2 HEPI.
  pose proof HL as (HCELLS & _ & LAWS & _ & HGX & _ & _ & _ & LCAF & LCLC & _).
  destruct (iak_geo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX)
    as (HARc & Hce & Hlo & Hhi & H47 & Hsp0al & Hal).
  pose proof HAT as (HCUR & HSV & HRG & HHI & HSF & _ & _ & _ & HTW).
  pose proof HCUR as (HJ & _).
  pose proof HFX as (_ & _ & _ & Hgp & Htp & _).
  pose proof (ios_len60 _ _ _ HCSF) as Hlen.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FR : IOSEND_FRAME = 160) by reflexivity.
  assert (IS : 160 + 4096 <= IOSEND_STK) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (EST : ESTACK = 4096) by reflexivity.
  pose proof HRG as (R2 & R3 & R4 & _ & _ & _ & _).
  set (sp := spZ regs - IOSEND_FRAME) in *.
  assert (Esp : sp = spZ regs - IOSEND_FRAME) by reflexivity.
  change IOS_F_OFF with 8 in HSF.
  assert (Hsp : 2 ^ 46 <= sp <= 2 ^ 47 - 160) by lia.
  assert (Hsp16 : sp mod 16 = 0).
  { rewrite Esp, FR. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
  assert (R2' : YK11.getr rg (Z_to_bv 5 2) = Z_to_bv 64 sp) by exact R2.
  assert (R3' : YK11.getr rg (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite <- Hgp; exact R3).
  assert (R4' : YK11.getr rg (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite <- Htp; exact R4).
  assert (HSPU : spZ rg = sp)
    by (change (spZ rg) with (bv_unsigned (YK11.getr rg (Z_to_bv 5 2))); rewrite R2'; apply unsigned_lit_small; lia).
  assert (HWIN : iak_call_win STK sp0 sp) by (split; [exact Hsp16 | split; lia]).
  (* the struct f at sp + 8 and its cmd byte at sp + 48 *)
  pose proof HSF as (Hfp0 & Hfp8 & SB & HG & HLSB & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fcmd & _).
  remember (DSpec.sf_cmd (TC.rf frame)) as cmd eqn:Ecmd.
  assert (Rcmd : 0 <= cmd < 256).
  { pose proof (TWL.u_at_range SB 40 1) as R. rewrite Fcmd in R. exact R. }
  assert (Vcmd : val_mem segs (mrestrict (w_H W2) mem2) (spZ rg + 48) 1 cmd).
  { pose proof (iak_field _ (sp + 8) SB 40 1 cmd HG ltac:(lia) ltac:(rewrite HLSB; cbn; lia) Fcmd) as G1.
    destruct (G1 0%nat ltac:(rewrite length_map, TWL.length_put; lia)) as [HV _].
    rewrite (iak_put1 cmd Rcmd) in HV. rewrite HSPU. replace (sp + 48) with (sp + 8 + 40 + Z.of_nat 0) by (cbn; lia).
    exact HV. }
  (* the GOT words, as the world holds them *)
  pose (ua := TW.u_at (ios_B0 Bw) (TW.OFF_GOT + 204) 4).
  pose (ue := TW.u_at (ios_B0 Bw) (TW.OFF_GOT + 200) 4).
  assert (Rua : 0 <= ua < 2 ^ 32) by exact (TWL.u_at_range (ios_B0 Bw) (TW.OFF_GOT + 204) 4).
  assert (Rue : 0 <= ue < 2 ^ 32) by exact (TWL.u_at_range (ios_B0 Bw) (TW.OFF_GOT + 200) 4).
  assert (Vua : val_mem segs (mrestrict (w_H W2) mem2) (TA_GOT + 204) 4 ua)
    by exact (tw_read_val segs (mrestrict (w_H W2) mem2) TMAP_A (ios_B0 Bw) TW.OFF_GOT TA_GOT TW.SZ_GOT 204 4
      TMAP_A_ok HTW TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; cbn; lia)).
  assert (Vue : val_mem segs (mrestrict (w_H W2) mem2) (TA_GOT + 200) 4 ue)
    by exact (tw_read_val segs (mrestrict (w_H W2) mem2) TMAP_A (ios_B0 Bw) TW.OFF_GOT TA_GOT TW.SZ_GOT 200 4
      TMAP_A_ok HTW TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; cbn; lia)).
  (* the symbolic state at IOS_CSF *)
  assert (HS : st_ok_pi segs VAL (iak_E rg cmd ua ue) ss_iak
    (restrict (w_H W2) (@YK11.mkst fx rg (Z_to_bv 64 (BASE + IOS_CSF)) mem2 (YK11.seg_rom segs))))
    by (apply iak_entry; [rewrite HSPU; lia | rewrite HSPU; exact Hsp16 | exact Rcmd | exact Vcmd]).
  assert (HEI : img_env VAL A_LIM (iak_E rg cmd ua ue)) by (unfold iak_E; apply Eimg_env).
  assert (SHOK : sh_ok segs IAK_Bx (@nil shent) (iak_E rg cmd ua ue) (mrestrict (w_H W2) mem2)) by constructor.
  assert (U2 : bv_unsigned (ew (iak_E rg cmd ua ue) 2) = sp)
    by (unfold iak_E; rewrite (iak_E_reg rg _ 2 (Z_to_bv 5 2) eq_refl); exact HSPU).
  assert (U266 : bv_unsigned (ew (iak_E rg cmd ua ue) 266%nat) = IAK_ACKS)
    by (unfold iak_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
  assert (U267 : bv_unsigned (ew (iak_E rg cmd ua ue) 267%nat) = IAK_E3)
    by (unfold iak_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
  assert (U449 : bv_unsigned (ew (iak_E rg cmd ua ue) 449%nat) = IAK_ACKS - 0x30c)
    by (unfold iak_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
  assert (U450 : bv_unsigned (ew (iak_E rg cmd ua ue) 450%nat) = IAK_E3 - 0x2dc)
    by (unfold iak_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
  pose proof (@paj_run_x fx rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
    HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
    HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  (* the exits whose stretch writes nothing *)
  assert (XE2 : forall ms md3, (forall x, ms_mem ms x = mem2 x) ->
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly2 S2 W2 (ms_mem ms) md3 (k + 0) ->
     iak_regs rg (ms_regs ms) cmd -> (cmd = TC.SPEC_CMD_E2 \/ cmd = TC.SPEC_CMD_DATA) ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_E2DATA) (ms_regs ms) (ms_mem ms) md3) Q).
  { intros ms md3 KM HJ3 Hregs Hc.
    apply (HE2 (ms_regs ms) (ms_mem ms) md3 Hc).
    - exact (iak_at_csf_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2
        rg (ms_mem ms) md3 (ms_regs ms) cmd LAWS HGX HFX HAT ltac:(lia) HJ3 KM Hregs).
    - exact (proj2 Hregs).
    - intros a. exact (iak_aview_ext _ _ _ _ a KM).
    - intros a h. exact (iak_present_ext _ _ _ a KM h). }
  assert (XOTH : forall ms md3, (forall x, ms_mem ms x = mem2 x) ->
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly2 S2 W2 (ms_mem ms) md3 (k + 0) ->
     iak_regs rg (ms_regs ms) cmd ->
     cmd <> TC.SPEC_CMD_ACK -> cmd <> TC.SPEC_CMD_E2 -> cmd <> TC.SPEC_CMD_DATA -> cmd <> TC.SPEC_CMD_E3 ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_EPI) (ms_regs ms) (ms_mem ms) md3) Q).
  { intros ms md3 KM HJ3 Hregs N1 N2 N3 N4.
    rewrite Ecmd in N1, N2, N3, N4.
    pose proof (ios_arm_other Bw frame Bw' HARM N1 N2 N3 N4) as EBw'.
    destruct (iak_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p (TW.g_fail_next Bw) frame Bw
      ly2 S2 W2 mem2 md2 (ms_mem ms) md3 rg (ms_regs ms) cmd (fun _ => False) LAWS HGX HFX HCUR HSV HRG HHI HJ3
      (fun a _ _ => iak_aview_ext _ _ _ _ a KM) (fun a h => iak_present_ext _ _ _ a KM h)
      (fun a f => False_ind _ f) Hregs) as (HC3 & HS3 & HR3 & HH3).
    apply (HEPI (ms_regs ms) (ms_mem ms) md3 HC3 HS3 HR3 HH3). rewrite EBw'.
    apply (tw_kept TMAP_A _ _ _ HTW). intros x _. exact (iak_aview_ext _ _ _ _ x KM). }
  unfold cfg_at.
  change (SRr segs W2 (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + IOS_CSF)) mem2 (YK11.seg_rom segs)) md2) Q).
  (* 0x83088: s5 = f.cmd; a0 = 0xe1; it stops at `blt a0, s5` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { iak_awr U266 U449. }
  iak_md. rename ms into ms1.
  assert (K1 : forall x, ms_mem ms1 x = mem2 x) by (intros x; exact (iak_ro_frame _ _ _ HF x)).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan; rename Hc into Hb1; rewrite (iak_br_lt rg cmd ua ue Rcmd) in Hb1.
  - (* 0xe1 < f.cmd *)
    apply Z.ltb_lt in Hb1.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { iak_awr U266 U449. }
    iak_md. rename ms into ms2.
    assert (K2 : forall x, ms_mem ms2 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K1 x)).
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan; rename Hc into Hb2;
      rewrite (iak_br_eq rg cmd ua ue 226 Rcmd ltac:(lia)) in Hb2.
    + (* f.cmd = 0xe2 *)
      apply Z.eqb_eq in Hb2.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1e84.
      { iak_awr U266 U449. }
      iak_md. rename ms into ms3.
      assert (K3 : forall x, ms_mem ms3 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K2 x)).
      clear HF HFr HG.
      assert (Hregs : iak_regs rg (ms_regs ms3) cmd)
        by (apply (iak_regs_run rg cmd ua ue _ ms3 (w_H W2) HS); vm_compute; reflexivity).
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
        change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_E2DATA) (ms_regs ms3) (ms_mem ms3) mdx) Q) end.
      apply (XE2 ms3 _ K3 HJ Hregs). left. unfold TC.SPEC_CMD_E2. exact Hb2.
    + apply Z.eqb_neq in Hb2.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { iak_awr U266 U449. }
      iak_md. rename ms into ms3.
      assert (K3 : forall x, ms_mem ms3 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K2 x)).
      clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan; rename Hc into Hb3;
        rewrite (iak_br_ne rg cmd ua ue 227 Rcmd ltac:(lia)) in Hb3.
      * (* another value above 0xe3 *)
        apply negb_true_iff, Z.eqb_neq in Hb3.
        paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x2120.
        { iak_awr U266 U449. }
        iak_md. rename ms into ms4.
        assert (K4 : forall x, ms_mem ms4 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K3 x)).
        clear HF HFr HG.
        assert (Hregs : iak_regs rg (ms_regs ms4) cmd)
          by (apply (iak_regs_run rg cmd ua ue _ ms4 (w_H W2) HS); vm_compute; reflexivity).
        pmkst HS.
        lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
          change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_EPI) (ms_regs ms4) (ms_mem ms4) mdx) Q) end.
        apply (XOTH ms4 _ K4 HJ Hregs);
          unfold TC.SPEC_CMD_ACK, TC.SPEC_CMD_E2, TC.SPEC_CMD_DATA, TC.SPEC_CMD_E3; lia.
      * (* f.cmd = 0xe3: E3 *)
        apply negb_false_iff, Z.eqb_eq in Hb3.
        assert (Ec : DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E3) by (rewrite <- Ecmd; exact Hb3).
        destruct (ios_arm_e3 Bw frame Bw' HARM Ec) as (e3 & Ee & EBw' & HCLC).
        rewrite iak_got_e3 in Ee. apply iak_int_inc in Ee.
        (* GOT.e3 joins the state, as the load addresses it *)
        assert (RGe : region_ok segs (iak_E rg cmd ua ue) (mrestrict (w_H W2) (ms_mem ms3)) iak_e3_region).
        { unfold iak_e3_region, region_ok.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          change (A_OBJ 26) with 267%nat. rewrite U267.
          split; [unfold IAK_E3, TA_GOT; lia|]. split; [unfold IAK_E3, TA_GOT; lia|]. split.
          - intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (IAK_E3 + o) G_HARNESS_rw).
            apply (ios_inG_row _ _ _ _ TMAP_A_GOT). unfold IAK_E3, TW.SZ_GOT. lia.
          - constructor; [|constructor].
            apply (chunk_ok_val segs _ _ IAK_E3 0 4 (SOff 34 0) ue);
              [cbn [sv_denot]; rewrite iak_E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
            apply (iak_val_mem_ext segs (w_H W2) mem2 (ms_mem ms3) _ 4 ue K3).
            replace (IAK_E3 + 0) with (TA_GOT + 200) by (unfold IAK_E3; lia). exact Vue. }
        assert (DJe : all_disjoint (iak_E rg cmd ua ue) iak_e3_region [iak_cmd_region]).
        { cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, iak_e3_region, iak_cmd_region.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_OBJ 26) with 267%nat. rewrite U267, U2.
          left. unfold IAK_E3, TA_GOT. lia. }
        lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
          pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) iak_e3_region HS eq_refl RGe DJe) as HSe end.
        clear HS. iak_rw HSe.
        (* `bne` falls through; auipc; lw a1 = GOT.e3; a1 + 1; it stops at the store *)
        paj_run_tok RUN HSe HJ SHOK YC4b.Bspan.
        { iak_awr U267 U450. }
        iak_md. rename ms into ms4.
        assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (IAK_E3 <= a < IAK_E3 + 4) ->
          aview segs (w_H W2) (ms_mem ms4) a = aview segs (w_H W2) (ms_mem ms3) a).
        { apply (kept_of_frame _ _ _ _ _ (fun a => IAK_E3 <= a < IAK_E3 + 4) HFr).
          intros b wlo whi x Hin Hx. iak_win Hin Hx ltac:(rewrite ?U267, ?U450 in Hx; unfold IAK_E3 in *; lia). }
        assert (G4 : forall a, apresent (w_H W2) (ms_mem ms3) a -> apresent (w_H W2) (ms_mem ms4) a)
          by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
        clear HF HFr HG.
        (* the word, as the store addresses it *)
        lazymatch type of HSe with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
          let r0 := eval vm_compute in (nth 0 (ss_mem ss) iak_cmd_region) in
          pose proof (st_ok_pi_region_nth Ex ss (restrict Hh m) 0 r0 HSe ltac:(vm_compute; reflexivity)) as RG0;
          pose proof (st_ok_pi_submem Ex ss (restrict Hh m) [iak_cmd_region] HSe
            ltac:(vm_compute; apply submem_drop; apply submem_refl) eq_refl) as HSd end.
        pose proof (iak_rebase _ _ 267%nat 450%nat 0x2dc (SOff 34 0) RG0
          ltac:(rewrite U267, U450; unfold IAK_E3; lia) ltac:(rewrite U450; unfold IAK_E3, TA_GOT; lia)) as RGs.
        assert (DJs : all_disjoint (iak_E rg cmd ua ue) iak_e3_st [iak_cmd_region]).
        { cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, iak_e3_st, iak_cmd_region.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_HI 50) with 450%nat. rewrite U450, U2.
          left. unfold IAK_E3, TA_GOT. lia. }
        lazymatch type of HSd with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
          pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) iak_e3_st HSd eq_refl RGs DJs) as HSs end.
        clear HSe HSd RG0 RGs. iak_rw HSs.
        (* the store; it runs on to IOS_CTRL *)
        paj_run_to_tok RUNTO HSs HJ SHOK YC4b.Bspan 0x1e78.
        { iak_awr U267 U450. }
        iak_md. rename ms into ms5.
        assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (IAK_E3 <= a < IAK_E3 + 4) ->
          aview segs (w_H W2) (ms_mem ms5) a = aview segs (w_H W2) (ms_mem ms4) a).
        { apply (kept_of_frame _ _ _ _ _ (fun a => IAK_E3 <= a < IAK_E3 + 4) HFr).
          intros b wlo whi x Hin Hx. iak_win Hin Hx ltac:(rewrite ?U267, ?U450 in Hx; unfold IAK_E3 in *; lia). }
        assert (G5 : forall a, apresent (w_H W2) (ms_mem ms4) a -> apresent (w_H W2) (ms_mem ms5) a)
          by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
        clear HF HFr HG.
        lazymatch type of HSs with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
          let r0 := eval vm_compute in (nth 0 (ss_mem ss) iak_cmd_region) in
          pose proof (st_ok_pi_region_nth Ex ss (restrict Hh m) 0 r0 HSs ltac:(vm_compute; reflexivity)) as RG5 end.
        cbn [ms_mem restrict] in RG5.
        pose proof (iak_region_rd4 _ _ _ 450%nat _ _ _ _ _ _ e3 _ RG5 U450
          ltac:(rewrite Ee; exact (iak_inc_den _ 34 ue (iak_E34 rg cmd ua ue) Rue))) as V5.
        assert (Hregs : iak_regs rg (ms_regs ms5) cmd)
          by (apply (iak_regs_run rg cmd ua ue _ ms5 (w_H W2) HSs); vm_compute; reflexivity).
        (* the world after the store: Bw' *)
        assert (HTW5 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms5)) Bw').
        { rewrite EBw', iak_set_e3.
          apply (tw_write TMAP_A (aview segs (w_H W2) mem2) _ (ios_B0 Bw) TW.OFF_GOT TA_GOT TW.SZ_GOT 200 4 e3
            TMAP_A_ok HTW TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; cbn; lia)).
          - intros j Hj. rewrite <- (V5 j Hj). f_equal; unfold IAK_E3; lia.
          - intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh.
            unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
            rewrite (K5 x ltac:(lia) ltac:(unfold IAK_E3; cbn in Hn; lia)).
            rewrite (K4 x ltac:(lia) ltac:(unfold IAK_E3; cbn in Hn; lia)).
            apply iak_aview_ext. exact K3. }
        assert (HSF5 : trans_sframe_at W2 (ms_mem ms5) (sp + 8) p (TC.rf frame)).
        { apply (iak_sframe_kept W2 mem2 (ms_mem ms5) (sp + 8) p (TC.rf frame)); [|exact HSF].
          intros a Ha. rewrite (K5 a ltac:(lia) ltac:(unfold IAK_E3, TA_GOT; lia)).
          rewrite (K4 a ltac:(lia) ltac:(unfold IAK_E3, TA_GOT; lia)). apply iak_aview_ext. exact K3. }
        pmkst HSs.
        lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
          change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CTRL) (ms_regs ms5) (ms_mem ms5) mdx) Q) end.
        apply (iak_ctrl STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms5) _ (k + 0) (ms_regs ms5) sp p frame Bw'
          Q HCELLS LAWS HGX LCLC HJ
          (eq_trans (proj1 Hregs 2%bv ltac:(iak_kin)) R2') (eq_trans (proj1 Hregs 3%bv ltac:(iak_kin)) R3')
          (eq_trans (proj1 Hregs 4%bv ltac:(iak_kin)) R4') HWIN HSF5 HTW5 HCLC).
        intros rg4 mem4 md4 HJ4 HK4 HG4 HP4.
        pose proof (iak_regs_pres rg (ms_regs ms5) rg4 cmd Hregs HP4) as Hregs4.
        destruct (iak_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p (TW.g_fail_next Bw) frame Bw
          ly2 S2 W2 mem2 md2 mem4 md4 rg rg4 cmd (fun a => (IAK_E3 <= a < IAK_E3 + 4) \/ (sp - ESTACK <= a < sp))
          LAWS HGX HFX HCUR HSV HRG HHI HJ4) as (HC4 & HS4 & HR4 & HH4).
        { intros a Ha Hn. rewrite (HK4 a Ha ltac:(intros X; apply Hn; right; exact X)).
          rewrite (K5 a Ha ltac:(intros X; apply Hn; left; exact X)).
          rewrite (K4 a Ha ltac:(intros X; apply Hn; left; exact X)). apply iak_aview_ext. exact K3. }
        { intros a Hp. apply HG4. apply G5. apply G4.
          apply (iak_present_ext _ _ _ a K3). exact Hp. }
        { intros a [Ha | Ha]; [right | left; lia]. split.
          - apply (ios_inG_row _ _ _ _ TMAP_A_GOT). unfold IAK_E3, TW.SZ_GOT in *. lia.
          - apply ios_wr_got_e3. unfold IAK_E3 in Ha. lia. }
        { exact Hregs4. }
        apply (HEPI rg4 mem4 md4 HC4 HS4 HR4 HH4).
        apply (tw_kept TMAP_A _ _ Bw' HTW5). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
        unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply HK4; lia.
  - (* f.cmd <= 0xe1 *)
    apply Z.ltb_ge in Hb1.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { iak_awr U266 U449. }
    iak_md. rename ms into ms2.
    assert (K2 : forall x, ms_mem ms2 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K1 x)).
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan; rename Hc into Hb2;
      rewrite (iak_br_eq rg cmd ua ue 0 Rcmd ltac:(lia)) in Hb2.
    + (* f.cmd = 0: DATA *)
      apply Z.eqb_eq in Hb2.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1e84.
      { iak_awr U266 U449. }
      iak_md. rename ms into ms3.
      assert (K3 : forall x, ms_mem ms3 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K2 x)).
      clear HF HFr HG.
      assert (Hregs : iak_regs rg (ms_regs ms3) cmd)
        by (apply (iak_regs_run rg cmd ua ue _ ms3 (w_H W2) HS); vm_compute; reflexivity).
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
        change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_E2DATA) (ms_regs ms3) (ms_mem ms3) mdx) Q) end.
      apply (XE2 ms3 _ K3 HJ Hregs). right. unfold TC.SPEC_CMD_DATA. exact Hb2.
    + apply Z.eqb_neq in Hb2.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { iak_awr U266 U449. }
      iak_md. rename ms into ms3.
      assert (K3 : forall x, ms_mem ms3 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K2 x)).
      clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan; rename Hc into Hb3;
        rewrite (iak_br_ne rg cmd ua ue 160 Rcmd ltac:(lia)) in Hb3.
      * (* another value below 0xe2 *)
        apply negb_true_iff, Z.eqb_neq in Hb3.
        paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x2120.
        { iak_awr U266 U449. }
        iak_md. rename ms into ms4.
        assert (K4 : forall x, ms_mem ms4 x = mem2 x) by (intros x; rewrite (iak_ro_frame _ _ _ HF x); exact (K3 x)).
        clear HF HFr HG.
        assert (Hregs : iak_regs rg (ms_regs ms4) cmd)
          by (apply (iak_regs_run rg cmd ua ue _ ms4 (w_H W2) HS); vm_compute; reflexivity).
        pmkst HS.
        lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
          change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_EPI) (ms_regs ms4) (ms_mem ms4) mdx) Q) end.
        apply (XOTH ms4 _ K4 HJ Hregs);
          unfold TC.SPEC_CMD_ACK, TC.SPEC_CMD_E2, TC.SPEC_CMD_DATA, TC.SPEC_CMD_E3; lia.
      * (* f.cmd = 0xa0: ACK *)
        apply negb_false_iff, Z.eqb_eq in Hb3.
        assert (Ec : DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_ACK) by (rewrite <- Ecmd; exact Hb3).
        destruct (ios_arm_ack Bw frame Bw' HARM Ec) as (a0 & Ea & EBw' & HCAF & HCLC).
        rewrite iak_got_acks in Ea. apply iak_int_inc in Ea.
        (* GOT.acks joins the state, as the load addresses it *)
        assert (RGa : region_ok segs (iak_E rg cmd ua ue) (mrestrict (w_H W2) (ms_mem ms3)) iak_acks_region).
        { unfold iak_acks_region, region_ok.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          change (A_OBJ 25) with 266%nat. rewrite U266.
          split; [unfold IAK_ACKS, TA_GOT; lia|]. split; [unfold IAK_ACKS, TA_GOT; lia|]. split.
          - intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (IAK_ACKS + o) G_HARNESS_rw).
            apply (ios_inG_row _ _ _ _ TMAP_A_GOT). unfold IAK_ACKS, TW.SZ_GOT. lia.
          - constructor; [|constructor].
            apply (chunk_ok_val segs _ _ IAK_ACKS 0 4 (SOff 33 0) ua);
              [cbn [sv_denot]; rewrite iak_E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
            apply (iak_val_mem_ext segs (w_H W2) mem2 (ms_mem ms3) _ 4 ua K3).
            replace (IAK_ACKS + 0) with (TA_GOT + 204) by (unfold IAK_ACKS; lia). exact Vua. }
        assert (DJa : all_disjoint (iak_E rg cmd ua ue) iak_acks_region [iak_cmd_region]).
        { cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, iak_acks_region, iak_cmd_region.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_OBJ 25) with 266%nat. rewrite U266, U2.
          left. unfold IAK_ACKS, TA_GOT. lia. }
        lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
          pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) iak_acks_region HS eq_refl RGa DJa) as HSa end.
        clear HS. iak_rw HSa.
        (* `bne` falls through; auipc; lw a1 = GOT.acks; a1 + 1; it stops at the store *)
        paj_run_tok RUN HSa HJ SHOK YC4b.Bspan.
        { iak_awr U266 U449. }
        iak_md. rename ms into ms4.
        assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (IAK_ACKS <= a < IAK_ACKS + 4) ->
          aview segs (w_H W2) (ms_mem ms4) a = aview segs (w_H W2) (ms_mem ms3) a).
        { apply (kept_of_frame _ _ _ _ _ (fun a => IAK_ACKS <= a < IAK_ACKS + 4) HFr).
          intros b wlo whi x Hin Hx. iak_win Hin Hx ltac:(rewrite ?U266, ?U449 in Hx; unfold IAK_ACKS in *; lia). }
        assert (G4 : forall a, apresent (w_H W2) (ms_mem ms3) a -> apresent (w_H W2) (ms_mem ms4) a)
          by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
        clear HF HFr HG.
        (* the word, as the store addresses it *)
        lazymatch type of HSa with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
          let r0 := eval vm_compute in (nth 0 (ss_mem ss) iak_cmd_region) in
          pose proof (st_ok_pi_region_nth Ex ss (restrict Hh m) 0 r0 HSa ltac:(vm_compute; reflexivity)) as RG0;
          pose proof (st_ok_pi_submem Ex ss (restrict Hh m) [iak_cmd_region] HSa
            ltac:(vm_compute; apply submem_drop; apply submem_refl) eq_refl) as HSd end.
        pose proof (iak_rebase _ _ 266%nat 449%nat 0x30c (SOff 33 0) RG0
          ltac:(rewrite U266, U449; unfold IAK_ACKS; lia) ltac:(rewrite U449; unfold IAK_ACKS, TA_GOT; lia)) as RGs.
        assert (DJs : all_disjoint (iak_E rg cmd ua ue) iak_acks_st [iak_cmd_region]).
        { cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, iak_acks_st, iak_cmd_region.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_HI 49) with 449%nat. rewrite U449, U2.
          left. unfold IAK_ACKS, TA_GOT. lia. }
        lazymatch type of HSd with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
          pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) iak_acks_st HSd eq_refl RGs DJs) as HSs end.
        clear HSa HSd RG0 RGs. iak_rw HSs.
        (* the store; a0 = sp + 8; it stops at `jal check_ack_frame` *)
        paj_run_tok RUN HSs HJ SHOK YC4b.Bspan.
        { iak_awr U266 U449. }
        iak_md. rename ms into ms5.
        assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (IAK_ACKS <= a < IAK_ACKS + 4) ->
          aview segs (w_H W2) (ms_mem ms5) a = aview segs (w_H W2) (ms_mem ms4) a).
        { apply (kept_of_frame _ _ _ _ _ (fun a => IAK_ACKS <= a < IAK_ACKS + 4) HFr).
          intros b wlo whi x Hin Hx. iak_win Hin Hx ltac:(rewrite ?U266, ?U449 in Hx; unfold IAK_ACKS in *; lia). }
        assert (G5 : forall a, apresent (w_H W2) (ms_mem ms4) a -> apresent (w_H W2) (ms_mem ms5) a)
          by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
        clear HF HFr HG.
        lazymatch type of HSs with YP0l.st_ok ?sg ?Ex ?ss (restrict ?Hh ?m) =>
          let r0 := eval vm_compute in (nth 0 (ss_mem ss) iak_cmd_region) in
          pose proof (YC4b.st_ok_region_nth Ex ss (restrict Hh m) 0 r0 HSs ltac:(vm_compute; reflexivity)) as RG5 end.
        cbn [ms_mem restrict] in RG5.
        pose proof (iak_region_rd4 _ _ _ 449%nat _ _ _ _ _ _ a0 _ RG5 U449
          ltac:(rewrite Ea; exact (iak_inc_den _ 33 ua (iak_E33 rg cmd ua ue) Rua))) as V5.
        assert (Hregs : iak_regs rg (ms_regs ms5) cmd)
          by (apply (iak_regs_call rg cmd ua ue _ ms5 (w_H W2) HSs); vm_compute; reflexivity).
        (* the world after the store: Bw' *)
        assert (HTW5 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms5)) Bw').
        { rewrite EBw', iak_set_acks.
          apply (tw_write TMAP_A (aview segs (w_H W2) mem2) _ (ios_B0 Bw) TW.OFF_GOT TA_GOT TW.SZ_GOT 204 4 a0
            TMAP_A_ok HTW TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; cbn; lia)).
          - intros j Hj. rewrite <- (V5 j Hj). f_equal; unfold IAK_ACKS; lia.
          - intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh.
            unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
            rewrite (K5 x ltac:(lia) ltac:(unfold IAK_ACKS; cbn in Hn; lia)).
            rewrite (K4 x ltac:(lia) ltac:(unfold IAK_ACKS; cbn in Hn; lia)).
            apply iak_aview_ext. exact K3. }
        assert (HSF5 : trans_sframe_at W2 (ms_mem ms5) (sp + 8) p (TC.rf frame)).
        { apply (iak_sframe_kept W2 mem2 (ms_mem ms5) (sp + 8) p (TC.rf frame)); [|exact HSF].
          intros a Ha. rewrite (K5 a ltac:(lia) ltac:(unfold IAK_ACKS, TA_GOT; lia)).
          rewrite (K4 a ltac:(lia) ltac:(unfold IAK_ACKS, TA_GOT; lia)). apply iak_aview_ext. exact K3. }
        (* the registers at the call *)
        iak_reg HSs (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 0x1e54)) QA1 ltac:(apply codeptr_val; assumption).
        iak_reg HSs (Z_to_bv 5 10) (Z_to_bv 64 (sp + 8)) QA10
          ltac:(unfold iak_E; apply iak_den_sp; [exact R2' | lia]).
        assert (QAra : YK0s.ret_ok (YK11.getr (ms_regs ms5) (Z_to_bv 5 1)))
          by (rewrite QA1; apply (@ret_ok_codeptr_v rc transport_listing PI_transport); [lia | reflexivity]).
        pmkst HSs.
        lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
          change (SRr sg Wx (mkCfg (YK11.mkst rgx (Z_to_bv 64 LAFc.CHECK_ACK_FRAME) mm rom) mdx) Qx) end.
        eapply SRr_bind.
        { exact (iak_call_caf STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms5) _ (k + 0) (ms_regs ms5) sp p
            frame Bw' HCELLS LAWS LCAF HJ (eq_trans (proj1 Hregs 2%bv ltac:(iak_kin)) R2') QA10 QAra
            (eq_trans (proj1 Hregs 3%bv ltac:(iak_kin)) R3') (eq_trans (proj1 Hregs 4%bv ltac:(iak_kin)) R4')
            HWIN HSF5 HTW5 HCAF). }
        intros W3 c3 _ (-> & rg6 & mem6 & md6 & -> & HJ6 & HP6 & _ & HK6 & HG6 & _).
        rewrite QA1.
        assert (SP5 : spZ (ms_regs ms5) = sp).
        { assert (Q52 : YK11.getr (ms_regs ms5) (Z_to_bv 5 2) = Z_to_bv 64 sp)
            by exact (eq_trans (proj1 Hregs 2%bv ltac:(iak_kin)) R2').
          change (spZ (ms_regs ms5)) with (bv_unsigned (YK11.getr (ms_regs ms5) (Z_to_bv 5 2))).
          rewrite Q52. apply unsigned_lit_small. lia. }
        pose proof (iak_regs_pres rg (ms_regs ms5) rg6 cmd Hregs HP6) as Hregs6.
        (* 0x830b8: `j` to IOS_CTRL *)
        pose proof (iak_entry0 W2 rg6 mem6 0x1e54) as HS6.
        assert (HEI6 : img_env VAL A_LIM (iak_E0 rg6)) by (unfold iak_E0; apply Eimg_env).
        assert (SHOK6 : sh_ok segs IAK_Bx (@nil shent) (iak_E0 rg6) (mrestrict (w_H W2) mem6)) by constructor.
        paj_run_to_tok RUNTO HS6 HJ6 SHOK6 YC4b.Bspan 0x1e78.
        { apply awr_ok_x_nil. }
        iak_md. rename ms into ms7.
        assert (K7 : forall x, ms_mem ms7 x = mem6 x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
        clear HF HFr HG.
        pose proof (aregs_preserved_of_st_ok segs (w_H W2) (iak_E0 rg6) _ ms7 rg6 [] HS6 (iak_agree rg6 [])
          ltac:(vm_compute; reflexivity)) as P7.
        pose proof (iak_regs_pres rg rg6 (ms_regs ms7) cmd Hregs6 P7) as Hregs7.
        assert (K67 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
          aview segs (w_H W2) (ms_mem ms7) a = aview segs (w_H W2) (ms_mem ms5) a).
        { intros a Ha Hn. rewrite (iak_aview_ext _ _ _ _ a K7).
          exact (HK6 a Ha ltac:(rewrite SP5; exact Hn) ltac:(intros X; inversion X)). }
        assert (HSF7 : trans_sframe_at W2 (ms_mem ms7) (sp + 8) p (TC.rf frame))
          by (apply (iak_sframe_kept W2 (ms_mem ms5) (ms_mem ms7) (sp + 8) p (TC.rf frame)); [|exact HSF5];
              intros a Ha; apply K67; lia).
        assert (HTW7 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms7)) Bw').
        { apply (tw_kept TMAP_A _ _ Bw' HTW5). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
          unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply K67; lia. }
        pmkst HS6.
        lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
          change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CTRL) (ms_regs ms7) (ms_mem ms7) mdx) Q) end.
        apply (iak_ctrl STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms7) _ (k + 0) (ms_regs ms7) sp p frame
          Bw' Q HCELLS LAWS HGX LCLC HJ6
          (eq_trans (proj1 Hregs7 2%bv ltac:(iak_kin)) R2') (eq_trans (proj1 Hregs7 3%bv ltac:(iak_kin)) R3')
          (eq_trans (proj1 Hregs7 4%bv ltac:(iak_kin)) R4') HWIN HSF7 HTW7 HCLC).
        intros rg4 mem4 md4 HJ4 HK4 HG4 HP4.
        pose proof (iak_regs_pres rg (ms_regs ms7) rg4 cmd Hregs7 HP4) as Hregs4.
        destruct (iak_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p (TW.g_fail_next Bw) frame Bw
          ly2 S2 W2 mem2 md2 mem4 md4 rg rg4 cmd (fun a => (IAK_ACKS <= a < IAK_ACKS + 4) \/ (sp - ESTACK <= a < sp))
          LAWS HGX HFX HCUR HSV HRG HHI HJ4) as (HC4 & HS4 & HR4 & HH4).
        { intros a Ha Hn. rewrite (HK4 a Ha ltac:(intros X; apply Hn; right; exact X)).
          rewrite (K67 a Ha ltac:(intros X; apply Hn; right; exact X)).
          rewrite (K5 a Ha ltac:(intros X; apply Hn; left; exact X)).
          rewrite (K4 a Ha ltac:(intros X; apply Hn; left; exact X)). apply iak_aview_ext. exact K3. }
        { intros a Hp. apply HG4. apply (iak_present_ext _ _ _ a K7). apply HG6. apply G5.
          apply G4. apply (iak_present_ext _ _ _ a K3). exact Hp. }
        { intros a [Ha | Ha]; [right | left; lia]. split.
          - apply (ios_inG_row _ _ _ _ TMAP_A_GOT). unfold IAK_ACKS, TW.SZ_GOT in *. lia.
          - apply ios_wr_got_acks. unfold IAK_ACKS in Ha. lia. }
        { exact Hregs4. }
        apply (HEPI rg4 mem4 md4 HC4 HS4 HR4 HH4).
        apply (tw_kept TMAP_A _ _ Bw' HTW7). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
        unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply HK4; lia.
Qed.

End x.
