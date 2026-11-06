(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths, module names and numbers changed; 1057 of its 1130 lines of code are new or changed and 692 lines of the source are left out. *)
(* io_send_seg_dmid: the middle of the DATA arm of the image-B walk of io_send (fuzz_transport.asan-ubsan
   41113a03c82f, entry 0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt), from the cut IOS_CMDS (0x83220 = transportb_text + IOS_AT 0x224) to the two
   exits IOS_KA (0x83254, the keepalive case) and IOS_SENT (0x8328c, the check_latest_sent case): the segment
   statement lib/B/Prog/io_send_seg_cut.v iod_mid_stmt.

   The code (io_send_cg.v header; listing slots of lib/B/Prog/DgnTransportBList.v):
     0x83220 - 0x83228  a0 = sp + 8, a1 = s2 (the count cmds); call of check_latest_frame (0x8478c), return
                        address 0x8322c;
     0x8322c - 0x83250  a1 = f.send (the 4-byte load at sp + 40); a0 = g_raw (the 4-byte load at -1056 (s6),
                        s6 = io_send_seg_cut.v IOS_S6 = g_raw + 1056); s2 = M (`auipc` + PAddHi, the listing's
                        object 8); the 4-byte store of f.send at M + 84 (M.host_counter); a2 = (g_raw <u 1) & s5;
                        the 4-byte store of f.send at -1160 (a3), a3 the listing's A_HI 59 = g_last_counter + 1160;
                        a2 = 0 goes to 0x8328c (IOS_SENT, a0 = g_raw), else on to 0x83254 (IOS_KA).
   `sp` here is the walk's sp (the entry sp less IOSEND_FRAME = 160). The stretch holds no instrumented check and no
   branch to the trap word.

   The walk: two runs of TransportGRunB.v paj_run_x / paj_run_to_x over the caller's G journal and one leaf call
   through TransportGCg.v gx_call_leaf and the leaf bridge DgnTransportBLeafb.v decode_leafb_journal.
     idm_call_clf  the call of check_latest_frame (lib/B/Prog/check_latest_frame_cg.v through transport_leaf_at;
                   a0 = sp + 8, a1 = bv_swrap 32 cmds; it reads f.send, f.ncmds and f.body_len of the struct);
     idm_callC     0x83220 .. 0x83228 joined to that call, from IOS_CMDS to the return 0x8322c;
     idm_entryD    the symbolic state at 0x8322c (f.send, g_raw through s6, and M.host_counter);
     idm_runD      0x8322c .. 0x83250: the two 4-byte stores of f.send into G, one TWorldG.v tw_write each at the
                   rows TMAP_B_M and TMAP_B_g_last_counter (the world io_send_seg_cut.v ios_B5), and the last branch
                   `beq ((g_raw <u 1) & s5), 0`, giving the two exits with their case facts;
     iod_mid       the three joined, from the cut iod_at to the exits' ios_tail_at at ios_B5 Bw frame.
   Each store is a byte of G (W_journalG.v awr_ok_x's G case) and of io_send_cg.v iosend_wr (io_send_seg_world.v
   ios_wr_hostc / ios_wr_lastc), so the running kept fact holds on (idm_cur_step); the leaf keeps every byte outside
   its ESTACK window below sp, so the struct, the frame bytes, the saved words and the world relation hold on; the
   two stores miss g_raw's world bytes, so the case fact reads g_raw at ios_B5 as at ios_B0.
   Ported from image A's lib/A/Prog/io_send_seg_data.v (iod_call_clf, iod_callC, iod_entryD, iod_runD) and the join
   in lib/A/Prog/io_send_seg_dpost.v, at image B's names; the helpers copied from lib/A/Prog/io_send_seg_ack.v and
   io_send_seg_data.v carry the prefix idm_. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBLeafb LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCgRun CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg io_send_cg check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require check_latest_frame_cg check_latest_frame_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_frame_cg.
Module LLFc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_frame_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The addresses of the stretch                                        *)
(* ------------------------------------------------------------------ *)

(* The return of check_latest_frame (0x8322c). *)
Definition IDM_CLF_RET : Z := IOS_AT 0x230.

Lemma idm_addrs :
  transportb_text + IOS_CMDS = 0x83220 /\ transportb_text + IDM_CLF_RET = 0x8322c /\
  transportb_text + IOS_KA = 0x83254 /\ transportb_text + IOS_SENT = 0x8328c.
Proof. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Bytes, words and branches                                           *)
(* ------------------------------------------------------------------ *)

Lemma idm_bow : forall v j, (j < 4)%nat ->
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

(* The value a signed 4-byte load leaves. *)
Lemma idm_sext32_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* bv_eqb of two 64-bit literals. *)
Lemma idm_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
intros x y Hx Hy. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma idm_sltu_den : forall (x y : word),
  alu64 ALU_SLTU x y = Z_to_bv 64 (if bv_unsigned x <? bv_unsigned y then 1 else 0).
Proof.
intros x y. cbn [alu64 alu]. rewrite bv_ltu_unsigned.
destruct (bv_unsigned x <? bv_unsigned y); reflexivity.
Qed.

(* A signed wrap does not change the low bytes a store writes. *)
Lemma idm_swrap_mod : forall (n : N) z, bv_swrap n z mod 2 ^ Z.of_N n = z mod 2 ^ Z.of_N n.
Proof.
intros n z. unfold bv_swrap, bv_wrap, bv_modulus. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma idm_le_byte_swrap : forall (n : N) (w j : nat) v, Z.of_N n = 8 * Z.of_nat w ->
  YO0f.le_byte (bv_swrap n v) w j = YO0f.le_byte v w j.
Proof.
intros n w j v Hn. unfold YO0f.le_byte. rewrite <- Hn, idm_swrap_mod. reflexivity.
Qed.

(* The last branch's condition, 0x83240 - 0x83250: g_raw = 0 AND the keepalive flag. *)
Lemma idm_andb_den : forall a b, 0 <= a <= 1 -> 0 <= b <= 1 ->
  alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if ((a =? 1) && (b =? 1))%bool then 1 else 0).
Proof.
intros a b Ha Hb.
assert (Ea : a = 0 \/ a = 1) by lia. assert (Eb : b = 0 \/ b = 1) by lia.
destruct Ea as [Ea0|Ea1]; destruct Eb as [Eb0|Eb1]; subst; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma idm_cond_den : forall E n m (gs s : Z), sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 gs ->
  - 2 ^ 31 <= gs < 2 ^ 31 -> ew E m = Z_to_bv 64 s -> 0 <= s <= 1 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SExt true 32 (SOff n 0)) (SLit 1)) (SOff m 0))
    = Z_to_bv 64 (if (negb (TC.truth gs) && (s =? 1))%bool then 1 else 0).
Proof.
intros E n m gs s Hg Hr Hm Hs.
change (sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SExt true 32 (SOff n 0)) (SLit 1)) (SOff m 0)))
  with (alu64 ALU_AND (alu64 ALU_SLTU (sv_denot E (SExt true 32 (SOff n 0))) (Z_to_bv 64 1))
          (sv_denot E (SOff m 0))).
assert (Hden : sv_denot E (SOff m 0) = Z_to_bv 64 s)
  by (cbn [sv_denot]; rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rewrite Hg, Hden, idm_sltu_den.
assert (Hlt : (bv_unsigned (Z_to_bv 64 gs) <? bv_unsigned (Z_to_bv 64 1)) = negb (TC.truth gs)).
{ change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. unfold TC.truth.
  destruct (Z.eqb_spec gs 0) as [->|Hne]; [reflexivity|].
  destruct (Z_lt_le_dec gs 0) as [Hl|Hge].
  - assert (Hm2 : gs mod 18446744073709551616 = gs + 18446744073709551616).
    { rewrite <- (Z.mod_add gs 1 18446744073709551616) by lia. rewrite Z.mul_1_l. apply Z.mod_small. lia. }
    rewrite Hm2. cbn [negb]. apply Z.ltb_ge. lia.
  - rewrite Z.mod_small by lia. cbn [negb]. apply Z.ltb_ge. lia. }
rewrite Hlt.
rewrite (idm_andb_den (if negb (TC.truth gs) then 1 else 0) s
  ltac:(destruct (negb (TC.truth gs)); lia) Hs).
f_equal. destruct (TC.truth gs); cbn [negb]; destruct (Z.eqb_spec s 1); cbn [andb]; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the struct                                                  *)
(* ------------------------------------------------------------------ *)

(* Byte j of the little-endian value of a byte list of n bytes. *)
Lemma idm_le_byte_n : forall (l : list byte) (n j : nat) d, length l = n -> (j < n)%nat ->
  YO0f.le_byte (bytes_le_to_Z l) n j = bv_unsigned (nth j l d).
Proof. intros l n j d <- Hj. exact (tw_le_byte_ble l j d Hj). Qed.

(* Byte j of the n-byte field at offset k of a byte list. *)
Lemma idm_u_at_byte : forall (L : list byte) (k n j : nat), (k + n <= length L)%nat -> (j < n)%nat ->
  YO0f.le_byte (TW.u_at L (Z.of_nat k) n) n j = bv_unsigned (nth (k + j) L (Z_to_bv 8 0)).
Proof.
intros L k n j Hkn Hj.
assert (HL : length (TW.sub L (Z.of_nat k) n) = n) by (apply TWL.length_sub; lia).
unfold TW.u_at.
rewrite (idm_le_byte_n (TW.sub L (Z.of_nat k) n) n j (Z_to_bv 8 0) HL Hj).
rewrite (tw_nth_sub L (Z.of_nat k) n j (Z_to_bv 8 0) ltac:(lia) Hj ltac:(lia)).
replace (Z.to_nat (Z.of_nat k) + j)%nat with (k + j)%nat by lia. reflexivity.
Qed.

(* The n-byte field at offset k of a byte list the view shows at q, as a chunk value. *)
Lemma idm_val_of_garr8 : forall (mm : word -> option byte) q (L : list byte) (k n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> (k + n <= length L)%nat ->
  YI04.val_mem tfibsegs mm (q + Z.of_nat k) n (TW.u_at L (Z.of_nat k) n).
Proof.
intros mm q L k n Hg Hkn j Hj.
assert (Hj2 : (k + j < length (map DSpec.bz L))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte tfibsegs mm q (map DSpec.bz L) (k + j) Hg Hj2) as Hm.
replace (q + Z.of_nat k + Z.of_nat j) with (q + Z.of_nat (k + j)) by lia.
rewrite Hm. f_equal. f_equal.
rewrite (idm_u_at_byte L k n j Hkn Hj).
change (nth (k + j) (map DSpec.bz L) 0) with (nth (k + j) (map DSpec.bz L) (DSpec.bz (Z_to_bv 8 0))).
rewrite map_nth. reflexivity.
Qed.

Lemma idm_val_at : forall (mm : word -> option byte) q (L : list byte) (k : Z) (n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  YI04.val_mem tfibsegs mm (q + k) n (TW.u_at L k n).
Proof.
intros mm q L k n Hg Hk Hkn. replace k with (Z.of_nat (Z.to_nat k)) by lia.
apply (idm_val_of_garr8 mm q L (Z.to_nat k) n Hg). lia.
Qed.

(* put n of the value of n bytes of a list is those n bytes. *)
Lemma idm_put_sub : forall (SB : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  TW.put n (TW.u_at SB k n) = TW.sub SB k n.
Proof.
  intros SB k n Hk Hl. pose proof (TWL.length_sub SB k n Hk Hl) as L. unfold TW.put, TW.u_at.
  remember (TW.sub SB k n) as s eqn:Es. rewrite <- L. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma idm_nth_sub : forall (SB : list byte) k n j, 0 <= k -> (j < n)%nat ->
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

Lemma idm_garr8_sub : forall (m : word -> option byte) p (SB : list byte) k n,
  garr8 tfibsegs m p (map DSpec.bz SB) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  garr8 tfibsegs m (p + k) (map DSpec.bz (TW.sub SB k n)).
Proof.
  intros m p SB k n HG Hk Hl j Hj.
  rewrite length_map, (TWL.length_sub SB k n Hk Hl) in Hj.
  rewrite (idm_nth_sub SB k n j Hk Hj Hl).
  assert (Hj' : (Z.to_nat k + j < length (map DSpec.bz SB))%nat) by (rewrite length_map; lia).
  replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
  exact (HG _ Hj').
Qed.

(* A field of n bytes at offset k of the struct's byte list, of value v. *)
Lemma idm_field : forall (m : word -> option byte) p (SB : list byte) k n v,
  garr8 tfibsegs m p (map DSpec.bz SB) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  TW.u_at SB k n = v -> garr8 tfibsegs m (p + k) (map DSpec.bz (TW.put n v)).
Proof.
  intros m p SB k n v HG Hk Hl Hv. subst v. rewrite (idm_put_sub SB k n Hk Hl).
  exact (idm_garr8_sub m p SB k n HG Hk Hl).
Qed.

(* ------------------------------------------------------------------ *)
(* Kept bytes                                                          *)
(* ------------------------------------------------------------------ *)

Lemma idm_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) base l,
  (forall a, base <= a < base + Z.of_nat (length l) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m) base l -> garr8 tfibsegs (mrestrict H m') base l.
Proof.
  intros H m m' base l Heq HG. apply (garr8_frame tfibsegs _ _ base l HG).
  intros a Ha. apply (mbyte_of_aview tfibsegs). apply Heq. exact Ha.
Qed.

Lemma idm_sframe_kept : forall (W : world tfibsegs) mem mem' p fa f,
  (forall a, p <= a < p + 80 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  trans_sframe_at W mem p fa f -> trans_sframe_at W mem' p fa f.
Proof.
  intros W mem mem' p fa f Heq (H0 & H8 & SB & HG & HL & R). split; [exact H0|]. split; [exact H8|].
  exists SB. split; [|split; [exact HL | exact R]].
  apply (idm_garr8_kept _ mem mem' p _); [|exact HG].
  intros a Ha. rewrite length_map, HL in Ha. change (Z.of_nat 80) with 80 in Ha. apply Heq. exact Ha.
Qed.

Lemma idm_rdword_eq : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) ->
  rdword r' a = rdword r a.
Proof.
  intros r r' a H. unfold rdword.
  assert (E0 : r' a = r a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma idm_saved_kept : forall (W : world tfibsegs) mem mem' regs,
  (forall a, spZ regs - 72 <= a < spZ regs -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ios_saved W mem regs -> ios_saved W mem' regs.
Proof.
  intros W mem mem' regs Heq HS. unfold ios_saved in *. rewrite Forall_forall in HS |- *.
  intros o Ho. rewrite <- (HS o Ho). apply idm_rdword_eq. intros i Hi. apply Heq.
  unfold IOS_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho.
Qed.

(* A range of n bytes at x + k, x 8-aligned, inside one granule has one shadow byte. *)
Lemma idm_shadow_one : forall x k n, 0 <= x -> x mod 8 = 0 -> 0 <= k -> 0 < n -> k mod 8 + n <= 8 ->
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

Lemma idm_aview_ext : forall segs0 (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview segs0 H m' a = aview segs0 H m a.
Proof. intros segs0 H m m' a Hx. unfold aview, YP09.mbyte, mrestrict. rewrite Hx. reflexivity. Qed.

Lemma idm_present_ext : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a Hx [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hx. exact Hb. Qed.

(* A register of the callee-saved set, kept by a call (aregs_preserved). *)
Lemma idm_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof.
intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H.
rewrite !stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The harness globals are visible                                     *)
(* ------------------------------------------------------------------ *)

Lemma idm_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. apply (decode_vis_seg W).
  apply (decode_covers_img TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) x);
    [vm_compute; reflexivity | lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory the leaf reads. *)
Lemma idm_tw_csw : forall (W : world tfibsegs) mem Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) mem) Bw -> tw_at TMAP_B (CSW.csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  unfold CSW.csw_view. rewrite (decode_aview_mrd W mem x (idm_hull_vis W x (TMAP_B_hull x Hx))). reflexivity.
Qed.

(* A range of the harness globals' hull is visible, so a leaf's footprint may read it. *)
Lemma idm_rng_hull : forall (W : world tfibsegs) lo len,
  TG.G_HARNESS_B_LO <= lo -> lo + len <= TG.G_HARNESS_B_HI ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2.
  apply (decode_rng W); [unfold TG.G_HARNESS_B_LO in *; lia | unfold TG.G_HARNESS_B_HI in *; lia |].
  intros b Hb. apply idm_hull_vis. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Region reads                                                        *)
(* ------------------------------------------------------------------ *)

(* The 4 bytes of the one chunk of a region, read through the view. *)
Lemma idm_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok tfibsegs E (mrestrict H mm) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview tfibsegs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview tfibsegs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte tfibsegs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply idm_bow. exact Hj.
Qed.

Lemma idm_region_rd4 : forall E (H : word -> bool) (mm : word -> option byte) n lo hi wlo whi off e v b,
  region_ok tfibsegs E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi [YP09.mkChunk off (CVal 4 e)]) ->
  bv_unsigned (ew E n) = b -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview tfibsegs H mm (b + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
  intros E H mm n lo hi wlo whi off e v b (_ & _ & _ & HC) Hb Hv.
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite Hb in HC. apply Forall_inv in HC.
  exact (idm_chunk_rd E H mm b off e v HC Hv).
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state of run D                                         *)
(* ------------------------------------------------------------------ *)

(* run D (0x8322c .. 0x83250). Atoms: 0 .. 31 the registers at the return of check_latest_frame (2 = sp, 20 = s4 the
   shadow base, 21 = s5 the keepalive flag, 22 = s6 = IOS_S6), 32 = f.send, 33 = g_raw. Regions: io_send's frame
   (read-only) with f.send at sp + 40, g_raw read through s6 (-1056), and M's host_counter (writable, through the
   listing's object 8). g_last_counter's region, through the listing's A_HI 59 (1160 above it), joins after the first
   store. *)
Definition idm_frameD : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 160 0 0 [YP09.mkChunk 40 (CVal 4 (SOff 32 0))].
Definition idm_rawD : YP09.region :=
  YP09.mkRegion (Some 22%nat) (-1056) (-1052) 0 0 [YP09.mkChunk (-1056) (CVal 4 (SOff 33 0))].
Definition idm_hostD : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 84 88 84 88 [].
Definition idm_lastD : YP09.region := YP09.mkRegion (Some (A_HI 59)) (-1160) (-1156) (-1160) (-1156) [].
Definition idm_regionsD : smem := [idm_frameD; idm_rawD; idm_hostD].
Definition idm_factsD : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (22%nat, mkAF IOS_S6 IOS_S6 4);
           (A_OBJ 8, mkAF TB_M TB_M 5);
           (A_HI 59, mkAF (TB_g_last_counter + 1160) (TB_g_last_counter + 1160) 3)] [] [].
Definition idm_ssD : sstate := mkSS IDM_CLF_RET sr_atoms idm_regionsD None idm_factsD.

(* The token engine's shadow base (s4) and its shadow entries (none: the stretch has no instrumented check). *)
Definition IDM_Bx : sv := SOff 20 0.
Definition IDM_SH : list shent := [].

(* A state with no region and no fact, from the concrete registers. *)
Definition idm_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac idm_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "idm_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac idm_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run whose regions are all read-only. *)
Ltac idm_awrA :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The write rights of run D: the two words it stores are bytes of G (M.host_counter, g_last_counter). *)
Ltac idm_awrD UM U59 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite UM in Ha; apply (ios_inG_row _ _ _ a TMAP_B_M); unfold TW.SZ_M in *; lia
            | rewrite U59 in Ha; apply (ios_inG_row _ _ _ a TMAP_B_g_last_counter);
              unfold TW.SZ_g_last_counter in *; lia ]
    |]);
  apply awr_ok_x_nil.

(* Normalize a symbolic state in place. *)
Ltac idm_rw HS := lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.

(* A register index is callee-saved: compute its number, then compare. *)
Ltac idm_cs :=
  unfold acallee_saved;
  repeat (lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end);
  lia.

(* The value of a register of a stopped run, as the symbolic value its state names. *)
Ltac idm_rv HS :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      lazymatch goal with
      | |- YK11.getr (ms_regs _) ?r = _ =>
          let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
          refine (eq_trans (st_ok_restrict_reg sg Hh Ex ssx msx r HS) _);
          change (sv_denot Ex (sr_get (ss_regs ssx) r)) with (sv_denot Ex e)
      end
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      lazymatch goal with
      | |- YK11.getr (ms_regs _) ?r = _ =>
          let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
          refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _);
          change (sv_denot Ex (sr_get (ss_regs ssx) r)) with (sv_denot Ex e)
      end
  end.

(* A register is in a literal list of registers. *)
Ltac idm_kin := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).

(* The registers kept from IOS_CMDS to the return of check_latest_frame: io_send's own (callee-saved). *)
Definition IDM_KEEPC : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* The registers run D keeps: io_send's own but s2, which it loads with M. *)
Definition IDM_KEEPD : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* The eight bytes of G run D writes. *)
Definition IDM_WR (a : Z) : Prop :=
  (TB_M + 84 <= a < TB_M + 88) \/ (TB_g_last_counter <= a < TB_g_last_counter + 4).

Section dmid. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The close of one exit of run D: the memory is the one after the two stores, the world is at B5. It leaves
   the kept registers, s2 = M and the case fact. *)
Ltac idm_fin HS HJ Em HK pc K1 K2 G1 G2 HTW :=
  pmkst HS;
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx sg (transportb_text + pc) rgx mm mdx) Qx) end;
  rewrite Em in HJ |- *;
  apply HK;
  [ exact HJ
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn; unfold IDM_WR in Hn;
    rewrite (K2 a Ha ltac:(intros X; apply Hn; right; exact X));
    apply K1; [lia | intros X; apply Hn; left; exact X]
  | let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; apply G2; apply G1; exact Hp
  | idtac | idtac | exact HTW | idtac ].

(* ------------------------------------------------------------------ *)
(* Valuations                                                          *)
(* ------------------------------------------------------------------ *)

Definition idm_E0 (rg : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg rg []).

Lemma idm_E_reg : forall rg l n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (PI := PI_transportb) (Ereg rg l)) n = YK11.getr rg r.
Proof. intros rg l n r Hn. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma idm_agree : forall rg l, env_agree 32 (Ereg rg l) (Eimg (PI := PI_transportb) (Ereg rg l)).
Proof. intros rg l. split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

Lemma idm_entry0 : forall (W : world segs) rg mem pc,
  st_ok_pi segs VAL (idm_E0 rg) (idm_ss0 pc)
    (restrict (w_H W) (@YK11.mkst fx rg (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W rg mem pc. rewrite restrict_mkst_fx. unfold idm_ss0, idm_E0.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb);
    [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]].
Qed.

(* sp + c, from a state whose sp register is the atom 2. *)
Lemma idm_den_sp : forall rg l sp c, YK11.getr rg (Z_to_bv 5 2) = Z_to_bv 64 sp -> 0 <= sp < 2 ^ 64 ->
  sv_denot (Eimg (PI := PI_transportb) (Ereg rg l)) (SOff 2 c) = Z_to_bv 64 (sp + c).
Proof.
  intros rg l sp c H2 Hsp. cbn [sv_denot]. rewrite (idm_E_reg rg l 2 (Z_to_bv 5 2) eq_refl), H2.
  rewrite unsigned_lit_small by exact Hsp. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The running kept fact                                               *)
(* ------------------------------------------------------------------ *)

(* A step of the walk that changes only bytes of io_send's stack window or bytes of G in its written range keeps the
   running kept fact. *)
Lemma idm_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi
    (E Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B G ->
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (slo <= a < shi) \/ (inG G a /\ E a)) ->
  YM05.alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transportb_segs_low G a HGX Ha)).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia |].
    intros HZa. destruct (HZ a HZa) as [Hs | [Hg _]]; [exact (Hw Hs) | pose proof (GLOW a Hg); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [Hg _]]; [lia | exact (HnG Hg)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < YM05.alloc_ceiling).
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
Lemma idm_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs frame
    ly2 S2 (W2 : world segs) mem2 md2 mem3 md3 (Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B lyc Sc W memc mdc ->
  YM05.alloc_ceiling <= spZ regs - IOSEND_STK -> spZ regs <= 2 ^ 47 ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 ->
  @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (spZ regs - IOSEND_STK <= a < spZ regs) \/
                     (inG TG.G_HARNESS_B a /\ iosend_wr (Z.of_nat (length frame)) a)) ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs frame ly2 S2 W2 mem2 md2 mem3 md3 Zs
    LAWS HGX HAR Hce Hhi (HJ & HF & HP & HM & HK) HJ3 Hkp Hgr HZ.
  split; [exact HJ3|]. split; [exact HF|]. split; [exact HP|]. split; [exact HM|].
  exact (idm_kept_step _ _ _ _ _ mdc W2 mem2 mem3 _ _ _ Zs LAWS HGX HAR HK Hkp Hgr HZ Hce Hhi).
Qed.

(* ------------------------------------------------------------------ *)
(* The leaf call of check_latest_frame                                 *)
(* ------------------------------------------------------------------ *)

(* What a leaf call returns (DgnTransportBLeafb.v decode_leafb_journal's facts with RES = None, WR = [] and the
   leaf's X Bx = Bx). *)
Definition idm_lr (regsT : bvmap 5 word) (W2 : world segs) (memT : word -> option byte) (Bx : list byte)
    (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  aregs_preserved regsT regs2 /\ (forall r, None = Some r -> YK11.getr regs2 10 = w64 r) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> ~ LCK.in_wr [] a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W2) memT a) /\
  (forall a, apresent (w_H W2) memT a -> apresent (w_H W2) mem2 a) /\ Bx = Bx.

(* The stack window of a call from io_send's frame: the struct at sp + 8 lies in the caller's journal window, above
   the callee's ESTACK window. *)
Definition idm_call_win (STK sp0 sp : Z) : Prop :=
  sp mod 16 = 0 /\ sp0 - STK <= sp - ESTACK /\ sp + 88 <= sp0.

(* check_latest_frame at 0x8478c (call at 0x83228), a0 = sp + 8, a1 = cmds (sign-extended from 32 bits). It reads
   f.send, f.ncmds and f.body_len of the struct at sp + 8. *)
Lemma idm_call_clf : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) memT mdT k
    (regsT : bvmap 5 word) (sp p cmds : Z) (fr Bx : list byte),
  transport_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLF.transport_check_latest_frame_cg) fx') ->
  @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 memT mdT k ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 sp -> YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 (sp + 8) ->
  YK11.getr regsT (Z_to_bv 5 11) = Z_to_bv 64 (bv_swrap 32 cmds) -> 0 <= cmds < 2 ^ 32 ->
  YK0s.ret_ok (YK11.getr regsT (Z_to_bv 5 1)) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  idm_call_win STK sp0 sp ->
  trans_sframe_at W2 memT (sp + 8) p (TC.rf fr) ->
  tw_at TMAP_B (aview segs (w_H W2) memT) Bx -> TC.check_latest_frame_m Bx fr cmds = Some (Bx, tt) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LLFc.CHECK_LATEST_FRAME) memT (YK11.seg_rom segs)) mdT)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsT (Z_to_bv 5 1)) mem3 (YK11.seg_rom segs)) md3 /\
       @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
         ly2 S2 W2 mem3 md3 k /\
       idm_lr regsT W2 memT Bx regs3 mem3 md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k regsT sp p cmds fr Bx HCELLS LAWS LEAF HJ
    R2 R10 R11 Hcm Rra R3 R4 (Hal & Hlo & Hhi) HSF HTW HM.
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (SPu : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp) by (rewrite R2; apply unsigned_lit_small; lia).
  destruct HSF as (Hfp0 & Hfp8 & SB & HG & HLSB & _ & _ & _ & _ & _ & _ & _ & Fsend & _ & _ & Fncm & _ & Fblen & _).
  apply (gx_call_leaf segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k _
    (YK11.getr regsT (Z_to_bv 5 1)) (idm_lr regsT W2 memT Bx) HJ).
  intros memS HJS.
  pose proof HJS as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  unfold idm_lr.
  apply (decode_leafb_journal B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0 own ly2 S2 mdT k (sp - sp0)
    LLFc.CHECK_LATEST_FRAME None [] (fun _ => Bx = Bx) HJS).
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
    unfold transport_leaf_at, LLF.transport_check_latest_frame_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT mdT (sp - ESTACK) Bx Bx (sp + 8) fr cmds HPRE).
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
      rewrite (idm_shadow_one (sp + 8) o n) in Hr by first [exact Hfp8 | lia]. exact Hr. }
    assert (HRJ : forall o n, 0 <= o -> o + n <= 80 ->
      ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W2) (sp + 8 + o) n)
      by (intros o n Ho Hon;
          apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k (sp + 8 + o) n HJS);
          lia).
    assert (HBY : forall k0 (n : nat) v, 0 <= k0 -> k0 + Z.of_nat n <= 80 -> TW.u_at SB k0 n = v ->
      LMem.bytes_at segs memT (sp + 8 + k0) (TW.put n v)).
    { intros k0 n v Hk Hkn Hv.
      apply (decode_leafb_bytes_garr8 W2 memT (sp + 8 + k0) (TW.put n v)); [| lia | rewrite TWL.length_put; lia].
      exact (idm_field _ (sp + 8) SB k0 n v HG Hk ltac:(rewrite HLSB; exact Hkn) Hv). }
    apply LF; clear LF.
    + exact R10.
    + exact R11.
    + exact Hcm.
    + lia.
    + exact Hfp8.
    + exact (HBY 32 4%nat _ ltac:(lia) ltac:(cbn; lia) Fsend).
    + exact (HBY 41 1%nat _ ltac:(lia) ltac:(cbn; lia) Fncm).
    + exact (HBY 56 8%nat _ ltac:(lia) ltac:(cbn; lia) Fblen).
    + exact (idm_tw_csw W2 memT Bx HTW).
    + exact HM.
    + rewrite SPu. apply (decode_leafb_stk_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - ESTACK) sp HJS); lia.
    + rewrite SPu. unfold LLFc.CHECK_LATEST_FRAME_FRAME. lia.
    + unfold AKA.off_stk. rewrite SPu.
      unfold LLFc.CHECK_LATEST_FRAME_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
    + exact (decode_leafb_asan_cells B HCELLS ly2 S2 W2 memT mdT HAR).
    + rewrite SPu. apply (@decode_leafb_app_stack rc). unfold LLFc.CHECK_LATEST_FRAME_FRAME. lia.
    + rewrite SPu. apply (@decode_leafb_app_stack rc). lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLFc.CHECK_LATEST_FRAME_FRAME, ACells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLFc.CHECK_LATEST_FRAME_FRAME, ACells.CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 56 8 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 41 1 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 32 4 ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite SPu. apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - LLFc.CHECK_LATEST_FRAME_FRAME) LLFc.CHECK_LATEST_FRAME_FRAME HJS);
        unfold LLFc.CHECK_LATEST_FRAME_FRAME; lia.
    + exact (proj1 (decode_leafb_rng_cells W2)).
    + exact (proj2 (decode_leafb_rng_cells W2)).
    + exact (HRS 56 8 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + exact (HRJ 56 8 ltac:(lia) ltac:(lia)).
    + apply idm_rng_hull; unfold LLFc.CHECK_LATEST_FRAME_MAXBODY, TB_g_cfg, TW.A_Cfg_max_body, TW.OFF_g_cfg,
        TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    + exact (HRS 41 1 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + exact (HRJ 41 1 ltac:(lia) ltac:(lia)).
    + apply idm_rng_hull; unfold LLFc.CHECK_LATEST_FRAME_MAXCMDS, TB_g_cfg, TW.A_Cfg_max_cmds, TW.OFF_g_cfg,
        TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    + apply idm_rng_hull; unfold TB_g_raw, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    + exact (HRS 32 4 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + apply idm_rng_hull; unfold LLFc.CHECK_LATEST_FRAME_HOST, TB_M, TW.A_M_host_counter, TW.OFF_M,
        TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    + exact (HRJ 32 4 ltac:(lia) ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* run C and the call: IOS_CMDS to the return 0x8322c                  *)
(* ------------------------------------------------------------------ *)

(* 0x83220: a0 = sp + 8; 0x83224: a1 = s2 (cmds); 0x83228: the call of check_latest_frame; it returns to 0x8322c. *)
Lemma idm_callC : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem3 md3 k
    (regs4 : bvmap 5 word) (sp p cmds : Z) (frame Bx : list byte) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 k ->
  YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 sp -> YK11.getr regs4 (Z_to_bv 5 3) = w64 (as_gp B) ->
  YK11.getr regs4 (Z_to_bv 5 4) = w64 (as_tp B) ->
  YK11.getr regs4 (Z_to_bv 5 18) = Z_to_bv 64 (bv_swrap 32 cmds) -> 0 <= cmds < 2 ^ 32 ->
  idm_call_win STK sp0 sp -> 2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 ->
  trans_sframe_at W2 mem3 (sp + 8) p (TC.rf frame) ->
  tw_at TMAP_B (aview segs (w_H W2) mem3) Bx -> TC.check_latest_frame_m Bx frame cmds = Some (Bx, tt) ->
  (forall mem5 md5 (regs5 : bvmap 5 word),
     @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem5 md5 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
        aview segs (w_H W2) mem5 a = aview segs (w_H W2) mem3 a) ->
     (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem5 a) ->
     (forall r, In r IDM_KEEPC -> YK11.getr regs5 r = YK11.getr regs4 r) ->
     SRr segs W2 (@cfg_at fx segs (transportb_text + IDM_CLF_RET) regs5 mem5 md5) Q) ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs4 mem3 md3) Q.
Proof.
  intros STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 mem3 md3 k regs4 sp p cmds frame Bx Q
    HL HJ R2 R3 R4 R18 Hcm HWIN Hs1 Hs2 HSF HTW HM HK.
  pose proof HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRF & HCSFc & HAF & HLC & HCIR & HSW
    & HIN2 & HTO & HLF & HKD & HCLS & HLD & HAI1).
  pose proof HWIN as (Hal & Hlo & Hhi).
  pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
    TG.G_HARNESS_B HGX 0 []) as RUN.
  pose proof (idm_entry0 W2 regs4 mem3 IOS_CMDS) as HS.
  assert (HEI : img_env VAL A_LIM (idm_E0 regs4)) by (unfold idm_E0; apply Eimg_env).
  assert (SHOK : sh_ok segs IDM_Bx (@nil shent) (idm_E0 regs4) (mrestrict (w_H W2) mem3)) by constructor.
  unfold cfg_at.
  change (SRr segs W2 (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + IOS_CMDS)) mem3 (YK11.seg_rom segs)) md3) Q).
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { apply awr_ok_x_nil. }
  set (md1 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md1. clear mat.
  rename ms into ms1.
  assert (K1 : forall x, ms_mem ms1 x = mem3 x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
  clear HF HFr HG.
  pose proof (aregs_preserved_of_st_ok segs (w_H W2) (idm_E0 regs4) _ ms1 regs4 [] HS (idm_agree regs4 [])
    ltac:(vm_compute; reflexivity)) as P1.
  idm_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + IDM_CLF_RET)) Q1 ltac:(apply codeptr_val; assumption).
  idm_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (sp + 8)) Q10 ltac:(unfold idm_E0; apply idm_den_sp; [exact R2 | lia]).
  idm_reg HS (Z_to_bv 5 11) (Z_to_bv 64 (bv_swrap 32 cmds)) Q11
    ltac:(unfold idm_E0; cbn [sv_denot]; rewrite (idm_E_reg regs4 [] 18 (Z_to_bv 5 18) eq_refl), R18, Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  assert (Q2 : YK11.getr (ms_regs ms1) (Z_to_bv 5 2) = Z_to_bv 64 sp)
    by (rewrite (P1 2 ltac:(unfold acallee_saved; lia)); exact R2).
  assert (Q3 : YK11.getr (ms_regs ms1) (Z_to_bv 5 3) = w64 (as_gp B))
    by (rewrite (P1 3 ltac:(unfold acallee_saved; lia)); exact R3).
  assert (Q4 : YK11.getr (ms_regs ms1) (Z_to_bv 5 4) = w64 (as_tp B))
    by (rewrite (P1 4 ltac:(unfold acallee_saved; lia)); exact R4).
  assert (Qra : YK0s.ret_ok (YK11.getr (ms_regs ms1) (Z_to_bv 5 1))).
  { rewrite Q1. unfold IDM_CLF_RET, IOS_AT, AF_io_send.
    apply (@ret_ok_codeptr_v rc transportb_listing PI_transportb); [lia | reflexivity]. }
  assert (HSF1 : trans_sframe_at W2 (ms_mem ms1) (sp + 8) p (TC.rf frame))
    by (apply (idm_sframe_kept W2 mem3 (ms_mem ms1) (sp + 8) p (TC.rf frame));
        [intros a _; apply idm_aview_ext; exact K1 | exact HSF]).
  assert (HTW1 : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms1)) Bx)
    by (apply (tw_kept TMAP_B _ _ Bx HTW); intros x _; apply idm_aview_ext; exact K1).
  assert (KC : forall r, In r IDM_KEEPC -> YK11.getr (ms_regs ms1) r = YK11.getr regs4 r).
  { eapply (regs_kept_of_st_ok segs _ _ _ _ _ IDM_KEEPC HS); [exact (idm_agree regs4 []) | vm_compute; reflexivity]. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (YK11.mkst rgx (Z_to_bv 64 LLFc.CHECK_LATEST_FRAME) mm rom) mdx) Qx) end.
  eapply SRr_bind.
  { exact (idm_call_clf STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 (ms_mem ms1) _ k (ms_regs ms1) sp p cmds
      frame Bx HCELLS LAWS HLF HJ Q2 Q10 Q11 Hcm Qra Q3 Q4 HWIN HSF1 HTW1 HM). }
  intros W3 c3 _ (-> & rg5 & mem5 & md5 & -> & HJ5 & HP5 & _ & HK5 & HG5 & _).
  rewrite Q1.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) _ =>
    change (SRr segs W2 (@cfg_at fx segs (transportb_text + IDM_CLF_RET) rgx mm mdx) Q) end.
  assert (SP1 : spZ (ms_regs ms1) = sp)
    by (change (spZ (ms_regs ms1)) with (bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2))); rewrite Q2;
        apply unsigned_lit_small; lia).
  apply HK.
  - exact HJ5.
  - intros a Ha Hn. rewrite (HK5 a Ha ltac:(rewrite SP1; exact Hn) ltac:(intros X; inversion X)).
    apply idm_aview_ext. exact K1.
  - intros a Hp. apply HG5. apply (idm_present_ext _ _ _ a K1). exact Hp.
  - intros r Hr. rewrite (idm_ap _ rg5 r HP5 ltac:(unfold IDM_KEEPC in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [idm_cs |]); destruct Hr)). exact (KC r Hr).
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the return 0x8322c                            *)
(* ------------------------------------------------------------------ *)

(* run D's valuation: the registers there, f.send as atom 32 and g_raw as atom 33. *)
Definition idm_ED (regs5 : bvmap 5 word) (send graw : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs5 [Z_to_bv 64 send; Z_to_bv 64 graw]).

Lemma idm_vals : VAL (A_OBJ 8) = TB_M /\ VAL (A_HI 59) = TB_g_last_counter + 1160.
Proof. split; vm_compute; reflexivity. Qed.

Lemma idm_entryD : forall (W2 : world segs) mem5 (regs5 : bvmap 5 word) (sp send graw : Z),
  YK11.getr regs5 2 = w64 sp -> YK11.getr regs5 20 = w64 SHADOW_OFF -> YK11.getr regs5 22 = w64 IOS_S6 ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= send < 2 ^ 32 -> 0 <= graw < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) (sp + 40) 4 send ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) TB_g_raw 4 graw ->
  st_ok_pi segs VAL (idm_ED regs5 send graw) idm_ssD
    (restrict (w_H W2) (@YK11.mkst fx regs5 (Z_to_bv 64 (BASE + IDM_CLF_RET)) mem5 (YK11.seg_rom segs)))
  /\ sh_ok segs IDM_Bx IDM_SH (idm_ED regs5 send graw) (mrestrict (w_H W2) mem5).
Proof.
intros W2 mem5 regs5 sp send graw H2 H20 H22 Hs1 Hs2 Hs16 Hsd Hgr V40 V0.
destruct idm_vals as (VM & V59).
set (E := idm_ED regs5 send graw).
assert (E2 : ew E 2 = YK11.getr regs5 2) by (unfold E, idm_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = YK11.getr regs5 20) by (unfold E, idm_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E22 : ew E 22 = YK11.getr regs5 22) by (unfold E, idm_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2, H2; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20, H20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = IOS_S6)
  by (rewrite E22, H22; unfold w64; apply unsigned_lit_small; unfold IOS_S6, TB_g_raw; lia).
assert (E32 : ew E 32 = Z_to_bv 64 send)
  by (unfold E, idm_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 graw)
  by (unfold E, idm_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
assert (UM : bv_unsigned (ew E (A_OBJ 8)) = TB_M).
{ unfold E, idm_ED. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite VM.
  apply unsigned_lit_small. unfold TB_M; lia. }
assert (U59 : bv_unsigned (ew E (A_HI 59)) = TB_g_last_counter + 1160).
{ unfold E, idm_ED. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite V59.
  apply unsigned_lit_small. unfold TB_g_last_counter; lia. }
split; [|unfold sh_ok, IDM_SH; constructor].
rewrite restrict_mkst_fx. unfold idm_ssD, idm_regionsD.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold idm_frameD, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ sp 40 4 (SOff 32 0) send);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V40].
  + unfold idm_rawD, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [unfold IOS_S6, TB_g_raw; lia|]. split; [unfold IOS_S6, TB_g_raw; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ IOS_S6 (-1056) 4 (SOff 33 0) graw);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia
      | unfold IOS_S6, TB_g_raw; lia
      | replace (IOS_S6 + -1056) with TB_g_raw by (unfold IOS_S6; lia); exact V0].
  + unfold idm_hostD, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UM. split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
    split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B _ G_HARNESS_B_rw).
    apply (ios_inG_row _ _ _ _ TMAP_B_M). unfold TW.SZ_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold idm_frameD, idm_rawD, idm_hostD, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, UM, U22.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | unfold IOS_S6, TB_g_raw, TB_M, TB_g_last_counter; lia].
- unfold idm_factsD, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U20, U22, UM, U59.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I;
    first [lia | unfold SHADOW_OFF; lia | unfold IOS_S6, TB_g_raw; lia | unfold TB_M; lia
          | unfold TB_g_last_counter; lia | vm_compute; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* run D: the two stores into G and the last branch, 0x8322c .. 0x83250 *)
(* ------------------------------------------------------------------ *)

Lemma idm_runD : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem5 md5 k
    (regs5 : bvmap 5 word) (sp send graw kaz : Z) (Bx : list byte) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
    ly2 S2 W2 mem5 md5 k ->
  YK11.getr regs5 2 = w64 sp -> YK11.getr regs5 20 = w64 SHADOW_OFF -> YK11.getr regs5 22 = w64 IOS_S6 ->
  YK11.getr regs5 21 = w64 kaz -> 0 <= kaz <= 1 ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= send < 2 ^ 32 -> 0 <= graw < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) (sp + 40) 4 send ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) TB_g_raw 4 graw ->
  tw_at TMAP_B (aview segs (w_H W2) mem5) Bx -> TW.g_raw Bx = bv_swrap 32 graw ->
  (forall mem7 md7 (regs7 : bvmap 5 word) (pc : Z),
     @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem7 md7 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ IDM_WR a ->
        aview segs (w_H W2) mem7 a = aview segs (w_H W2) mem5 a) ->
     (forall a, apresent (w_H W2) mem5 a -> apresent (w_H W2) mem7 a) ->
     (forall r, In r IDM_KEEPD -> YK11.getr regs7 r = YK11.getr regs5 r) ->
     YK11.getr regs7 18 = w64 TB_M ->
     tw_at TMAP_B (aview segs (w_H W2) mem7)
       (TW.set_g_last_counter (TW.set_M_host_counter Bx send) send) ->
     (pc = IOS_KA /\ TC.truth (TW.g_raw Bx) = false /\ kaz = 1 \/
      pc = IOS_SENT /\ YK11.getr regs7 10 = w64 (TW.g_raw Bx) /\
        (TC.truth (TW.g_raw Bx) = false -> kaz = 0)) ->
     SRr segs W2 (@cfg_at fx segs (transportb_text + pc) regs7 mem7 md7) Q) ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IDM_CLF_RET) regs5 mem5 md5) Q.
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 mem5 md5 k regs5 sp send graw kaz Bx Q
  HL HJ R2 R20 R22 R21 Hkz Hs1 Hs2 Hs16 Hsd Hgr V40 V0 HTW HGR HK.
pose proof HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRF & HCSFc & HAF & HLC & HCIR & HSW
  & HIN2 & HTO & HLF & HKD & HCLS & HLD & HAI1).
destruct idm_vals as (VM & V59).
set (ED := idm_ED regs5 send graw) in *.
assert (E32 : ew ED 32 = Z_to_bv 64 send)
  by (unfold ED, idm_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (E33 : ew ED 33 = Z_to_bv 64 graw)
  by (unfold ED, idm_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
assert (E21 : ew ED 21 = YK11.getr regs5 21) by (unfold ED, idm_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (UM : bv_unsigned (ew ED (A_OBJ 8)) = TB_M).
{ unfold ED, idm_ED. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite VM.
  apply unsigned_lit_small. unfold TB_M; lia. }
assert (U59 : bv_unsigned (ew ED (A_HI 59)) = TB_g_last_counter + 1160).
{ unfold ED, idm_ED. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite V59.
  apply unsigned_lit_small. unfold TB_g_last_counter; lia. }
assert (U2 : bv_unsigned (ew ED 2) = sp).
{ assert (E2 : ew ED 2 = YK11.getr regs5 2) by (unfold ED, idm_ED; apply ew_Eimg_Ereg_nat; reflexivity).
  rewrite E2, R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U22 : bv_unsigned (ew ED 22) = IOS_S6).
{ assert (E22 : ew ED 22 = YK11.getr regs5 22) by (unfold ED, idm_ED; apply ew_Eimg_Ereg_nat; reflexivity).
  rewrite E22, R22. unfold w64. apply unsigned_lit_small. unfold IOS_S6, TB_g_raw; lia. }
destruct (idm_entryD W2 mem5 regs5 sp send graw R2 R20 R22 Hs1 Hs2 Hs16 Hsd Hgr V40 V0) as [HS SHOK].
fold ED in HS, SHOK.
assert (UMn : bv_unsigned (ew ED 249%nat) = TB_M) by exact UM.
assert (U59n : bv_unsigned (ew ED 459%nat) = TB_g_last_counter + 1160) by exact U59.
assert (HEI : img_env VAL A_LIM ED) by (unfold ED, idm_ED; apply Eimg_env).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs5 (Z_to_bv 64 (BASE + IDM_CLF_RET)) mem5 (YK11.seg_rom segs)) md5)
    Qx) end.
(* 0x8322c .. 0x8323c: a1 = f.send, a0 = g_raw, s2 = M, the store at M + 84 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1fa0.
{ idm_awrD UMn U59n. }
set (md1 := with_vm_backing (m_vm_lazy md5) mat md5) in *. clearbody md1. clear mat.
rename ms into ms1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 84 <= a < TB_M + 88) ->
  aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem5 a).
{ apply (kept_of_frame _ _ _ _ _ (fun a => TB_M + 84 <= a < TB_M + 88) HFr).
  intros b wlo whi x Hin Hx. idm_win Hin Hx ltac:(rewrite ?U2, ?U22, ?UMn in Hx; unfold TB_M in *; lia). }
assert (G1 : forall a, apresent (w_H W2) mem5 a -> apresent (w_H W2) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the word the first store left at M + 84 *)
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let r0 := eval vm_compute in (nth 2 (ss_mem ssx) idm_hostD) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh m) 2 r0 HS ltac:(vm_compute; reflexivity)) as RG1 end.
cbn [ms_mem restrict] in RG1.
assert (DS : sv_denot ED (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (bv_swrap 32 send))
  by exact (idm_sext32_den ED 32 send E32 ltac:(lia)).
assert (DG : sv_denot ED (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 graw))
  by exact (idm_sext32_den ED 33 graw E33 ltac:(lia)).
pose proof (idm_region_rd4 ED (w_H W2) (ms_mem ms1) 249%nat 84 88 84 88 84 (SExt true 32 (SOff 32 0))
  (bv_swrap 32 send) TB_M RG1 UMn DS) as V1.
(* the world after the first store *)
assert (HTW1 : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms1)) (TW.set_M_host_counter Bx send)).
{ change (TW.set_M_host_counter Bx send) with (TW.upd Bx (TW.OFF_M + 84) (TW.put 4 send)).
  apply (tw_write TMAP_B (aview segs (w_H W2) mem5) _ Bx TW.OFF_M TB_M TW.SZ_M 84 4 send
    TMAP_B_ok HTW TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; cbn; lia)).
  - intros j Hj. rewrite (V1 j Hj). f_equal. apply (idm_le_byte_swrap 32 4 j send). reflexivity.
  - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply K1; [lia | cbn in Hn; lia]. }
(* the second store's region, added now so the first store's world step stands *)
assert (RGL : region_ok segs ED (mrestrict (w_H W2) (ms_mem ms1)) idm_lastD).
{ unfold idm_lastD, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U59. split; [unfold TB_g_last_counter; lia|]. split; [unfold TB_g_last_counter; lia|].
  split; [|constructor].
  intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B _ G_HARNESS_B_rw).
  apply (ios_inG_row _ _ _ _ TMAP_B_g_last_counter). unfold TW.SZ_g_last_counter. lia. }
assert (DJL : all_disjoint ED idm_lastD [idm_frameD; idm_rawD]).
{ unfold idm_lastD, idm_frameD, idm_rawD. cbn [all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U22, U59.
  repeat split; try exact I; unfold TB_M, IOS_S6, TB_g_raw, TB_g_last_counter; lia. }
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let rs := eval vm_compute in (firstn 2 (ss_mem ssx)) in
  pose proof (st_ok_pi_submem Ex ssx (restrict Hh m) rs HS
    ltac:(vm_compute; apply submem_keep; [apply subregion_refl|];
          apply submem_keep; [apply subregion_refl|]; constructor)
    ltac:(vm_compute; reflexivity)) as HSd end.
lazymatch type of HSd with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  pose proof (st_ok_pi_add_region Ex ssx (restrict Hh m) idm_lastD HSd ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_mem restrict]; exact RGL) ltac:(exact DJL)) as HSL end.
clear HS HSd RG1. idm_rw HSL.
(* 0x83240 .. 0x83250: a2 = (g_raw <u 1) & s5, the store at g_last_counter, then the branch *)
paj_run_to_tok RUNTO HSL HJ SHOK YC4b.Bspan 0x1fb0.
{ idm_awrD UMn U59n. }
set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
rename ms into ms2.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_last_counter <= a < TB_g_last_counter + 4) ->
  aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) (ms_mem ms1) a).
{ apply (kept_of_frame _ _ _ _ _ (fun a => TB_g_last_counter <= a < TB_g_last_counter + 4) HFr).
  intros b wlo whi x Hin Hx.
  idm_win Hin Hx ltac:(rewrite ?U2, ?U22, ?UMn, ?U59n in Hx; unfold TB_M, TB_g_last_counter in *; lia). }
assert (G2 : forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
lazymatch type of HSL with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) idm_lastD) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh m) 0 r0 HSL ltac:(vm_compute; reflexivity)) as RG2 end.
cbn [ms_mem restrict] in RG2.
pose proof (idm_region_rd4 ED (w_H W2) (ms_mem ms2) 459%nat (-1160) (-1156) (-1160) (-1156) (-1160)
  (SExt true 32 (SOff 32 0)) (bv_swrap 32 send) (TB_g_last_counter + 1160) RG2 U59n DS) as V2.
assert (HTW2 : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms2))
  (TW.set_g_last_counter (TW.set_M_host_counter Bx send) send)).
{ change (TW.set_g_last_counter (TW.set_M_host_counter Bx send) send)
    with (TW.upd (TW.set_M_host_counter Bx send) (TW.OFF_g_last_counter + 0) (TW.put 4 send)).
  apply (tw_write TMAP_B (aview segs (w_H W2) (ms_mem ms1)) _ (TW.set_M_host_counter Bx send)
    TW.OFF_g_last_counter TB_g_last_counter TW.SZ_g_last_counter 0 4 send
    TMAP_B_ok HTW1 TMAP_B_g_last_counter ltac:(lia) ltac:(unfold TW.SZ_g_last_counter; cbn; lia)).
  - intros j Hj.
    replace (TB_g_last_counter + 0 + Z.of_nat j) with (TB_g_last_counter + 1160 + -1160 + Z.of_nat j) by lia.
    rewrite (V2 j Hj). f_equal. apply (idm_le_byte_swrap 32 4 j send). reflexivity.
  - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply K2; [lia | cbn in Hn; lia]. }
assert (Hgs : - 2 ^ 31 <= TW.g_raw Bx < 2 ^ 31)
  by (pose proof (TWL.s32_range Bx TW.OFF_g_raw) as Hr; unfold TW.g_raw; lia).
(* both regions of G are done with; keep only the two read-only ones, so the exits' runs touch no memory *)
lazymatch type of HSL with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let rs := eval vm_compute in (skipn 1 (ss_mem ssx)) in
  pose proof (st_ok_pi_submem Ex ssx (restrict Hh m) rs HSL
    ltac:(vm_compute; apply submem_drop; apply submem_refl)
    ltac:(vm_compute; reflexivity)) as HSr end.
clear HSL RG2. idm_rw HSr.
psrr_branch_tok RUN BR HSr SHOK YC4b.Bspan.
all: rewrite (idm_cond_den ED 33 21 (TW.g_raw Bx) kaz ltac:(rewrite HGR; exact DG) Hgs
  ltac:(rewrite E21, R21; reflexivity) Hkz) in Hc.
all: cbn [branch_taken sv_denot] in Hc.
all: rewrite (idm_eqb (if (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool then 1 else 0) 0
  ltac:(destruct (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool; lia) ltac:(lia)) in Hc.
- (* the condition is 0: to 0x8328c, the check_latest_sent case *)
  apply Z.eqb_eq in Hc.
  destruct (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool eqn:Hcc; [discriminate Hc|].
  paj_run_to_tok RUNTO HSr HJ SHOK YC4b.Bspan 0x1fec.
  { idm_awrA. }
  rename ms into ms3. assert (Em3 : ms_mem ms3 = ms_mem ms2).
  { eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG.
  idm_fin HSr HJ Em3 HK IOS_SENT K1 K2 G1 G2 HTW2.
  + exact (regs_kept_of_st_ok_pi _ _ _ _ _ IDM_KEEPD HSr ltac:(unfold ED, idm_ED; apply idm_agree)
      ltac:(vm_compute; reflexivity)).
  + idm_rv HSr. cbn [sv_denot]. rewrite UMn, Z.add_0_r. reflexivity.
  + right. split; [reflexivity|]. split.
    * idm_rv HSr. rewrite HGR. exact DG.
    * intros Ht. rewrite Ht in Hcc. cbn [negb] in Hcc.
      destruct (Z.eqb_spec kaz 1) as [Hk1|Hk0]; [cbn [andb] in Hcc; discriminate Hcc | lia].
- (* the condition is 1: on to 0x83254, the keepalive case *)
  apply Z.eqb_neq in Hc.
  destruct (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool eqn:Hcc; [|exfalso; apply Hc; reflexivity].
  apply andb_prop in Hcc as (Hc1 & Hc2). apply negb_true_iff in Hc1. apply Z.eqb_eq in Hc2.
  paj_run_to_tok RUNTO HSr HJ SHOK YC4b.Bspan 0x1fb4.
  { idm_awrA. }
  rename ms into ms3. assert (Em3 : ms_mem ms3 = ms_mem ms2).
  { eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG.
  idm_fin HSr HJ Em3 HK IOS_KA K1 K2 G1 G2 HTW2.
  + exact (regs_kept_of_st_ok_pi _ _ _ _ _ IDM_KEEPD HSr ltac:(unfold ED, idm_ED; apply idm_agree)
      ltac:(vm_compute; reflexivity)).
  + idm_rv HSr. cbn [sv_denot]. rewrite UMn, Z.add_0_r. reflexivity.
  + left. split; [reflexivity | split; [exact Hc1 | exact Hc2]].
Qed.

(* ------------------------------------------------------------------ *)
(* The segment: IOS_CMDS .. IOS_KA / IOS_SENT                          *)
(* ------------------------------------------------------------------ *)

Lemma iod_mid : @iod_mid_stmt fx rc B MT.
Proof.
unfold iod_mid_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw cmds ly2 S2 W2 mem2 md2 regs2 Q
  HL HFX HCSFm HAT R18c Hcm HCLF HK.
pose proof HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRF & HCSFc & HAF & HLC & HCIR & HSW
  & HIN2 & HTO & HLF & HKD & HCLS & HLD & HAI1).
pose proof HFX as (HJ & _ & _ & Hgp & Htp & _ & _ & Hsp16 & Hlo & Hhi & _).
destruct HAT as (HCSF & R21 & R22).
pose proof HCSF as (HCUR & HSAV & HREG & HS811 & HSFa & HSFsrc & HGARR & HSRC & HTW).
pose proof HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof HCUR as (HJ2 & Hfrs & Hperm & Hmo & HKEPT).
pose proof HJ2 as (HSTK3 & _ & (memS3 & HJ3i & _) & _).
rewrite !Z.add_0_r in HJ3i.
pose proof HJ3i as (HAR3 & _).
clear HJ3i memS3.
pose proof HJ as (HSTK & _ & (memS0 & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (FS : IOSEND_STK = 8512) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
set (sp := spZ regs - IOSEND_FRAME) in *.
assert (Esp : sp = spZ regs - IOSEND_FRAME) by reflexivity.
assert (Hsp16' : sp mod 16 = 0) by (rewrite Esp, Zminus_mod, Hsp16, FF; reflexivity).
set (graw := TW.u_at (ios_B0 Bw) TW.OFF_g_raw 4) in *.
assert (HGR : TW.g_raw (ios_B0 Bw) = bv_swrap 32 graw) by reflexivity.
pose proof (TWL.u_at_range (ios_B0 Bw) TW.OFF_g_raw 4) as Rgr.
change (8 * Z.of_nat 4) with 32 in Rgr.
assert (HWIN : idm_call_win STK sp0 sp) by (split; [exact Hsp16' | split; lia]).
assert (Hkz : 0 <= ios_kaz frame <= 1) by (unfold ios_kaz; destruct (ios_ka frame); lia).
(* IOS_CMDS .. 0x8322c: a0 = sp + 8, a1 = cmds, the call of check_latest_frame *)
apply (idm_callC STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 0) regs2 sp p cmds frame
  (ios_B0 Bw) Q HL HJ2 R2 ltac:(transitivity (YK11.getr regs 3); [exact R3 | exact Hgp])
  ltac:(transitivity (YK11.getr regs 4); [exact R4 | exact Htp]) R18c Hcm
  HWIN ltac:(lia) ltac:(lia) HSFa HTW HCLF).
intros mem5 md5 regs5 HJ5 HK5 HG5 HKC5.
(* the struct, the world and the two values run D reads, at the memory the leaf left *)
assert (HSF5 : trans_sframe_at W2 mem5 (sp + 8) p (TC.rf frame)).
{ apply (idm_sframe_kept W2 mem2 mem5 (sp + 8) p (TC.rf frame)); [|exact HSFa].
  intros a Ha. apply HK5; lia. }
assert (HTW5 : tw_at TMAP_B (aview segs (w_H W2) mem5) (ios_B0 Bw)).
{ apply (tw_kept TMAP_B _ _ _ HTW). intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply HK5; lia. }
pose proof HSF5 as (Hfp0' & Hfp8' & SB' & HGsb' & HLSB' & G0 & G8' & G16 & G24' & G26 & G28 & G30 & G32 & G36 &
  G40 & G41 & G48 & G56 & G64 & G72).
pose proof (TWL.u_at_range SB' 32 4) as Rsd. change (8 * Z.of_nat 4) with 32 in Rsd. rewrite G32 in Rsd.
assert (V40 : YI04.val_mem segs (mrestrict (w_H W2) mem5) (sp + 40) 4 (DSpec.sf_send (TC.rf frame))).
{ replace (sp + 40) with (sp + 8 + 32) by lia. rewrite <- G32.
  apply (idm_val_at (mrestrict (w_H W2) mem5) (sp + 8) SB' 32 4 HGsb'); [lia | rewrite HLSB'; cbn; lia]. }
assert (V0 : YI04.val_mem segs (mrestrict (w_H W2) mem5) TB_g_raw 4 graw).
{ pose proof (tw_read_val segs (mrestrict (w_H W2) mem5) TMAP_B (ios_B0 Bw) TW.OFF_g_raw TB_g_raw TW.SZ_g_raw
    0 4 TMAP_B_ok HTW5 TMAP_B_g_raw ltac:(lia) ltac:(unfold TW.SZ_g_raw; cbn; lia)) as Hv.
  rewrite Z.add_0_r in Hv. unfold graw. rewrite Z.add_0_r in Hv. exact Hv. }
clear G0 G8' G16 G24' G26 G28 G30 G36 G40 G41 G48 G56 G64 G72.
(* 0x8322c .. 0x83250: the two stores and the last branch *)
apply (idm_runD STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem5 md5 (k + 0) regs5 sp
  (DSpec.sf_send (TC.rf frame)) graw (ios_kaz frame) (ios_B0 Bw) Q HL HJ5
  ltac:(transitivity (YK11.getr regs2 2); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R2])
  ltac:(transitivity (YK11.getr regs2 20); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R20])
  ltac:(transitivity (YK11.getr regs2 22); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R22])
  ltac:(transitivity (YK11.getr regs2 21); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R21])
  Hkz ltac:(lia) ltac:(lia) Hsp16' Rsd Rgr V40 V0 HTW5 HGR).
intros mem7 md7 regs7 pc HJ7 HK7 HG7 HKD7 Q18' HTW7 Hcase.
assert (HK7all : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - ESTACK <= a < sp) \/ IDM_WR a) ->
  aview segs (w_H W2) mem7 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (HK7 a Ha ltac:(intros X; apply Hn; right; exact X)).
  apply HK5; [exact Ha | intros X; apply Hn; left; exact X]. }
assert (HG7all : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem7 a)
  by (intros a Hp'; apply HG7; apply HG5; exact Hp').
(* the running facts at the exit: what changed is the leaf's window below sp and the two words of G *)
assert (HCUR7 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem7 md7).
{ apply (idm_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs frame ly2 S2 W2 mem2 md2 mem7 md7
    (fun a => (sp - ESTACK <= a < sp) \/ IDM_WR a) LAWS HGX HAR0 ltac:(lia) ltac:(lia) HCUR HJ7 HK7all HG7all).
  intros a [Hw | Hw]; [left; lia|]. right. unfold IDM_WR in Hw. destruct Hw as [Hw|Hw].
  - split; [apply (ios_inG_row _ _ _ a TMAP_B_M); unfold TW.SZ_M; lia | apply (ios_wr_hostc _ a); lia].
  - split; [apply (ios_inG_row _ _ _ a TMAP_B_g_last_counter); unfold TW.SZ_g_last_counter; lia
           | apply (ios_wr_lastc _ a); lia]. }
(* io_send's own frame above sp: the nine saved words and the struct *)
assert (HSAV7 : ios_saved W2 mem7 regs).
{ apply (idm_saved_kept W2 mem2 mem7 regs); [|exact HSAV].
  intros a Ha. apply HK7all; [lia|]. intros [Hw | Hw]; [lia|].
  unfold IDM_WR in Hw. destruct Hw as [Hw|Hw]; unfold TB_M, TB_g_last_counter in Hw; lia. }
assert (HSF7 : trans_sframe_at W2 mem7 (sp + 8) p (TC.rf frame)).
{ apply (idm_sframe_kept W2 mem2 mem7 (sp + 8) p (TC.rf frame)); [|exact HSFa].
  intros a Ha. apply HK7all; [lia|]. intros [Hw | Hw]; [lia|].
  unfold IDM_WR in Hw. destruct Hw as [Hw|Hw]; unfold TB_M, TB_g_last_counter in Hw; lia. }
(* the frame's bytes: outside the leaf's window (decode_off_win) and apart from the two words (iosend_frame_at) *)
pose proof HFX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp0 & _ & Hsrc & Hoff & Hfat & _).
pose proof (ios_len60 (ios_B0 Bw) frame (ios_B0 Bw) HCSFm) as HL60.
assert (Hplen : 4096 <= p /\ p + Z.of_nat (length frame) <= 2 ^ 47).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p (Z.of_nat (length frame)) HAR0 Hsrc ltac:(lia))
    as [Hpl | Hpl]; lia. }
assert (HnWR : forall a, p <= a < p + Z.of_nat (length frame) -> ~ IDM_WR a).
{ intros a Ha HW. destruct Hfat as [Hout | (Hgs1 & Hgs2)].
  - apply (Hout a Ha). destruct HW as [HM'|HM'].
    + apply (ios_inG_row _ _ _ _ TMAP_B_M). unfold TW.SZ_M. lia.
    + apply (ios_inG_row _ _ _ _ TMAP_B_g_last_counter). unfold TW.SZ_g_last_counter. lia.
  - destruct HW as [HM'|HM']; unfold TB_M, TB_g_last_counter, TB_g_s, TW.SZ_g_s in *; lia. }
assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
  aview segs (w_H W2) mem7 a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply HK7all; [lia|].
  intros [Hw | Hw]; [unfold decode_off_win in Hoff; destruct Hoff as [Ho|Ho]; lia | exact (HnWR a Ha Hw)]. }
assert (HGARR7 : garr8 segs (mrestrict (w_H W2) mem7) p (map DSpec.bz frame)).
{ apply (idm_garr8_kept (w_H W2) mem2 mem7 p (map DSpec.bz frame)); [|exact HGARR].
  intros a Ha. rewrite length_map in Ha. exact (KF a Ha). }
(* the frame's placement at the exit: its bytes and the shadow of the caller's frames are kept *)
pose proof HJ7 as (HSTK7 & _ & (memS7 & HJ7i & _) & _).
rewrite !Z.add_0_r in HJ7i. pose proof HJ7i as (HAR7 & _). clear HJ7i memS7.
assert (HSRC7 : trans_src_ok B ly2 S2 W2 mem7 p (Z.of_nat (length frame))).
{ apply (trans_src_ok_kept B LAWS ly2 S2 W2 mem2 md2 ly2 S2 W2 mem7 md7 p (Z.of_nat (length frame))
    HAR3 HAR7 (Permutation_refl _) eq_refl (fun c q => eq_refl) eq_refl eq_refl KF); [| exact HSRC | lia].
  intros cid pos s Hin Hs'.
  destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR3 Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr ly2 cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr ly2 cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs'. cbn [fst snd] in Hs'.
  unfold ACells.shadow_addr, ACells.ASAN_K, YG0f.shadow_addr, SHADOW_OFF in *.
  change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
  assert (Hsub : frame_addr ly2 cid pos / 8 + fs_frame_bytes cid / 8
    <= (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8) by (Z.div_mod_to_equations; lia).
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  assert (Hs0 : 0 <= s < 2 ^ 64) by lia.
  assert (HsW : ~ (sp - ESTACK <= s < sp)) by lia.
  assert (HsG : ~ IDM_WR s) by (unfold IDM_WR, TB_M, TB_g_last_counter; lia).
  apply HK7all; [exact Hs0 | intros [Hw|Hw]; [exact (HsW Hw) | exact (HsG Hw)]]. }
assert (HTAIL : ios_tail_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem7 md7
  (ios_B5 Bw frame)).
{ split; [exact HCUR7|]. split; [exact HSAV7|]. split; [exact HSF7|]. split; [exact HGARR7|].
  split; [exact HSRC7|]. split; [exact Hoff|]. split; [exact Hfat | exact HTW7]. }
(* the two stores leave g_raw alone, and the keepalive flag as a boolean *)
assert (EGR : TW.g_raw (ios_B5 Bw frame) = TW.g_raw (ios_B0 Bw)).
{ assert (LB : Z.of_nat (length (ios_B0 Bw)) = TW.W_LEN).
  { rewrite (tw_len TMAP_B _ _ HTW). unfold TW.W_LEN. lia. }
  unfold ios_B5, TW.set_g_last_counter, TW.set_M_host_counter, TW.g_raw.
  rewrite TWL.s32_at_upd_out by
    (rewrite ?TWL.length_put, ?TWL.length_upd_put;
     unfold TW.OFF_g_last_counter, TW.OFF_g_raw, TW.A_M_host_counter, TW.OFF_M, TW.W_LEN in *; lia).
  rewrite TWL.s32_at_upd_out by
    (rewrite ?TWL.length_put;
     unfold TW.OFF_g_raw, TW.A_M_host_counter, TW.OFF_M, TW.W_LEN in *; lia).
  reflexivity. }
assert (Hcase' : pc = IOS_KA /\ TC.truth (TW.g_raw (ios_B5 Bw frame)) = false /\ ios_ka frame = true \/
    pc = IOS_SENT /\ YK11.getr regs7 10 = w64 (TW.g_raw (ios_B5 Bw frame)) /\
      (TC.truth (TW.g_raw (ios_B5 Bw frame)) = false -> ios_ka frame = false)).
{ rewrite EGR. destruct Hcase as [(E1 & E2 & E3) | (E1 & E2 & E3)].
  - left. split; [exact E1 | split; [exact E2|]].
    unfold ios_kaz in E3. destruct (ios_ka frame); [reflexivity | lia].
  - right. split; [exact E1 | split; [exact E2|]]. intros Ht. pose proof (E3 Ht) as Hz.
    unfold ios_kaz in Hz. destruct (ios_ka frame); [lia | reflexivity]. }
(* the registers the tail reads: io_send's own, kept by the call and by run D *)
assert (P2 : YK11.getr regs7 2 = w64 (spZ regs - IOSEND_FRAME)).
{ transitivity (YK11.getr regs5 2); [apply HKD7; unfold IDM_KEEPD; idm_kin|].
  transitivity (YK11.getr regs2 2); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R2]. }
assert (P3 : YK11.getr regs7 3 = YK11.getr regs 3).
{ transitivity (YK11.getr regs5 3); [apply HKD7; unfold IDM_KEEPD; idm_kin|].
  transitivity (YK11.getr regs2 3); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R3]. }
assert (P4 : YK11.getr regs7 4 = YK11.getr regs 4).
{ transitivity (YK11.getr regs5 4); [apply HKD7; unfold IDM_KEEPD; idm_kin|].
  transitivity (YK11.getr regs2 4); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R4]. }
assert (P8 : YK11.getr regs7 8 = w64 (Z.of_nat (length frame))).
{ transitivity (YK11.getr regs5 8); [apply HKD7; unfold IDM_KEEPD; idm_kin|].
  transitivity (YK11.getr regs2 8); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R8]. }
assert (P9 : YK11.getr regs7 9 = w64 p).
{ transitivity (YK11.getr regs5 9); [apply HKD7; unfold IDM_KEEPD; idm_kin|].
  transitivity (YK11.getr regs2 9); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R9]. }
assert (P19 : YK11.getr regs7 19 = w64 (TW.g_fail_next Bw)).
{ transitivity (YK11.getr regs5 19); [apply HKD7; unfold IDM_KEEPD; idm_kin|].
  transitivity (YK11.getr regs2 19); [apply HKC5; unfold IDM_KEEPC; idm_kin | exact R19]. }
assert (P24 : forall rr, 24 <= rr <= 27 -> YK11.getr regs7 (Z_to_bv 5 rr) = YK11.getr regs (Z_to_bv 5 rr)).
{ intros rr Hrr. rewrite <- (HS811 rr Hrr).
  assert (Er : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  destruct Er as [-> | [-> | [-> | ->]]];
    (etransitivity; [apply HKD7; unfold IDM_KEEPD; idm_kin | apply HKC5; unfold IDM_KEEPC; idm_kin]). }
exact (HK mem7 md7 regs7 pc HTAIL P2 P3 P4 P8 P9 P19 P24 Q18' Hcase').
Qed.

End dmid.
