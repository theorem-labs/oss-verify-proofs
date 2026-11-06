(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths, module names and numbers changed; 1240 of its 1319 lines of code are new or changed and 686 lines of the source are left out. *)
(* io_send_seg_data: the DATA arm's head of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f,
   entry 0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt), from the cut IOS_DATA (0x83148) to IOS_CMDS (0x83220) or IOS_LOOP (0x83198).
   It proves lib/B/Prog/io_send_seg_cut.v iod_head_stmt, as `iod_head`.

   The code (io_send_cg.v header, lines 112-119; listing slots of lib/B/Prog/DgnTransportBList.v):
     0x83148 - 0x83174, 0x83348 - 0x83354  s5 = 0 when f.body_len (the 8-byte load at sp + 64) <> 1; else
                        a0 = f.body (the 8-byte load at sp + 56), whose test against 0 (`beq a0, zero, 0x83358`,
                        the UBSan trap word) is refuted: at a parse that succeeded f.body = p + 30 and 0 < p; the
                        CHECKED 1-byte load of body[0] at f.body; body[0] <> 0 gives s5 = 0, else (0x83348)
                        s5 = (f.ncmds (the 1-byte load at sp + 49) = 1). s5 is the model's keepalive flag
                        io_send_seg_cut.v ios_kaz frame (io_send_segs.v ios_ka);
     0x83178            the 4-byte store of 0 at sp + 4 (io_send's own int display);
     0x8317c            `jal` check_inflight_new (0x84654), return address 0x83180, no argument;
     0x83180 - 0x83194  s6 = the %hi of g_raw (IOS_S6 = TB_g_raw + 1056, the listing's A_HI 57); g_raw (the 4-byte
                        load at 0x5ded60, the listing's object 30) <> 0 or s5 <> 0 goes to 0x83214; else
                        f.body_len = 0 goes to 0x8321c; else the command count loop at 0x83198 = IOS_LOOP with
                        a1 = f.body_len (ANOTHER segment);
     0x83214 - 0x83218  s2 = f.ncmds (the 1-byte load at sp + 49); `j` 0x83220 = IOS_CMDS;
     0x8321c            s2 = 0, then 0x83220 = IOS_CMDS.
   `sp` here is the walk's sp (the entry sp less IOSEND_FRAME = 160).

   The error path this stretch must refute is 0x83364 (`__asan_report_load1`, reached through the slow block
   0x8335c - 0x83360), the checked load of body[0] = p + 30: the byte lies in [p, p + len) (len >= 60 by
   lib/A/Prog/io_send_seg_frm.v ios_len60), which trans_src_ok marks usable. The token engine of
   lib/A/Prog/PaShadow.v decides it: the shadow byte's load leaves a token, the `bne` on it is the ASan slow block,
   and the obligation it leaves is range_addressable of [p + 30, p + 31), which decode_rd_ok
   (lib/B/Prog/DgnTransportBCg.v trans_src_ok_rd) gives.

   The walk: two runs of lib/B/Prog/TransportGRunB.v paj_run_x over the caller's G journal, with the leaf call of
   check_inflight_new between them, lifted by lib/A/Prog/TransportGCg.v gx_call_leaf and the leaf bridge
   lib/B/Prog/DgnTransportBLeafb.v decode_leafb_journal.
     run A (0x83148 .. 0x8317c)  the keepalive flag and the 4-byte store of 0 at sp + 4 (the only byte range this
                                 file writes: a byte of io_send's own window, inside the caller's journal window,
                                 so the run's write right awr_ok_x takes its stack case);
     check_inflight_new          lib/B/Prog/check_inflight_new_cg.v, through transport_leaf_at (no argument);
     run B (0x83180 .. the exits)  s6, g_raw and the three branches.
   Proved here:
     iod_entryA   the symbolic state at the cut 0x83148 (io_send's own 160-byte frame with the three fields the
                  stretch reads and the one word it writes, and the frame's byte body[0] at p + 30);
     iod_runA     0x83148 .. 0x8317c, all three paths, the UBSan trap branch on f.body refuted, the ASan check of
                  body[0] refuted from trans_src_ok, and s5 = ios_kaz frame on each of them;
     iod_call_cin the call of check_inflight_new through gx_call_leaf and decode_leafb_journal;
     iod_entryB, iod_runB  0x83180 .. the three exits: g_raw <> 0 or the keepalive flag to IOS_CMDS with
                  s2 = f.ncmds, body_len = 0 to IOS_CMDS with s2 = 0, else to IOS_LOOP with a1 = body_len;
     iod_close    the cut iod_at rebuilt at the memory run A, the leaf and run B left: the running facts
                  (io_send_seg_cut.v ios_cur), the nine saved words, the registers, the struct, the frame and the
                  world relation, all kept because every byte this stretch changed lies in
                  [sp - ESTACK, sp + 8) ⊆ io_send's own stack window;
     iod_head     the statement iod_head_stmt. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCgRun DgnTransportBLeafb CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_wake_c check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg io_send_cg io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  LeafCgKit AsanKA check_inflight_new_c check_inflight_new_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_new_cg.
Module LINc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_new_c.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The addresses of the stretch                                        *)
(* ------------------------------------------------------------------ *)

(* The return address of the call of check_inflight_new (0x83180). *)
Definition IOD_CIN_RET : Z := IOS_AT 0x184.

Lemma iod_addrs : transportb_text + IOS_DATA = 0x83148 /\ transportb_text + IOD_CIN_RET = 0x83180 /\
  transportb_text + IOS_LOOP = 0x83198 /\ transportb_text + IOS_CMDS = 0x83220.
Proof. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Reading the struct and the frame                                    *)
(* ------------------------------------------------------------------ *)

(* Byte j of the little-endian value of a byte list of n bytes. *)
Lemma iod_le_byte_n : forall (l : list byte) (n j : nat) d, length l = n -> (j < n)%nat ->
  YO0f.le_byte (bytes_le_to_Z l) n j = bv_unsigned (nth j l d).
Proof. intros l n j d <- Hj. exact (tw_le_byte_ble l j d Hj). Qed.

(* Byte j of the n-byte field at offset k of a byte list. *)
Lemma iod_u_at_byte : forall (L : list byte) (k n j : nat), (k + n <= length L)%nat -> (j < n)%nat ->
  YO0f.le_byte (TW.u_at L (Z.of_nat k) n) n j = bv_unsigned (nth (k + j) L (Z_to_bv 8 0)).
Proof.
intros L k n j Hkn Hj.
assert (HL : length (TW.sub L (Z.of_nat k) n) = n) by (apply TWL.length_sub; lia).
unfold TW.u_at.
rewrite (iod_le_byte_n (TW.sub L (Z.of_nat k) n) n j (Z_to_bv 8 0) HL Hj).
rewrite (tw_nth_sub L (Z.of_nat k) n j (Z_to_bv 8 0) ltac:(lia) Hj ltac:(lia)).
replace (Z.to_nat (Z.of_nat k) + j)%nat with (k + j)%nat by lia. reflexivity.
Qed.

(* The n-byte field at offset k of a byte list the view shows at q, as a chunk value. *)
Lemma iod_val_of_garr8 : forall (mm : word -> option byte) q (L : list byte) (k n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> (k + n <= length L)%nat ->
  YI04.val_mem tfibsegs mm (q + Z.of_nat k) n (TW.u_at L (Z.of_nat k) n).
Proof.
intros mm q L k n Hg Hkn j Hj.
assert (Hj2 : (k + j < length (map DSpec.bz L))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte tfibsegs mm q (map DSpec.bz L) (k + j) Hg Hj2) as Hm.
replace (q + Z.of_nat k + Z.of_nat j) with (q + Z.of_nat (k + j)) by lia.
rewrite Hm. f_equal. f_equal.
rewrite (iod_u_at_byte L k n j Hkn Hj).
change (nth (k + j) (map DSpec.bz L) 0) with (nth (k + j) (map DSpec.bz L) (DSpec.bz (Z_to_bv 8 0))).
rewrite map_nth. reflexivity.
Qed.

(* The same, with the offset as a Z (how the struct's fields are named). *)
Lemma iod_val_at : forall (mm : word -> option byte) q (L : list byte) (k : Z) (n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  YI04.val_mem tfibsegs mm (q + k) n (TW.u_at L k n).
Proof.
intros mm q L k n Hg Hk Hkn. replace k with (Z.of_nat (Z.to_nat k)) by lia.
apply (iod_val_of_garr8 mm q L (Z.to_nat k) n Hg). lia.
Qed.

(* An aview equality is an mbyte equality of the restricted memories. *)
Lemma iod_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H m') a) as [b1|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b2|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* garr8 at a later memory that keeps the range's bytes. *)
Lemma iod_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) q l,
  garr8 tfibsegs (mrestrict H m) q l ->
  (forall a, q <= a < q + Z.of_nat (length l) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m') q l.
Proof.
intros H m m' q l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
rewrite (iod_mbyte_of_aview H m m' (q + Z.of_nat j + Z.of_nat 0)); [exact (Hv 0%nat Hi) | apply Hk; lia].
Qed.

Lemma iod_sframe_kept : forall (W : world tfibsegs) mem mem' p fa f,
  (forall a, p <= a < p + 80 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  trans_sframe_at W mem p fa f -> trans_sframe_at W mem' p fa f.
Proof.
intros W mem mem' p fa f Heq (H0 & H8 & SB & HG & HL & R). split; [exact H0|]. split; [exact H8|].
exists SB. split; [|split; [exact HL | exact R]].
apply (iod_garr8_kept _ mem mem' p _); [exact HG|].
intros a Ha. rewrite length_map, HL in Ha. change (Z.of_nat 80) with 80 in Ha. apply Heq. exact Ha.
Qed.

(* An 8-byte word of a view, kept by a step that keeps its eight bytes. *)
Lemma iod_rdword_kept : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a Hk. unfold rdword.
pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)),
        (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)). reflexivity.
Qed.

Lemma iod_saved_kept : forall (W : world tfibsegs) mem mem' regs,
  (forall a, spZ regs - 72 <= a < spZ regs -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ios_saved W mem regs -> ios_saved W mem' regs.
Proof.
intros W mem mem' regs Heq HS. unfold ios_saved in *. rewrite Forall_forall in HS |- *.
intros o Ho. rewrite <- (HS o Ho). apply iod_rdword_kept. intros i Hi. apply Heq.
unfold IOS_SAVED in Ho. cbn [In] in Ho.
repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho.
Qed.

(* bv_eqb of two 64-bit literals. *)
Lemma iod_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
intros x y Hx Hy. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma iod_eqb0 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
intros x Hx. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616.
rewrite Z.mod_0_l by lia.
destruct (Z.eqb_spec x 0) as [->|Hne]; [rewrite Z.mod_0_l by lia; reflexivity|].
apply Z.eqb_neq.
destruct (Z_lt_le_dec x 0) as [Hlt|Hge].
- assert (Hm : x mod 18446744073709551616 = x + 18446744073709551616).
  { rewrite <- (Z.mod_add x 1 18446744073709551616) by lia. rewrite Z.mul_1_l.
    apply Z.mod_small. lia. }
  rewrite Hm. lia.
- rewrite Z.mod_small by lia. exact Hne.
Qed.

(* The value a 1-byte unsigned load leaves: the atom, zero-extended. *)
Lemma iod_zext8_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 256 ->
  sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 u.
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small u) by lia. apply Z.mod_small. lia.
Qed.

(* The value a signed 4-byte load leaves. *)
Lemma iod_sext32_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The two ALU steps that build the keepalive flag (`addi -1` then `sltiu 1`). *)
Lemma iod_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma iod_sltu_den : forall (x y : word),
  alu64 ALU_SLTU x y = Z_to_bv 64 (if bv_unsigned x <? bv_unsigned y then 1 else 0).
Proof.
intros x y. cbn [alu64 alu]. rewrite bv_ltu_unsigned.
destruct (bv_unsigned x <? bv_unsigned y); reflexivity.
Qed.

(* s5 after 0x83348 - 0x83350: 1 exactly when f.ncmds is 1. *)
Lemma iod_s5_den : forall E n ncm, ew E n = Z_to_bv 64 ncm -> 0 <= ncm < 256 ->
  sv_denot E (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff n 0)) (SLit (-1))) (SLit 1))
    = Z_to_bv 64 (if ncm =? 1 then 1 else 0).
Proof.
intros E n ncm Hn Hncm.
change (sv_denot E (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff n 0)) (SLit (-1))) (SLit 1)))
  with (alu64 ALU_SLTU (alu64 ALU_ADD (sv_denot E (SExt false 8 (SOff n 0))) (Z_to_bv 64 (-1)))
          (Z_to_bv 64 1)).
rewrite (iod_zext8_den E n ncm Hn Hncm), (iod_add_den ncm (-1)), iod_sltu_den.
f_equal. change (bv_unsigned (Z_to_bv 64 1)) with 1.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616.
destruct (Z.eqb_spec ncm 1) as [->|Hne]; [reflexivity|].
destruct (Z.eq_dec ncm 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.mod_small (ncm + -1)) by lia.
destruct (Z.ltb_spec (ncm + -1) 1); [lia | reflexivity].
Qed.

(* The byte body[0] the stretch loads, as the model's at8 of the body. *)
Lemma iod_nth_skipn : forall (m : nat) (l : list byte) d, nth 0 (skipn m l) d = nth m l d.
Proof.
induction m as [|m IH]; intros l d; [reflexivity|].
destruct l as [|x l]; cbn; [reflexivity | apply IH].
Qed.

Lemma iod_b0 : forall frame, DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK -> (31 <= length frame)%nat ->
  TW.u_at frame 30 1 = DSpec.at8 (ios_body frame) 0.
Proof.
intros frame HOK Hl.
destruct (ios_body_len frame HOK) as (EB & _ & _ & _).
unfold DSpec.at8, DSpec.bz, DSpec.b8. rewrite EB, iod_nth_skipn.
pose proof (iod_u_at_byte frame 30 1 0 ltac:(lia) ltac:(lia)) as Hb.
change (Z.of_nat 30) with 30 in Hb. change (30 + 0)%nat with 30%nat in Hb.
rewrite <- Hb.
pose proof (TWL.u_at_range frame 30 1) as R. change (8 * Z.of_nat 1) with 8 in R.
symmetry. exact (tw_le_byte1 (TW.u_at frame 30 1) ltac:(lia)).
Qed.

(* The struct's body pointer at a parse that succeeded: the frame's byte 30. *)
Lemma iod_sf_body : forall (fa : Z) (frame : list byte), DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK ->
  TCt.sf_ptr fa (TC.rf frame) (DSpec.sf_body (TC.rf frame)) = fa + 30.
Proof.
intros fa frame HOK.
destruct (ios_fields frame HOK)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fbody & _ & _ & _).
unfold TCt.sf_ptr. rewrite HOK, Z.eqb_refl. cbv iota. rewrite Fbody. reflexivity.
Qed.

(* The keepalive flag, branch by branch. *)
Lemma iod_kaz_val : forall frame,
  ios_kaz frame = (if ios_blen frame =? 1
                   then (if DSpec.at8 (ios_body frame) 0 =? 0
                         then (if DSpec.sf_ncmds (TC.rf frame) =? 1 then 1 else 0) else 0) else 0).
Proof.
intros frame. unfold ios_kaz, ios_ka.
destruct (ios_blen frame =? 1); cbn [andb]; [|reflexivity].
destruct (DSpec.at8 (ios_body frame) 0 =? 0); cbn [andb]; [|reflexivity].
destruct (DSpec.sf_ncmds (TC.rf frame) =? 1); reflexivity.
Qed.

(* env_agree survives the token engine's extra atoms. *)
Lemma iod_agree_ext : forall rg (l : list word) (E : env) n w, (32 <= n)%nat ->
  env_agree 32 (Ereg rg l) E -> env_agree 32 (Ereg rg l) (ewset E n w).
Proof.
intros rg l E n w Hn (H1 & H2). split; [| exact H2].
intros m Hm. rewrite ew_ewset_other by lia. exact (H1 m Hm).
Qed.

Lemma iod_agree {fx : YK11.FPState} {rc : YM05.RunCeil} :
  forall rg l, env_agree 32 (Ereg rg l) (Eimg (PI := PI_transportb) (Ereg rg l)).
Proof.
intros rg l. split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.

(* A register of the callee-saved set, kept by a call (aregs_preserved). *)
Lemma iod_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof.
intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H.
assert (E : Z_to_bv 5 (bv_unsigned r) = r)
  by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
rewrite E in H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic states of the two runs                                 *)
(* ------------------------------------------------------------------ *)

(* run A (0x83148 .. 0x8317c). Atoms: 0 .. 31 the registers at the cut (2 = sp, 9 = s1 = p, 20 = s4 = the shadow
   base), 32 = f.body_len, 33 = f.ncmds, 34 = the byte body[0]. Regions: io_send's own 160-byte frame above sp,
   writable exactly at the int display [4, 8) (the one store of the stretch) and holding the three fields it reads,
   and the frame's byte body[0] at p + 30. *)
Definition iod_frameA : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 160 4 8
    [YP09.mkChunk 49 (CVal 1 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 9 30));
     YP09.mkChunk 64 (CVal 8 (SOff 32 0))].
Definition iod_bodyA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 30 31 0 0 [YP09.mkChunk 30 (CVal 1 (SOff 34 0))].
Definition iod_regionsA : smem := [iod_frameA; iod_bodyA].
Definition iod_factsA : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4096 (2 ^ 47 - 60) 0);
           (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_iodA : sstate := mkSS IOS_DATA sr_atoms iod_regionsA None iod_factsA.

(* The token engine's shadow base (s4) and its shadow entries (none: the only instrumented check of the stretch is
   decided by the obligation the token leaves). *)
Definition IOD_Bx : sv := SOff 20 0.
Definition IOD_SH : list shent := [].

(* run B (0x83180 .. the exits). Atoms: 32 = g_raw, 33 = f.ncmds, 34 = f.body_len. Regions: g_raw's 4 bytes (the
   listing's object 30) and io_send's frame, both read-only. *)
Definition iod_rawB : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 30)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition iod_frameB : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 160 0 0
    [YP09.mkChunk 49 (CVal 1 (SOff 33 0)); YP09.mkChunk 64 (CVal 8 (SOff 34 0))].
Definition iod_regionsB : smem := [iod_frameB; iod_rawB].
Definition iod_factsB : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 30, mkAF TB_g_raw TB_g_raw 5)] [] [].
Definition ss_iodB : sstate := mkSS IOD_CIN_RET sr_atoms iod_regionsB None iod_factsB.

(* The registers run A leaves untouched (io_send's own, less s5, which it sets). *)
Definition IOD_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv.
(* The registers run B leaves untouched (io_send's own, less s2 and s6, which it sets). *)
Definition IOD_KEEPB : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25; 26; 27]%bv.
(* The registers the cut iod_at reads, kept by the whole stretch. *)
Definition IOD_KEEPC : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 24; 25; 26; 27]%bv.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac iod_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "iod_reg: no match for" T; fail
  end.

(* The value of a register of a stopped run, as the symbolic value its state names. *)
Ltac iod_rv HS :=
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

(* Normalize a symbolic state in place. *)
Ltac iod_rw HS := lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.

(* A register index is callee-saved: compute its number, then compare. *)
Ltac iod_cs :=
  unfold acallee_saved;
  repeat (lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end);
  lia.

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac iod_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of run A: the only writable window is io_send's int display at sp + 4, a byte of the caller's
   journal window; every other region is read-only. *)
Ltac iod_awrA Usp :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite ?ew_ewset_other in Ha by lia; rewrite Usp in Ha;
              left; split; [unfold awr_byte; left; lia | lia] ] |]);
  apply awr_ok_x_nil.

(* The write rights of a run whose regions are all read-only. *)
Ltac iod_awrRO :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* What the leaf call needs of the harness globals                     *)
(* ------------------------------------------------------------------ *)

(* Every payload byte of the 18 harness globals lies in a loaded segment of image B, so no world hides it. *)
Lemma iod_hull_vis : forall (W : world tfibsegs) x,
  TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI -> w_H W (Z_to_bv 64 x) = false.
Proof.
intros W x Hx. apply (decode_vis_seg W).
apply (decode_covers_img TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) x);
  [vm_compute; reflexivity | lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory the leaf reads. *)
Lemma iod_tw_csw : forall (W : world tfibsegs) mem Bx,
  tw_at TMAP_B (aview tfibsegs (w_H W) mem) Bx -> tw_at TMAP_B (csw_view mem) Bx.
Proof.
intros W mem Bx H. apply (tw_kept TMAP_B _ _ Bx H). intros x Hx.
unfold csw_view. rewrite (decode_aview_mrd W mem x (iod_hull_vis W x (TMAP_B_hull x Hx))). reflexivity.
Qed.

(* A range of the harness globals' hull is visible, so a leaf's footprint may read it. *)
Lemma iod_rng_hull : forall (W : world tfibsegs) lo len, TG.G_HARNESS_B_LO <= lo -> lo + len <= TG.G_HARNESS_B_HI ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
intros W lo len H1 H2.
apply (decode_rng W); [unfold TG.G_HARNESS_B_LO in *; lia | unfold TG.G_HARNESS_B_HI in *; lia |].
intros b Hb. apply iod_hull_vis. lia.
Qed.

Section dataw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma iod_base : forall o : Z, BASE + o = transportb_text + o.
Proof. intros o. f_equal. Qed.

(* The stack window of a call from io_send's frame: the struct at sp + 8 lies in the caller's journal window,
   above the callee's ESTACK window. *)
Definition iod_call_win (STK sp0 sp : Z) : Prop :=
  sp mod 16 = 0 /\ sp0 - STK <= sp - ESTACK /\ sp + 88 <= sp0.

(* What io_send's fixed entry facts give about the stack. *)
Lemma iod_geo : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw,
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  @AR rc segs B lyc Sc W memc mdc /\ YM05.alloc_ceiling <= sp0 - STK /\ sp0 - STK <= spZ regs - IOSEND_STK /\
  spZ regs <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ spZ regs mod 16 = 0.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX.
  destruct HFX as (HJ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hhi & _).
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (H16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  split; [exact HAR|]. repeat split; lia.
Qed.

(* A step of the walk that changes only bytes of io_send's stack window or bytes of G in its written range keeps
   the running kept fact. *)
Lemma iod_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi
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
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR
    (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
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

(* The running facts at a cut, from those at the previous cut and the bytes the step changed (Zs: bytes of
   io_send's stack window). *)
Lemma iod_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    ly2 S2 (W2 : world segs) mem2 md2 mem3 md3 (Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> spZ regs - IOSEND_STK <= a < spZ regs) ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 mem3 md3 Zs
    LAWS HGX HFX (HJ & HF & HP & HM & HK) HJ3 Hkp Hgr HZ.
  destruct (iod_geo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX)
    as (HAR & Hce & Hlo & Hhi & H47 & _).
  split; [exact HJ3|]. split; [exact HF|]. split; [exact HP|]. split; [exact HM|].
  apply (iod_kept_step _ _ _ _ _ mdc W2 mem2 mem3 _ _ _ Zs LAWS HGX HAR HK Hkp Hgr
    ltac:(intros a Ha; left; exact (HZ a Ha)) ltac:(lia) ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut 0x83148                               *)
(* ------------------------------------------------------------------ *)

(* The walk's valuation for run A: the registers at the cut, and f.body_len, f.ncmds, body[0] as atoms 32, 33, 34. *)
Definition iod_EA (regs2 : bvmap 5 word) (blen ncm b0 : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 blen; Z_to_bv 64 ncm; Z_to_bv 64 b0]).

Lemma iod_entryA : forall (W2 : world segs) mem2 (regs2 : bvmap 5 word) (sp p blen ncm b0 : Z),
  YK11.getr regs2 2 = w64 sp -> YK11.getr regs2 9 = w64 p -> YK11.getr regs2 20 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  4096 <= p -> p + 60 <= 2 ^ 47 -> (p + 31 <= sp \/ sp + 160 <= p) ->
  0 <= blen < 2 ^ 64 -> 0 <= ncm < 256 -> 0 <= b0 < 256 ->
  (forall o, 4 <= o < 8 -> apresent (w_H W2) mem2 (sp + o)) ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 49) 1 ncm ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 56) 8 (p + 30) ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 64) 8 blen ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (p + 30) 1 b0 ->
  st_ok_pi segs VAL (iod_EA regs2 blen ncm b0) ss_iodA
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_DATA)) mem2 (YK11.seg_rom segs)))
  /\ sh_ok segs IOD_Bx IOD_SH (iod_EA regs2 blen ncm b0) (mrestrict (w_H W2) mem2).
Proof.
intros W2 mem2 regs2 sp p blen ncm b0 H2 H9 H20 Hs1 Hs2 Hs16 Hp1 Hp2 Hdisj Hbl Hnc Hb0 Hpres V49 V56 V64 V30.
set (E := iod_EA regs2 blen ncm b0).
assert (E2 : ew E 2 = YK11.getr regs2 2) by (unfold E, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E9 : ew E 9 = YK11.getr regs2 9) by (unfold E, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = YK11.getr regs2 20) by (unfold E, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2, H2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = p) by (rewrite E9, H9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20, H20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 blen)
  by (unfold E, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ncm)
  by (unfold E, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 b0)
  by (unfold E, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
split; [|unfold sh_ok, IOD_SH; constructor].
rewrite restrict_mkst_fx. unfold ss_iodA, iod_regionsA.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold iod_frameA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable segs); apply Hpres; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val segs E _ sp 49 1 (SOff 33 0) ncm);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V49].
    * apply (chunk_ok_val segs E _ sp 56 8 (SOff 9 30) (p + 30));
        [cbn [sv_denot]; rewrite U9; reflexivity | cbn; lia | lia | exact V56].
    * apply (chunk_ok_val segs E _ sp 64 8 (SOff 32 0) blen);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V64].
  + unfold iod_bodyA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ p 30 1 (SOff 34 0) b0);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V30].
- apply pairwise_disjoint_of_extents.
  unfold iod_frameA, iod_bodyA, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold iod_factsA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U20.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* run A: the keepalive flag and the store, 0x83148 .. 0x8317c         *)
(* ------------------------------------------------------------------ *)

(* The close of one path of run A: the memory it leaves differs from the cut's only on the int display, the
   registers are the cut's but for s5 and ra. It leaves one goal, the value of s5 on that path. *)
Ltac iod_closeA HS HJ HK Km Gm AG :=
  pmkst HS;
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (YK11.mkst rgx (Z_to_bv 64 LINc.CHECK_INFLIGHT_NEW) mm rom) mdx) Qx) end;
  apply HK;
  [ exact HJ
  | exact Km
  | exact Gm
  | eapply (regs_kept_of_st_ok segs _ _ _ _ _ IOD_KEEP HS);
      [ repeat (apply iod_agree_ext; [lia|]); exact AG | vm_compute; reflexivity ]
  | iod_rv HS
  | iod_rv HS; apply codeptr_val; assumption ].

Lemma iod_runA : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_at_csf B MT STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  (forall mem3 md3 (regs3 : bvmap 5 word),
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md3 (k + 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_FRAME + 4 <= a < spZ regs - IOSEND_FRAME + 8) ->
        aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
     (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
     (forall r, In r IOD_KEEP -> YK11.getr regs3 r = YK11.getr regs2 r) ->
     YK11.getr regs3 21 = w64 (ios_kaz frame) ->
     YK11.getr regs3 1 = Z_to_bv 64 (BASE + IOD_CIN_RET) ->
     SRr segs W2
       (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 LINc.CHECK_INFLIGHT_NEW) mem3 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_DATA) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
  HL HF HIN HCSF HK.
destruct HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRFc & HCSFc & HAF & HLC & HCIR & HSW
  & HIN2 & HTO & HLF & HKD & HCLS & HLD & HAI1).
destruct HF as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff & Hfat
  & Hfail & Hrom & Htw & Hinv1 & Hinv2 & Hnev).
unfold ios_at_csf, ios_e2_at in HIN.
destruct HIN as (HCUR & HSAV & HREG & HS811 & HSF & HSFsrc & HGARR & HSRC & HTW).
destruct HCUR as (HJ2 & Hfrs & Hperm & Hmo & HKEPT).
destruct HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof HJ as (HSTK & _ & (memS0 & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS0.
pose proof HJ2 as (HSTK2 & _ & (memS2 & HJ2i & _) & _).
rewrite !Z.add_0_r in HJ2i.
pose proof HJ2i as (HAR2 & HLE2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
clear HJ2i memS2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 160 + 4096 <= IOSEND_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
pose proof (ios_len60 (ios_B0 Bw) frame (ios_B0 Bw) HCSF) as HL60.
pose proof (ios_sf_code (ios_B0 Bw) frame (ios_B0 Bw) HCSF) as HOK.
assert (Hpp : 4096 <= p /\ p + Z.of_nat (length frame) <= 2 ^ 47).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p (Z.of_nat (length frame)) HAR0 Hsrc ltac:(lia))
    as [Hpl | Hpl]; lia. }
destruct Hpp as (Hp1 & Hplen).
assert (Hp2 : p + 60 <= 2 ^ 47) by lia.
assert (EFO : IOS_F_OFF = 8) by reflexivity.
assert (ESF : SF_SIZE = 80) by reflexivity.
set (sp := spZ regs - IOSEND_FRAME) in *.
assert (Esp : sp = spZ regs - IOSEND_FRAME) by reflexivity.
assert (Hdj : p + 31 <= sp \/ sp + 160 <= p)
  by (unfold decode_off_win in Hoff; destruct Hoff as [Hf1|Hf1]; [left | right]; lia).
rewrite EFO in HSF, HSFsrc.
destruct HSF as (Hfp0 & Hfp8 & SBl & HSB & HSBlen & F0 & F8 & F16 & F24 & F26 & F28 & F30 & F32 & F36 & F40 &
  F41 & F48 & F56 & F64 & F72).
assert (HSBl : Z.of_nat (length SBl) = 80) by (rewrite HSBlen; reflexivity).
assert (V49 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 49) 1 (TW.u_at SBl 41 1)).
{ replace (sp + 49) with (sp + 8 + 41) by lia.
  apply (iod_val_at (mrestrict (w_H W2) mem2) (sp + 8) SBl 41 1 HSB); [lia | cbn; lia]. }
assert (V56 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 56) 8 (p + 30)).
{ replace (sp + 56) with (sp + 8 + 48) by lia.
  rewrite <- (iod_sf_body p frame HOK), <- F48.
  apply (iod_val_at (mrestrict (w_H W2) mem2) (sp + 8) SBl 48 8 HSB); [lia | cbn; lia]. }
assert (V64 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 64) 8 (TW.u_at SBl 56 8)).
{ replace (sp + 64) with (sp + 8 + 56) by lia.
  apply (iod_val_at (mrestrict (w_H W2) mem2) (sp + 8) SBl 56 8 HSB); [lia | cbn; lia]. }
assert (V30 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (p + 30) 1 (TW.u_at frame 30 1))
  by exact (iod_val_at (mrestrict (w_H W2) mem2) p frame 30 1 HGARR ltac:(lia) ltac:(cbn; lia)).
pose proof (TWL.u_at_range SBl 56 8) as R56. change (8 * Z.of_nat 8) with 64 in R56.
pose proof (TWL.u_at_range SBl 41 1) as R41. change (8 * Z.of_nat 1) with 8 in R41.
pose proof (TWL.u_at_range frame 30 1) as R30. change (8 * Z.of_nat 1) with 8 in R30.
set (EA := iod_EA regs2 (TW.u_at SBl 56 8) (TW.u_at SBl 41 1) (TW.u_at frame 30 1)) in *.
assert (E32 : ew EA 32 = Z_to_bv 64 (TW.u_at SBl 56 8))
  by (unfold EA, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew EA 33 = Z_to_bv 64 (TW.u_at SBl 41 1))
  by (unfold EA, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew EA 34 = Z_to_bv 64 (TW.u_at frame 30 1))
  by (unfold EA, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (D32 : sv_denot EA (SOff 32 0) = Z_to_bv 64 (TW.u_at SBl 56 8))
  by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (E9 : ew EA 9 = YK11.getr regs2 9) by (unfold EA, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E2 : ew EA 2 = YK11.getr regs2 2) by (unfold EA, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew EA 20 = YK11.getr regs2 20) by (unfold EA, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U9 : bv_unsigned (ew EA 9) = p) by (rewrite E9, R9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew EA 2) = sp) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (UX : U EA (SOff 9 30) = p + 30) by (rewrite U_SOff, U9; apply zcanon_id; unfold M64; lia).
assert (UB : U EA IOD_Bx = SHADOW_OFF).
{ unfold IOD_Bx. rewrite U_SOff, E20, R20. unfold w64.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  apply zcanon_id. unfold SHADOW_OFF, M64. lia. }
destruct (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 p (Z.of_nat (length frame)) HAR2 HSRC ltac:(lia))
  as (HRDv & HRA & HRH & HRM & HR0 & HR63).
destruct (iod_entryA W2 mem2 regs2 sp p (TW.u_at SBl 56 8) (TW.u_at SBl 41 1) (TW.u_at frame 30 1)
  R2 R9 R20 ltac:(lia) ltac:(lia) ltac:(rewrite Esp, Zminus_mod, Hsp16, FF; reflexivity) Hp1 Hp2
  Hdj ltac:(lia) ltac:(cbn in R41; lia) ltac:(cbn in R30; lia)
  ltac:(intros o Ho; apply Hpres2; lia) V49 V56 V64 V30) as [HS SHOK].
fold EA in HS, SHOK.
assert (HEI : img_env VAL A_LIM EA) by (unfold EA, iod_EA; apply Eimg_env).
assert (AGbase : env_agree 32
  (Ereg regs2 [Z_to_bv 64 (TW.u_at SBl 56 8); Z_to_bv 64 (TW.u_at SBl 41 1); Z_to_bv 64 (TW.u_at frame 30 1)]) EA)
  by (unfold EA, iod_EA; apply iod_agree).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_DATA)) mem2 (YK11.seg_rom segs)) md2) Qx)
end.
(* 0x83148 - 0x8314c: a0 = f.body_len, a1 = 1 *)
paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
{ iod_awrA U2. }
rename ms into msa.
assert (Ka : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 4 <= a < sp + 8) ->
  aview segs (w_H W2) (ms_mem msa) a = aview segs (w_H W2) mem2 a).
{ apply (kept_of_frame _ _ _ _ _ (fun a => sp + 4 <= a < sp + 8) HFr).
  intros b wlo whi x Hin Hx.
  iod_win Hin Hx ltac:(rewrite ?ew_ewset_other in Hx by lia; rewrite ?U2 in Hx; lia). }
assert (Ga : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msa) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
all: rewrite D32 in Hc.
all: cbn [branch_taken sv_denot] in Hc.
all: rewrite (iod_eqb (TW.u_at SBl 56 8) 1 ltac:(lia) ltac:(lia)) in Hc.
all: set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *.
all: clearbody md1.
all: clear mat.
- (* f.body_len <> 1: the keepalive flag is 0 *)
  apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hblen.
  paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
  { iod_awrA U2. }
  rename ms into msc.
  assert (Kc : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 4 <= a < sp + 8) ->
    aview segs (w_H W2) (ms_mem msc) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite <- (Ka a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (fun a0 => sp + 4 <= a0 < sp + 8) HFr);
      [intros b wlo whi x Hin Hx;
       iod_win Hin Hx ltac:(rewrite ?ew_ewset_other in Hx by lia; rewrite ?U2 in Hx; lia)
      | exact Ha | exact Hn]. }
  assert (Gc : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msc) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (Ga a Ha))).
  clear HF HFr HG.
  iod_closeA HS HJ2 HK Kc Gc AGbase.
  + (* s5 = 0: the body is not one byte long *)
    change (sv_denot EA (SLit 0)) with (Z_to_bv 64 0).
    unfold w64. f_equal. rewrite iod_kaz_val. unfold ios_blen. rewrite <- F56.
    destruct (Z.eqb_spec (TW.u_at SBl 56 8) 1) as [Hz|_]; [exfalso; exact (Hblen Hz) | reflexivity].
- (* f.body_len = 1: the body pointer (whose test against 0, the branch to the trap word 0x83358, the engine
     decides from the fact 4096 <= atom 9) and the CHECKED 1-byte load of body[0] *)
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hblen.
  (* the shadow byte of p + 30 is the cut's: the stretch stores only at sp + 4 *)
  assert (HKsh : forall x, 0 <= x < 2 ^ 47 ->
    aview segs (w_H W2) (ms_mem msa) (shadow_of_addr SHADOW_OFF x) =
    aview segs (w_H W2) mem2 (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. unfold shadow_of_addr.
    pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as Hd.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Hd0.
    change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
    apply Ka; unfold SHADOW_OFF; lia. }
  assert (HRAa : range_addressable (aview segs (w_H W2) (ms_mem msa)) SHADOW_OFF p
    (Z.of_nat (length frame))).
  { intros x Hx. destruct (HRA x Hx) as (sv & Hsv & Hok).
    exists sv. split; [|exact Hok]. rewrite (HKsh x ltac:(lia)). exact Hsv. }
  paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
  { eapply obl_of_range; [exact HRAa | exact UB | rewrite UX; lia | rewrite UX; lia]. }
  { iod_awrA U2. }
  rename ms into msd.
  assert (Kd : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 4 <= a < sp + 8) ->
    aview segs (w_H W2) (ms_mem msd) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite <- (Ka a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (fun a0 => sp + 4 <= a0 < sp + 8) HFr);
      [intros b wlo whi x Hin Hx;
       iod_win Hin Hx ltac:(rewrite ?ew_ewset_other in Hx by lia; rewrite ?U2 in Hx; lia)
      | exact Ha | exact Hn]. }
  assert (Gd : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msd) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (Ga a Ha))).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  all: lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    let E34x := fresh "E34x" in
    assert (E34x : ew Ex 34 = Z_to_bv 64 (TW.u_at frame 30 1))
      by (rewrite ?ew_ewset_other by lia; exact E34);
    rewrite (iod_zext8_den Ex 34 (TW.u_at frame 30 1) E34x ltac:(lia)) in Hc end.
  all: cbn [branch_taken sv_denot] in Hc.
  all: rewrite (iod_eqb (TW.u_at frame 30 1) 0 ltac:(lia) ltac:(lia)) in Hc.
  + (* body[0] = 0: the keepalive flag is f.ncmds = 1 *)
    apply Z.eqb_eq in Hc. rename Hc into Hb0.
    paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
    { iod_awrA U2. }
    rename ms into mse.
    assert (Ke : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 4 <= a < sp + 8) ->
      aview segs (w_H W2) (ms_mem mse) a = aview segs (w_H W2) mem2 a).
    { intros a Ha Hn. rewrite <- (Kd a Ha Hn).
      apply (kept_of_frame _ _ _ _ _ (fun a0 => sp + 4 <= a0 < sp + 8) HFr);
        [intros b wlo whi x Hin Hx;
         iod_win Hin Hx ltac:(rewrite ?ew_ewset_other in Hx by lia; rewrite ?U2 in Hx; lia)
        | exact Ha | exact Hn]. }
    assert (Ge : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem mse) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (Gd a Ha))).
    clear HF HFr HG.
    iod_closeA HS HJ2 HK Ke Ge AGbase.
    * lazymatch goal with |- sv_denot ?Ex _ = _ =>
        let E33x := fresh "E33x" in
        assert (E33x : ew Ex 33 = Z_to_bv 64 (TW.u_at SBl 41 1))
          by (rewrite ?ew_ewset_other by lia; exact E33);
        rewrite (iod_s5_den Ex 33 (TW.u_at SBl 41 1) E33x ltac:(cbn in R41; lia)) end.
      unfold w64. f_equal. rewrite iod_kaz_val. unfold ios_blen. rewrite <- F56, Hblen.
      rewrite <- (iod_b0 frame HOK ltac:(lia)), Hb0. rewrite <- F41. reflexivity.
  + (* body[0] <> 0: the keepalive flag is 0 *)
    apply Z.eqb_neq in Hc. rename Hc into Hb0.
    paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
    { iod_awrA U2. }
    rename ms into msf.
    assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 4 <= a < sp + 8) ->
      aview segs (w_H W2) (ms_mem msf) a = aview segs (w_H W2) mem2 a).
    { intros a Ha Hn. rewrite <- (Kd a Ha Hn).
      apply (kept_of_frame _ _ _ _ _ (fun a0 => sp + 4 <= a0 < sp + 8) HFr);
        [intros b wlo whi x Hin Hx;
         iod_win Hin Hx ltac:(rewrite ?ew_ewset_other in Hx by lia; rewrite ?U2 in Hx; lia)
        | exact Ha | exact Hn]. }
    assert (Gf : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msf) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (Gd a Ha))).
    clear HF HFr HG.
    iod_closeA HS HJ2 HK Kf Gf AGbase.
    * change (sv_denot EA (SLit 0)) with (Z_to_bv 64 0).
      unfold w64. f_equal. rewrite iod_kaz_val.
      rewrite <- (iod_b0 frame HOK ltac:(lia)).
      destruct (Z.eqb_spec (ios_blen frame) 1) as [_|_]; [|reflexivity].
      destruct (Z.eqb_spec (TW.u_at frame 30 1) 0) as [Hz|_]; [exfalso; exact (Hb0 Hz) | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* The leaf call of check_inflight_new                                 *)
(* ------------------------------------------------------------------ *)

(* What a leaf call returns (DgnTransportBLeafb.v decode_leafb_journal's facts with RES = None, WR = [] and the
   leaf's X Bx = Bx). *)
Definition iod_lr (regsT : bvmap 5 word) (W2 : world segs) (memT : word -> option byte) (Bx : list byte)
    (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  aregs_preserved regsT regs2 /\ (forall r, None = Some r -> YK11.getr regs2 10 = w64 r) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> ~ LCK.in_wr [] a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W2) memT a) /\
  (forall a, apresent (w_H W2) memT a -> apresent (w_H W2) mem2 a) /\ Bx = Bx.

(* check_inflight_new at 0x84654 (call at 0x8317c), no argument. *)
Lemma iod_call_cin : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) memT mdT k
    (regsT : bvmap 5 word) (sp : Z) (Bx : list byte),
  transport_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_check_inflight_new_cg) fx') ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 memT mdT k ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 sp ->
  YK0s.ret_ok (YK11.getr regsT (Z_to_bv 5 1)) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  iod_call_win STK sp0 sp ->
  tw_at TMAP_B (aview segs (w_H W2) memT) Bx -> TC.check_inflight_new_m Bx = Some (Bx, tt) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LINc.CHECK_INFLIGHT_NEW) memT (YK11.seg_rom segs)) mdT)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsT (Z_to_bv 5 1)) mem3 (YK11.seg_rom segs)) md3 /\
       @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
         ly2 S2 W2 mem3 md3 k /\
       iod_lr regsT W2 memT Bx regs3 mem3 md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k regsT sp Bx HCELLS LAWS LEAF HJ
    R2 Rra R3 R4 (Hal & Hlo & Hhi) HTW HM.
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (SPu : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp) by (rewrite R2; apply unsigned_lit_small; lia).
  apply (gx_call_leaf segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k _
    (YK11.getr regsT (Z_to_bv 5 1)) (iod_lr regsT W2 memT Bx) HJ).
  intros memS HJS.
  pose proof HJS as (HAR & Hly & _).
  unfold iod_lr.
  apply (decode_leafb_journal B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0 own ly2 S2 mdT k (sp - sp0)
    LINc.CHECK_INFLIGHT_NEW None [] (fun _ => Bx = Bx) HJS).
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
    unfold transport_leaf_at, LIN.transport_check_inflight_new_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT mdT (sp - ESTACK) Bx Bx HPRE).
    cbv zeta in LF.
    apply LF; clear LF.
    + exact (iod_tw_csw W2 memT Bx HTW).
    + exact HM.
    + rewrite SPu. apply (decode_leafb_stk_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - ESTACK) sp HJS); lia.
    + rewrite SPu. unfold LINc.CHECK_INFLIGHT_NEW_FRAME. lia.
    + unfold AKA.off_stk. rewrite SPu.
      unfold LINc.CHECK_INFLIGHT_NEW_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
    + rewrite SPu. apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - LINc.CHECK_INFLIGHT_NEW_FRAME) LINc.CHECK_INFLIGHT_NEW_FRAME HJS);
        unfold LINc.CHECK_INFLIGHT_NEW_FRAME; lia.
    + apply iod_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_STATE, TB_M, TW.A_M_state, TW.OFF_M,
        TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    + apply iod_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_FLY_ON, TB_M, TW.A_M_fly_on, TW.OFF_M,
        TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    + apply iod_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_NOW, TB_g_now,
        TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    + apply iod_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_BACKOFF, TB_M, TW.A_M_backoff_until, TW.OFF_M,
        TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* run B: s6, g_raw and the three branches, 0x83180 .. the exits       *)
(* ------------------------------------------------------------------ *)

Definition iod_EB (regs3 : bvmap 5 word) (graw ncm blen : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs3 [Z_to_bv 64 graw; Z_to_bv 64 ncm; Z_to_bv 64 blen]).

Lemma iod_entryB : forall (W2 : world segs) mem3 (regs3 : bvmap 5 word) (sp graw ncm blen : Z),
  YK11.getr regs3 2 = w64 sp -> YK11.getr regs3 20 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= graw < 2 ^ 32 -> 0 <= ncm < 256 -> 0 <= blen < 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) TB_g_raw 4 graw ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) (sp + 49) 1 ncm ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) (sp + 64) 8 blen ->
  st_ok_pi segs VAL (iod_EB regs3 graw ncm blen) ss_iodB
    (restrict (w_H W2) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOD_CIN_RET)) mem3 (YK11.seg_rom segs)))
  /\ sh_ok segs IOD_Bx IOD_SH (iod_EB regs3 graw ncm blen) (mrestrict (w_H W2) mem3).
Proof.
intros W2 mem3 regs3 sp graw ncm blen H2 H20 Hs1 Hs2 Hs16 Hgr Hnc Hbl V0 V49 V64.
set (E := iod_EB regs3 graw ncm blen).
assert (E2 : ew E 2 = YK11.getr regs3 2) by (unfold E, iod_EB; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = YK11.getr regs3 20) by (unfold E, iod_EB; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2, H2; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20, H20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 graw)
  by (unfold E, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ncm)
  by (unfold E, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 blen)
  by (unfold E, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (EO : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
  by (unfold E, iod_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VO : VAL (A_OBJ 30) = TB_g_raw) by (vm_compute; reflexivity).
assert (UO : bv_unsigned (ew E (A_OBJ 30)) = TB_g_raw)
  by (rewrite EO, VO; apply unsigned_lit_small; unfold TB_g_raw; lia).
split; [|unfold sh_ok, IOD_SH; constructor].
rewrite restrict_mkst_fx. unfold ss_iodB, iod_regionsB.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold iod_frameB, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs E _ sp 49 1 (SOff 33 0) ncm);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V49].
    * apply (chunk_ok_val segs E _ sp 64 8 (SOff 34 0) blen);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V64].
  + unfold iod_rawB, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UO. split; [unfold TB_g_raw; lia|]. split; [unfold TB_g_raw; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TB_g_raw 0 4 (SOff 32 0) graw);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia
      | rewrite Z.add_0_r; exact V0].
- apply pairwise_disjoint_of_extents.
  unfold iod_frameB, iod_rawB, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, UO.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | unfold TB_g_raw; lia].
- unfold iod_factsB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U20, UO.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I;
    first [lia | unfold SHADOW_OFF; lia | unfold TB_g_raw; lia | vm_compute; reflexivity].
Qed.

(* The close of one path of run B: the memory is the one it started from, the registers of IOD_KEEPB are kept. *)
Ltac iod_closeB HS HJ Em HK AG pc :=
  pmkst HS;
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx sg (transportb_text + pc) rgx mm mdx) Qx) end;
  rewrite Em in HJ |- *;
  apply HK;
  [ exact (regs_kept_of_st_ok_pi _ _ _ _ _ IOD_KEEPB HS AG ltac:(vm_compute; reflexivity))
  | idtac | idtac | exact HJ | idtac .. ].

Lemma iod_runB : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem3 md3 k
    (regs3 : bvmap 5 word) (sp graw ncm : Z) (frame Bw : list byte) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 k ->
  YK11.getr regs3 2 = w64 sp -> YK11.getr regs3 20 = w64 SHADOW_OFF ->
  YK11.getr regs3 21 = w64 (ios_kaz frame) ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= graw < 2 ^ 32 -> 0 <= ncm < 256 -> 0 <= ios_blen frame < 2 ^ 64 ->
  TW.g_raw (ios_B0 Bw) = bv_swrap 32 graw ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) TB_g_raw 4 graw ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) (sp + 49) 1 ncm ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) (sp + 64) 8 (ios_blen frame) ->
  (forall md4 (regs4 : bvmap 5 word),
     (forall r, In r IOD_KEEPB -> YK11.getr regs4 r = YK11.getr regs3 r) ->
     YK11.getr regs4 22 = w64 IOS_S6 -> YK11.getr regs4 18 = w64 ncm ->
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md4 k ->
     (TC.truth (TW.g_raw (ios_B0 Bw)) = true \/ ios_ka frame = true) ->
     SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs4 mem3 md4) Q) ->
  (forall md4 (regs4 : bvmap 5 word),
     (forall r, In r IOD_KEEPB -> YK11.getr regs4 r = YK11.getr regs3 r) ->
     YK11.getr regs4 22 = w64 IOS_S6 -> YK11.getr regs4 18 = w64 0 ->
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md4 k ->
     TC.truth (TW.g_raw (ios_B0 Bw)) = false -> ios_ka frame = false -> ios_blen frame = 0 ->
     SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs4 mem3 md4) Q) ->
  (forall md4 (regs4 : bvmap 5 word),
     (forall r, In r IOD_KEEPB -> YK11.getr regs4 r = YK11.getr regs3 r) ->
     YK11.getr regs4 22 = w64 IOS_S6 -> YK11.getr regs4 11 = w64 (ios_blen frame) ->
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md4 k ->
     TC.truth (TW.g_raw (ios_B0 Bw)) = false -> ios_ka frame = false -> ios_blen frame <> 0 ->
     SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_LOOP) regs4 mem3 md4) Q) ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOD_CIN_RET) regs3 mem3 md3) Q.
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 mem3 md3 k regs3 sp graw ncm frame Bw Q
  HL HJ R2 R20 R21 Hs1 Hs2 Hs16 Hgr Hnc Hbl HGR V0 V49 V64 HKn HKz HKl.
pose proof HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRFc & HCSFc & HAF & HLC & HCIR & HSW
  & HIN2 & HTO & HLF & HKD & HCLS & HLD & HAI1).
set (EB := iod_EB regs3 graw ncm (ios_blen frame)) in *.
assert (E32 : ew EB 32 = Z_to_bv 64 graw)
  by (unfold EB, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew EB 33 = Z_to_bv 64 ncm)
  by (unfold EB, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew EB 34 = Z_to_bv 64 (ios_blen frame))
  by (unfold EB, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (E21 : ew EB 21 = YK11.getr regs3 21) by (unfold EB, iod_EB; apply ew_Eimg_Ereg_nat; reflexivity).
assert (AGB : env_agree 32 (Ereg regs3 [Z_to_bv 64 graw; Z_to_bv 64 ncm; Z_to_bv 64 (ios_blen frame)]) EB)
  by (unfold EB, iod_EB; apply iod_agree).
destruct (iod_entryB W2 mem3 regs3 sp graw ncm (ios_blen frame) R2 R20 Hs1 Hs2 Hs16 Hgr Hnc Hbl V0 V49 V64)
  as [HS SHOK].
fold EB in HS, SHOK.
assert (HEI : img_env VAL A_LIM EB) by (unfold EB, iod_EB; apply Eimg_env).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx
    (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOD_CIN_RET)) mem3 (YK11.seg_rom segs)) md3) Qx) end.
assert (Hgrr : - 2 ^ 63 <= TW.g_raw (ios_B0 Bw) < 2 ^ 63).
{ pose proof (TWL.s32_range (ios_B0 Bw) TW.OFF_g_raw) as Hr. unfold TW.g_raw. lia. }
assert (EH57 : ew EB (A_HI 57) = Z_to_bv 64 IOS_S6).
{ unfold EB, iod_EB. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite (@ios_s6_val fx rc). reflexivity. }
assert (QS6 : forall (ssx : sstate) (Ex : env) (msx : machine_state),
  st_ok_pi segs VAL Ex ssx (restrict (w_H W2) msx) -> ew Ex (A_HI 57) = Z_to_bv 64 IOS_S6 ->
  sr_get (ss_regs ssx) 22 = SOff (A_HI 57) 0 -> YK11.getr (ms_regs msx) 22 = w64 IOS_S6).
{ intros ssx Ex msx HSx HEx Hget.
  refine (eq_trans (st_ok_pi_restrict_reg (w_H W2) Ex ssx msx 22 HSx) _). rewrite Hget.
  cbn [sv_denot]. rewrite HEx, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
(* 0x83180 - 0x83184: s6 = the %hi of g_raw, a0 = g_raw *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ iod_awrRO. }
rename ms into msa.
assert (Ema : ms_mem msa = mem3).
{ eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
all: lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  let E32x := fresh "E32x" in
  assert (E32x : ew Ex 32 = Z_to_bv 64 graw) by (rewrite ?ew_ewset_other by lia; exact E32);
  rewrite (iod_sext32_den Ex 32 graw E32x ltac:(lia)) in Hc end.
all: rewrite <- HGR in Hc.
all: cbn [branch_taken sv_denot] in Hc.
all: rewrite (iod_eqb0 (TW.g_raw (ios_B0 Bw)) Hgrr) in Hc.
all: change (negb (TW.g_raw (ios_B0 Bw) =? 0)) with (TC.truth (TW.g_raw (ios_B0 Bw))) in Hc.
all: set (md1 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
all: clearbody md1. all: clear mat.
- (* g_raw <> 0: s2 = f.ncmds *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1f80.
  { iod_awrRO. }
  rename ms into msb. assert (Emb : ms_mem msb = mem3).
  { rewrite <- Ema. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG. iod_closeB HS HJ Emb HKn AGB IOS_CMDS.
  + exact (QS6 _ _ _ HS EH57 ltac:(vm_compute; reflexivity)).
  + iod_rv HS. lazymatch goal with |- sv_denot ?Ex _ = _ =>
      let E33x := fresh "E33x" in
      assert (E33x : ew Ex 33 = Z_to_bv 64 ncm) by (rewrite ?ew_ewset_other by lia; exact E33);
      exact (iod_zext8_den Ex 33 ncm E33x ltac:(lia)) end.
  + left. exact Hc.
- (* g_raw = 0: the keepalive flag *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { iod_awrRO. }
  rename ms into msc. assert (Emc : ms_mem msc = mem3).
  { rewrite <- Ema. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  all: lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    let E21x := fresh "E21x" in
    assert (E21x : ew Ex 21 = w64 (ios_kaz frame))
      by (rewrite ?ew_ewset_other by lia; rewrite E21; exact R21);
    cbn [branch_taken sv_denot] in Hc0; rewrite E21x in Hc0 end.
  all: unfold w64 in Hc0. all: rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc0.
  all: rewrite (iod_eqb (ios_kaz frame) 0 ltac:(unfold ios_kaz; destruct (ios_ka frame); lia) ltac:(lia)) in Hc0.
  all: unfold ios_kaz in Hc0.
  + (* the keepalive flag is set: s2 = f.ncmds *)
    destruct (ios_ka frame) eqn:HKA; [|cbn in Hc0; discriminate Hc0].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1f80.
    { iod_awrRO. }
    rename ms into msd. assert (Emd : ms_mem msd = mem3).
    { rewrite <- Emc. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
    clear HF HFr HG. iod_closeB HS HJ Emd HKn AGB IOS_CMDS.
    * exact (QS6 _ _ _ HS EH57 ltac:(vm_compute; reflexivity)).
    * iod_rv HS. lazymatch goal with |- sv_denot ?Ex _ = _ =>
        let E33x := fresh "E33x" in
        assert (E33x : ew Ex 33 = Z_to_bv 64 ncm) by (rewrite ?ew_ewset_other by lia; exact E33);
        exact (iod_zext8_den Ex 33 ncm E33x ltac:(lia)) end.
    * right. reflexivity.
  + (* the keepalive flag is clear: the test of f.body_len *)
    destruct (ios_ka frame) eqn:HKA; [cbn in Hc0; discriminate Hc0|].
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { iod_awrRO. }
    rename ms into mse. assert (Eme : ms_mem mse = mem3).
    { rewrite <- Emc. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    all: lazymatch type of Hc1 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      let E34x := fresh "E34x" in
      assert (E34x : ew Ex 34 = Z_to_bv 64 (ios_blen frame))
        by (rewrite ?ew_ewset_other by lia; exact E34);
      cbn [branch_taken sv_denot] in Hc1; rewrite E34x in Hc1 end.
    all: rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc1.
    all: rewrite (iod_eqb (ios_blen frame) 0 ltac:(lia) ltac:(lia)) in Hc1.
    * (* body_len = 0: s2 = 0 *)
      apply Z.eqb_eq in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1f80.
      { iod_awrRO. }
      rename ms into msf. assert (Emf : ms_mem msf = mem3).
      { rewrite <- Eme. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
      clear HF HFr HG. iod_closeB HS HJ Emf HKz AGB IOS_CMDS.
      -- exact (QS6 _ _ _ HS EH57 ltac:(vm_compute; reflexivity)).
      -- iod_rv HS. change (sv_denot EB (SLit 0)) with (Z_to_bv 64 0). reflexivity.
      -- exact Hc.
      -- reflexivity.
      -- exact Hc1.
    * (* body_len <> 0: the command count loop, a1 = body_len *)
      apply Z.eqb_neq in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1ef8.
      { iod_awrRO. }
      rename ms into msg. assert (Emg : ms_mem msg = mem3).
      { rewrite <- Eme. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
      clear HF HFr HG. iod_closeB HS HJ Emg HKl AGB IOS_LOOP.
      -- exact (QS6 _ _ _ HS EH57 ltac:(vm_compute; reflexivity)).
      -- iod_rv HS. lazymatch goal with |- sv_denot ?Ex _ = _ =>
           let E34x := fresh "E34x" in
           assert (E34x : ew Ex 34 = Z_to_bv 64 (ios_blen frame))
             by (rewrite ?ew_ewset_other by lia; exact E34);
           cbn [sv_denot]; rewrite E34x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end.
      -- exact Hc.
      -- reflexivity.
      -- exact Hc1.
Qed.

(* ------------------------------------------------------------------ *)
(* The cut, rebuilt at the memory the stretch left                     *)
(* ------------------------------------------------------------------ *)

Lemma iod_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) mem3 md3 (regs3 : bvmap 5 word),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_STK <= a < spZ regs - IOSEND_FRAME + 8) ->
     aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall r, In r IOD_KEEPC -> YK11.getr regs3 r = YK11.getr regs2 r) ->
  YK11.getr regs3 21 = w64 (ios_kaz frame) ->
  YK11.getr regs3 22 = w64 IOS_S6 ->
  iod_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 regs3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2
  mem3 md3 regs3 HL HFX HAT HCSF HJ3 Hkp Hgr HRK R21 R22.
destruct HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRFc & HCSFc & HAF & HLC & HCIR & HSW
  & HIN2 & HTO & HLF & HKD & HCLS & HLD & HAI1).
pose proof HFX as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff
  & Hfat & Hfail & Hrom & Htw & Hinv1 & Hinv2 & Hnev).
unfold ios_at_csf, ios_e2_at in HAT.
destruct HAT as (HCUR & HSAV & HREG & HS811 & HSF & HSFsrc & HGARR & HSRC & HTW).
pose proof HCUR as (HJ2 & Hfrs & Hperm & Hmo & HKEPT).
destruct HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
destruct (iod_geo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX)
  as (HAR0 & Hce & Hlo2 & Hhi2 & H47 & Hsp0a & Hsp16').
pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _). rewrite !Z.add_0_r in HJ2i.
pose proof (proj1 HJ2i) as HAR2. clear HJ2i memS2.
pose proof HJ3 as (_ & _ & (memS3 & HJ3i & _) & _). rewrite !Z.add_0_r in HJ3i.
pose proof (proj1 HJ3i) as HAR3. clear HJ3i memS3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 160 + 4096 <= IOSEND_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EFO : IOS_F_OFF = 8) by reflexivity.
assert (ESF : SF_SIZE = 80) by reflexivity.
pose proof (ios_len60 (ios_B0 Bw) frame (ios_B0 Bw) HCSF) as HL60.
assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
(* the bytes the stretch changed: inside io_send's own stack window *)
assert (HZ : forall a, spZ regs - IOSEND_STK <= a < spZ regs - IOSEND_FRAME + 8 ->
  spZ regs - IOSEND_STK <= a < spZ regs) by lia.
(* the frame's bytes and the caller's frame shadows are untouched *)
assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
  aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha.
  assert (Hpp : 4096 <= p /\ p + Z.of_nat (length frame) <= 2 ^ 47).
  { destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p (Z.of_nat (length frame)) HAR0 Hsrc ltac:(lia))
      as [Hpl | Hpl]; lia. }
  apply Hkp; [lia|]. unfold decode_off_win in Hoff. lia. }
assert (KS : forall cid pos s, In (cid, pos) (frames S2) ->
  in_zr s (YG0f.shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8) ->
  aview segs (w_H W2) mem3 s = aview segs (w_H W2) mem2 s).
{ intros cid pos s Hin Hs'.
  destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr ly2 cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr ly2 cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs'. cbn [fst snd] in Hs'.
  unfold YG0f.shadow_addr, SHADOW_OFF in *.
  change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  apply Hkp; lia. }
(* the running facts *)
assert (HCUR3 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3).
{ exact (iod_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2
    mem3 md3 (fun a => spZ regs - IOSEND_STK <= a < spZ regs - IOSEND_FRAME + 8)
    LAWS HGX HFX HCUR HJ3 Hkp Hgr HZ). }
unfold iod_at, ios_at_csf, ios_e2_at.
split; [|split; [exact R21 | exact R22]].
split; [exact HCUR3|].
split.
{ apply (iod_saved_kept W2 mem2 mem3 regs); [|exact HSAV]. intros a Ha. apply Hkp; lia. }
split.
{ unfold ios_regs. repeat split.
  - rewrite <- R2. apply HRK. unfold IOD_KEEPC. cbn [In]. auto 20.
  - rewrite <- R3. apply HRK. unfold IOD_KEEPC. cbn [In]. auto 20.
  - rewrite <- R4. apply HRK. unfold IOD_KEEPC. cbn [In]. auto 20.
  - rewrite <- R8. apply HRK. unfold IOD_KEEPC. cbn [In]. auto 20.
  - rewrite <- R9. apply HRK. unfold IOD_KEEPC. cbn [In]. auto 20.
  - rewrite <- R19. apply HRK. unfold IOD_KEEPC. cbn [In]. auto 20.
  - rewrite <- R20. apply HRK. unfold IOD_KEEPC. cbn [In]. auto 20. }
split.
{ intros r Hr. rewrite <- (HS811 r Hr). apply HRK.
  assert (Er : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  unfold IOD_KEEPC. destruct Er as [Ea|[Eb|[Ec|Ed]]]; cbn [In].
  - rewrite Ea. do 7 right. left. apply bv_eq; reflexivity.
  - rewrite Eb. do 8 right. left. apply bv_eq; reflexivity.
  - rewrite Ec. do 9 right. left. apply bv_eq; reflexivity.
  - rewrite Ed. do 10 right. left. apply bv_eq; reflexivity. }
rewrite EFO in HSF, HSFsrc |- *.
assert (KW : forall a, spZ regs - IOSEND_FRAME + 8 <= a < spZ regs - IOSEND_FRAME + 8 + SF_SIZE ->
  aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply Hkp; lia).
split.
{ apply (iod_sframe_kept W2 mem2 mem3 _ p (TC.rf frame)); [|exact HSF].
  intros a Ha. apply Hkp; lia. }
split.
{ exact (trans_src_ok_kept B LAWS ly2 S2 W2 mem2 md2 ly2 S2 W2 mem3 md3
    (spZ regs - IOSEND_FRAME + 8) SF_SIZE HAR2 HAR3
    (Permutation_refl _) eq_refl (fun c q => eq_refl) eq_refl eq_refl KW KS HSFsrc ltac:(lia)). }
split.
{ apply (iod_garr8_kept _ mem2 mem3 p _); [exact HGARR|].
  intros a Ha. rewrite length_map in Ha. apply KF. lia. }
split.
{ exact (trans_src_ok_kept B LAWS ly2 S2 W2 mem2 md2 ly2 S2 W2 mem3 md3 p (Z.of_nat (length frame))
    HAR2 HAR3 (Permutation_refl _) eq_refl (fun c q => eq_refl) eq_refl eq_refl KF KS HSRC ltac:(lia)). }
apply (tw_kept TMAP_B _ _ _ HTW). intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply Hkp; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

Lemma iod_head : @iod_head_stmt fx rc B MT.
Proof.
unfold iod_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
  HL HFX HCSF HCMD HRET HCIN HAT HKn HKz HKl.
pose proof HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRFc & HCSFc & HAF & HLC & HCIR & HSW
  & HIN2 & HTO & HLF & HKD & HCLS & HLD & HAI1).
pose proof HFX as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff
  & Hfat & Hfail & Hrom & Htw & Hinv1 & Hinv2 & Hnev).
pose proof HAT as HATc.
unfold ios_at_csf, ios_e2_at in HATc.
pose proof HATc as (HCUR & HSAV & HREG & HS811 & HSF & HSFsrc & HGARR & HSRC & HTW).
pose proof HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof HCUR as (HJ2 & Hfrs & Hperm & Hmo & HKEPT).
destruct (iod_geo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX)
  as (HAR0 & Hce & Hlo2 & Hhi2 & H47 & Hsp0a & Hsp16').
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 160 + 4096 <= IOSEND_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EFO : IOS_F_OFF = 8) by reflexivity.
assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
pose proof (ios_len60 (ios_B0 Bw) frame (ios_B0 Bw) HCSF) as HL60.
pose proof (ios_sf_code (ios_B0 Bw) frame (ios_B0 Bw) HCSF) as HOK.
pose proof (eq_refl (spZ regs - IOSEND_FRAME)) as Esp.
set (graw := TW.u_at (ios_B0 Bw) TW.OFF_g_raw 4) in *.
assert (HGR : TW.g_raw (ios_B0 Bw) = bv_swrap 32 graw) by reflexivity.
pose proof (TWL.u_at_range (ios_B0 Bw) TW.OFF_g_raw 4) as Rgr.
change (8 * Z.of_nat 4) with 32 in Rgr.
assert (HWIN : iod_call_win STK sp0 (spZ regs - IOSEND_FRAME))
  by (split; [rewrite Zminus_mod, Hsp16, FF; reflexivity | split; lia]).
(* 0x83148 .. 0x8317c *)
apply (iod_runA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
  HL HFX HAT HCSF).
intros mem3 md3 regs3 HJ3 HK3 HG3 HRK3 R21' R1'.
(* the registers at the call *)
assert (Q2 : YK11.getr regs3 2 = w64 (spZ regs - IOSEND_FRAME)).
{ rewrite <- R2. apply HRK3. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (Q3 : YK11.getr regs3 3 = w64 (as_gp B)).
{ rewrite <- Hgp, <- R3. apply HRK3. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (Q4 : YK11.getr regs3 4 = w64 (as_tp B)).
{ rewrite <- Htp, <- R4. apply HRK3. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (Qra : YK0s.ret_ok (YK11.getr regs3 1)).
{ rewrite R1'. unfold IOD_CIN_RET, IOS_AT, AF_io_send.
  apply (@ret_ok_codeptr_v rc transportb_listing PI_transportb); [lia | reflexivity]. }
(* the world relation at the call memory *)
assert (HTW3 : tw_at TMAP_B (aview segs (w_H W2) mem3) (ios_B0 Bw)).
{ apply (tw_kept TMAP_B _ _ _ HTW). intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply HK3; lia. }
(* the leaf call *)
eapply SRr_bind.
{ exact (iod_call_cin STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem3 md3 (k + 0) regs3
    (spZ regs - IOSEND_FRAME) (ios_B0 Bw) HCELLS LAWS HIN2 HJ3 Q2 Qra Q3 Q4 HWIN HTW3 HCIN). }
intros W3 c3 _ (-> & rg4 & mem4 & md4 & -> & HJ4 & HP4 & _ & HK4 & HG4 & _).
change (YK11.getr regs3 (Z_to_bv 5 1)) with (YK11.getr regs3 1). rewrite R1'.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) _ =>
  change (SRr segs W2 (@cfg_at fx segs (transportb_text + IOD_CIN_RET) rgx mm mdx) Q) end.
assert (SP3 : spZ regs3 = spZ regs - IOSEND_FRAME)
  by (change (spZ regs3) with (bv_unsigned (YK11.getr regs3 2)); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* what the leaf and run A together left *)
assert (HK4a : forall a, 0 <= a < 2 ^ 64 ->
  ~ (spZ regs - IOSEND_STK <= a < spZ regs - IOSEND_FRAME + 8) ->
  aview segs (w_H W2) mem4 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  rewrite (HK4 a Ha ltac:(rewrite SP3; lia) ltac:(intros X; inversion X)).
  apply HK3; [exact Ha | lia]. }
assert (HG4a : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem4 a)
  by (intros a Ha; apply HG4; apply HG3; exact Ha).
(* the registers after the leaf *)
assert (R21'' : YK11.getr rg4 21 = w64 (ios_kaz frame))
  by (rewrite (iod_ap regs3 rg4 21 HP4 ltac:(iod_cs)); exact R21').
assert (HRK4 : forall r, In r IOD_KEEP -> YK11.getr rg4 r = YK11.getr regs3 r).
{ intros r Hr. apply (iod_ap regs3 rg4 r HP4).
  unfold IOD_KEEP in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [iod_cs |]); destruct Hr. }
assert (Q2' : YK11.getr rg4 2 = w64 (spZ regs - IOSEND_FRAME))
  by (rewrite (HRK4 (2%bv) ltac:(unfold IOD_KEEP; cbn [In]; auto 20)); exact Q2).
assert (Q20' : YK11.getr rg4 20 = w64 SHADOW_OFF).
{ rewrite (HRK4 (20%bv) ltac:(unfold IOD_KEEP; cbn [In]; auto 20)).
  rewrite (HRK3 (20%bv) ltac:(unfold IOD_KEEP; cbn [In]; auto 20)). exact R20. }
(* the struct and the world at the memory the leaf left *)
assert (HTW4 : tw_at TMAP_B (aview segs (w_H W2) mem4) (ios_B0 Bw)).
{ apply (tw_kept TMAP_B _ _ _ HTW). intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply HK4a; lia. }
assert (HSF4 : trans_sframe_at W2 mem4 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame)).
{ apply (iod_sframe_kept W2 mem2 mem4 _ p (TC.rf frame)); [|exact HSF].
  intros a Ha. apply HK4a; lia. }
rewrite EFO in HSF4.
pose proof HSF4 as (Hfp0 & Hfp8 & SB & HGsb & HLSB & F0 & F8 & F16 & F24 & F26 & F28 & F30 & F32 & F36 & F40 &
  F41 & F48 & F56 & F64 & F72).
assert (HSBl : Z.of_nat (length SB) = 80) by (rewrite HLSB; reflexivity).
pose proof (TWL.u_at_range SB 41 1) as R41. change (8 * Z.of_nat 1) with 8 in R41.
pose proof (TWL.u_at_range SB 56 8) as R56. change (8 * Z.of_nat 8) with 64 in R56.
assert (Rncm : 0 <= DSpec.sf_ncmds (TC.rf frame) < 256) by (rewrite <- F41; lia).
assert (Rblen : 0 <= ios_blen frame < 2 ^ 64) by (unfold ios_blen; rewrite <- F56; lia).
assert (V49 : YI04.val_mem segs (mrestrict (w_H W2) mem4) (spZ regs - IOSEND_FRAME + 49) 1
  (DSpec.sf_ncmds (TC.rf frame))).
{ replace (spZ regs - IOSEND_FRAME + 49) with (spZ regs - IOSEND_FRAME + 8 + 41) by lia.
  rewrite <- F41.
  apply (iod_val_at (mrestrict (w_H W2) mem4) (spZ regs - IOSEND_FRAME + 8) SB 41 1 HGsb); [lia | cbn; lia]. }
assert (V64 : YI04.val_mem segs (mrestrict (w_H W2) mem4) (spZ regs - IOSEND_FRAME + 64) 8 (ios_blen frame)).
{ replace (spZ regs - IOSEND_FRAME + 64) with (spZ regs - IOSEND_FRAME + 8 + 56) by lia.
  unfold ios_blen. rewrite <- F56.
  apply (iod_val_at (mrestrict (w_H W2) mem4) (spZ regs - IOSEND_FRAME + 8) SB 56 8 HGsb); [lia | cbn; lia]. }
assert (V0 : YI04.val_mem segs (mrestrict (w_H W2) mem4) TB_g_raw 4 graw).
{ pose proof (tw_read_val segs (mrestrict (w_H W2) mem4) TMAP_B (ios_B0 Bw) TW.OFF_g_raw TB_g_raw TW.SZ_g_raw
    0 4 TMAP_B_ok HTW4 TMAP_B_g_raw ltac:(lia) ltac:(unfold TW.SZ_g_raw; cbn; lia)) as Hv.
  rewrite Z.add_0_r in Hv. unfold graw. rewrite Z.add_0_r in Hv. exact Hv. }
(* the close of each exit *)
assert (HCL : forall mem5 md5 (regs5 : bvmap 5 word),
  mem5 = mem4 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem5 md5 (k + 0) ->
  (forall r, In r IOD_KEEPB -> YK11.getr regs5 r = YK11.getr rg4 r) ->
  YK11.getr regs5 22 = w64 IOS_S6 ->
  iod_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem5 md5 regs5).
{ intros mem5 md5 regs5 Hm5 HJ5 HRK5 R22'. subst mem5.
  apply (iod_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2
    regs2 mem4 md5 regs5 HL HFX HAT HCSF HJ5 HK4a HG4a); [| | exact R22'].
  - intros r Hr.
    assert (HinB : In r IOD_KEEPB)
      by (unfold IOD_KEEPC in Hr; unfold IOD_KEEPB; cbn [In] in Hr |- *;
          repeat (destruct Hr as [<- | Hr]; [auto 20 |]); destruct Hr).
    assert (HinA : In r IOD_KEEP)
      by (unfold IOD_KEEPC in Hr; unfold IOD_KEEP; cbn [In] in Hr |- *;
          repeat (destruct Hr as [<- | Hr]; [auto 20 |]); destruct Hr).
    rewrite (HRK5 r HinB), (HRK4 r HinA). exact (HRK3 r HinA).
  - rewrite (HRK5 (21%bv) ltac:(unfold IOD_KEEPB; cbn [In]; auto 20)). exact R21''. }
(* 0x83180 .. the exits *)
apply (iod_runB STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem4 md4 (k + 0) rg4
  (spZ regs - IOSEND_FRAME) graw (DSpec.sf_ncmds (TC.rf frame)) frame Bw Q
  HL HJ4 Q2' Q20' R21'' ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hsp16, FF; reflexivity)
  ltac:(lia) Rncm Rblen HGR V0 V49 V64).
- intros md5 regs5 HRK5 R22' R18' HJ5 Hcase.
  apply (HKn mem4 md5 regs5 (HCL mem4 md5 regs5 eq_refl HJ5 HRK5 R22')); [|exact Hcase].
  exact R18'.
- intros md5 regs5 HRK5 R22' R18' HJ5 Ht Hk Hb0.
  apply (HKz mem4 md5 regs5 (HCL mem4 md5 regs5 eq_refl HJ5 HRK5 R22'));
    [exact R18' | exact Ht | exact Hk | exact Hb0].
- intros md5 regs5 HRK5 R22' R11' HJ5 Ht Hk Hb0.
  apply (HKl mem4 md5 regs5 (HCL mem4 md5 regs5 eq_refl HJ5 HRK5 R22'));
    [exact R11' | exact Ht | exact Hk | exact Hb0].
Qed.

End dataw.
