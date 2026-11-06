(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 2309 of its 2385 lines of code are new or changed and 689 lines of the source are left out. *)
(* lc_op4st_ok (LLVMFuzzerTestOneInput_segs.v:1085): op 4's segment OP4ST of the image-A walk, from the cut CMDW
   (+0x119c, the return of check_latest_submit) to the cut S4 (+0x12c8, `li a0, 0` before the call of settle).
   The code (LLVMFuzzerTestOneInput_cg.v :187-192, A.s +0x119c .. +0x12c8):
     +0x119c .. +0x11a0  s4 = 160(s1) (g_fail_next's page), `bnez s6` on want;                            run 1
     want <> 0 (+0x12ac): the plain load of g_ncmd, g_ncmd + 1, s3 / s7 the cursor, `j` to S4;             run A
     want = 0 (+0x11a4 ..): the four checked stores of g_cmd[serial]'s st = PENDING, key, display (4 bytes
                       each) and len (1 byte), then a0 = g_cmd[serial] + 12, a1 = c, a2 = len,
                       `jal __asan_memcpy`;                                                                run B1
     +0x1218           __asan_memcpy (g_cmd[serial].bytes, c, len) by TransportGCg.v gx_intrin_at (the premise
                       lp_memcpy): the destination is g_cmd's payload (its zero shadow, settle_cg.v
                       trans_settle_cells), the source is c in the own frame (its shadow bytes 4 .. 6 are 0
                       while c is in scope, o4_c_src);
     +0x121c .. +0x1220  `sext.w a0, s3; bltz a0` on at;                                                   run C
     at < 0 (the append, +0x1224 ..): g_nq + 1, a0 = g_q + 4 (old g_nq), the checked store of the serial
                       there, g_ncmd + 1, s3 / s7;                                                   runs P1, P2
     at >= 0 (the replace, +0x1228 ..): a0 = g_q + 4 at, the checked load of g_q[at], a1 = g_cmd + 40 g_q[at],
                       the checked store of REPLACED there, the plain store of the serial into g_q[at],
                       g_ncmd + 1, s3 / s7.                                                     runs R1, R2, R3
   Each run is a position-abstract symbolic run of lib/A/Prog/PaShadow.v over the walk's G journal
   (TransportGRunA.v paj_run_x / paj_run_to_x), in the idiom of diginet_session_submit_seg_app.v. The three
   addresses the engine cannot resolve by itself (g_q + 4 at, g_q + 4 g_nq, g_cmd + 40 g_q[at]) become fresh
   atoms by o4_gen, each with its own region, range fact and shadow entry (o4_she). The world is carried by
   the lemmas of this file's model section (o4_w_cmd / o4_w_rep / o4_w_app / o4_w_ncmd over TWorldG.v), the
   model by o4_model (LLVMFuzzerTestOneInput_st.v lc_op4_eq, lc_submit_tag_eq), and the loop's facts by
   LLVMFuzzerTestOneInput_st.v lc_core_kept (o4_kept3, o4_close, o4_closeG). The journal is never unfolded:
   it is the cut's, at FP = []. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP09 YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_seg_world settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The model's worlds of the segment (TOps.v op_submit_m :258-273)     *)
(* ------------------------------------------------------------------ *)

(* g_cmd[s] filled when want = SPEC_OK (:260-263): st, key, display, len, the first len bytes of cb. *)
Definition o4_cmdw (B5 : list byte) (s key disp len : Z) (cb : list byte) : list byte :=
  TW.set_Cmd_bytes
    (TW.set_Cmd_len (TW.set_Cmd_display (TW.set_Cmd_key (TW.set_Cmd_st B5 s TC.PENDING) s key) s disp) s len)
    s (firstn (Z.to_nat len) cb).
(* B6 (:258-272): the replace (at >= 0) or the append (at < 0) from Bw when want = SPEC_OK, else B5. *)
Definition o4_b6 (B5 Bw : list byte) (want at_ s : Z) : list byte :=
  if want =? DSpec.SPEC_OK then
    if 0 <=? at_ then TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s
    else TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32)
  else B5.
(* B7 (:273): g_ncmd + 1. *)
Definition o4_b7 (B6 : list byte) : list byte := TW.set_g_ncmd B6 ((TW.g_ncmd B6 + 1) mod 2 ^ 32).
(* ------------------------------------------------------------------ *)
(* World helpers                                                       *)
(* ------------------------------------------------------------------ *)

Lemma o4w_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l i d Hi; [lia|].
destruct l as [|x l]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|].
cbn [firstn nth]. apply IH. lia.
Qed.

Lemma o4w_le4_mod : forall v j, YO0f.le_byte (v mod 2 ^ 32) 4 j = YO0f.le_byte v 4 j.
Proof.
intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma o4w_len : forall (B v : list byte) k, length B = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> length (TW.upd B k v) = Z.to_nat TW.W_LEN.
Proof. intros B v k HL Hk Hv. rewrite TWL.length_upd; [exact HL | exact Hk | rewrite HL; lia]. Qed.

Lemma o4w_u_out : forall (B v : list byte) k k' m, length B = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> 0 <= k' -> (k' + Z.of_nat m <= k \/ k + Z.of_nat (length v) <= k') ->
  TW.u_at (TW.upd B k v) k' m = TW.u_at B k' m.
Proof.
intros B v k k' m HL Hk Hv Hk' Hd. apply TWL.u_at_upd_out; [exact Hk | exact Hk' | exact Hd | rewrite HL; lia].
Qed.

(* The length of a world after stores inside it. *)
Ltac o4w_lenW HL :=
  lazymatch goal with
  | |- length (TW.upd _ _ _) = _ => apply o4w_len; [o4w_lenW HL | lia | rewrite ?TWL.length_put; lia]
  | |- _ => exact HL
  end.

(* u_at of a world after stores outside the read span. *)
Ltac o4w_uout HL :=
  repeat (rewrite o4w_u_out;
    [| o4w_lenW HL | lia | rewrite ?TWL.length_put; lia | lia
     | first [left; rewrite ?TWL.length_put; lia | right; rewrite ?TWL.length_put; lia]]).

(* ------------------------------------------------------------------ *)
(* The world lemmas                                                    *)
(* ------------------------------------------------------------------ *)

(* g_cmd[s]'s st, key, display (4 bytes each), len (1 byte) and the first len bytes of cb at s + 12. *)
Lemma o4_w_cmd : forall (B5 : list byte) (rd0 rdF : Z -> option Z) (s key disp len : Z) (cb : list byte),
  tw_at TMAP_A rd0 B5 -> 0 <= s < 1024 -> 0 <= len <= 24 -> length cb = 24%nat ->
  (forall j, (j < 4)%nat -> rdF (TA_g_cmd + 40 * s + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_g_cmd + 40 * s + 4 + Z.of_nat j) = Some (YO0f.le_byte key 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_g_cmd + 40 * s + 8 + Z.of_nat j) = Some (YO0f.le_byte disp 4 j)) ->
  rdF (TA_g_cmd + 40 * s + 36) = Some (YO0f.le_byte len 1 0) ->
  (forall i, 0 <= i < len ->
     rdF (TA_g_cmd + 40 * s + 12 + i) = Some (bv_unsigned (nth (Z.to_nat i) cb (Z_to_bv 8 0)))) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_cmd + 40 * s <= x < TA_g_cmd + 40 * s + 12 + len) ->
     x <> TA_g_cmd + 40 * s + 36 -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (o4_cmdw B5 s key disp len cb).
Proof.
intros B5 rd0 rdF s key disp len cb Htw Hs Hlen Hcb Vst Vkey Vdisp Vlen Vcb Hk.
assert (SC : TW.SZ_g_cmd = 40960) by reflexivity.
assert (HLs : length (firstn (Z.to_nat len) cb) = Z.to_nat len) by (apply firstn_length_le; lia).
assert (HP : TC.PENDING = 1) by reflexivity.
unfold o4_cmdw, TW.set_Cmd_bytes, TW.set_Cmd_len, TW.set_Cmd_display, TW.set_Cmd_key, TW.set_Cmd_st,
  TW.A_Cmd_bytes, TW.A_Cmd_len, TW.A_Cmd_display, TW.A_Cmd_key, TW.A_Cmd_st.
rewrite HP.
pose proof (ios_tw_start rdF rd0 B5 Htw) as H0.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s) (TW.OFF_g_cmd + 40 * s + 0) 4 1
  H0 TMAP_A_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Vst) as H1.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s + 4) (TW.OFF_g_cmd + 40 * s + 4) 4
  key H1 TMAP_A_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; replace (TA_g_cmd + (40 * s + 4) + Z.of_nat j) with (TA_g_cmd + 40 * s + 4 + Z.of_nat j)
          by lia; exact (Vkey j Hj))) as H2.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s + 8) (TW.OFF_g_cmd + 40 * s + 8) 4
  disp H2 TMAP_A_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; replace (TA_g_cmd + (40 * s + 8) + Z.of_nat j) with (TA_g_cmd + 40 * s + 8 + Z.of_nat j)
          by lia; exact (Vdisp j Hj))) as H3.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s + 36) (TW.OFF_g_cmd + 40 * s + 36) 1
  len H3 TMAP_A_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; assert (Hj0 : j = 0%nat) by lia; subst j;
        replace (TA_g_cmd + (40 * s + 36) + Z.of_nat 0) with (TA_g_cmd + 40 * s + 36) by lia; exact Vlen)) as H4.
pose proof (ios_tw_fill rdF rd0 _ _ TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s + 12) (TW.OFF_g_cmd + 40 * s + 12)
  (firstn (Z.to_nat len) cb) H4 TMAP_A_g_cmd ltac:(lia) ltac:(lia) ltac:(rewrite HLs; lia)
  ltac:(rewrite HLs; intros i Hi; rewrite o4w_nth_firstn by lia;
        replace (TA_g_cmd + (40 * s + 12) + i) with (TA_g_cmd + 40 * s + 12 + i) by lia; apply Vcb; lia)) as H5.
rewrite HLs in H5. rewrite Z2Nat.id in H5 by lia.
apply (ios_tw_end rdF rd0 _ _ H5).
intros x Hx HP5. ios_unP HP5. apply Hk; [exact Hx | lia | lia].
Qed.

(* g_ncmd + 1 alone (want <> SPEC_OK). *)
Lemma o4_w_ncmd : forall (B6 : list byte) (rd0 rdF : Z -> option Z),
  tw_at TMAP_A rd0 B6 ->
  (forall j, (j < 4)%nat -> rdF (TA_g_ncmd + Z.of_nat j) = Some (YO0f.le_byte (TW.g_ncmd B6 + 1) 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_ncmd <= x < TA_g_ncmd + 4) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (o4_b7 B6).
Proof.
intros B6 rd0 rdF Htw Vn Hk.
assert (SN : TW.SZ_g_ncmd = 4) by reflexivity.
unfold o4_b7, TW.set_g_ncmd.
pose proof (ios_tw_start rdF rd0 B6 Htw) as H0.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 TW.OFF_g_ncmd 4
  ((TW.g_ncmd B6 + 1) mod 2 ^ 32) H0 TMAP_A_g_ncmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TA_g_ncmd + 0 + Z.of_nat j) with (TA_g_ncmd + Z.of_nat j) by lia; exact (Vn j Hj))) as H1.
apply (ios_tw_end rdF rd0 _ _ H1).
intros x Hx HP. ios_unP HP. apply Hk; [exact Hx | lia].
Qed.

(* The replace: g_cmd[q].st = 3 (q = g_q[at]), g_q[at] = s, then g_ncmd + 1. *)
Lemma o4_w_rep : forall (Bw : list byte) (rd0 rdF : Z -> option Z) (at_ s : Z),
  tw_at TMAP_A rd0 Bw -> 0 <= at_ < 1024 -> 0 <= TW.Q_at Bw at_ < 1024 ->
  (forall j, (j < 4)%nat ->
     rdF (TA_g_cmd + 40 * TW.Q_at Bw at_ + Z.of_nat j) = Some (YO0f.le_byte 3 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_g_q + 4 * at_ + Z.of_nat j) = Some (YO0f.le_byte s 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_g_ncmd + Z.of_nat j) = Some (YO0f.le_byte (TW.g_ncmd Bw + 1) 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_cmd + 40 * TW.Q_at Bw at_ <= x < TA_g_cmd + 40 * TW.Q_at Bw at_ + 4) ->
     ~ (TA_g_q + 4 * at_ <= x < TA_g_q + 4 * at_ + 4) -> ~ (TA_g_ncmd <= x < TA_g_ncmd + 4) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (o4_b7 (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s)).
Proof.
intros Bw rd0 rdF at_ s Htw Hat Hq Vst Vq Vn Hk.
pose proof (tw_len TMAP_A rd0 Bw Htw) as HL.
assert (EW : TW.W_LEN = 65616) by reflexivity. assert (EC : TW.OFF_g_cmd = 19912) by reflexivity.
assert (EQ : TW.OFF_g_q = 60872) by reflexivity. assert (EM : TW.OFF_g_ncmd = 64984) by reflexivity.
assert (SC : TW.SZ_g_cmd = 40960) by reflexivity. assert (SQ : TW.SZ_g_q = 4096) by reflexivity.
assert (SN : TW.SZ_g_ncmd = 4) by reflexivity.
assert (HR : TC.REPLACED = 3) by reflexivity.
assert (EN6 : TW.g_ncmd (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s) = TW.g_ncmd Bw).
{ unfold TW.g_ncmd, TW.set_Q_at, TW.set_Cmd_st, TW.A_Cmd_st. o4w_uout HL. reflexivity. }
unfold o4_b7. rewrite EN6. rewrite HR.
unfold TW.set_g_ncmd, TW.set_Q_at, TW.set_Cmd_st, TW.A_Cmd_st.
pose proof (ios_tw_start rdF rd0 Bw Htw) as H0.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * TW.Q_at Bw at_)
  (TW.OFF_g_cmd + 40 * TW.Q_at Bw at_ + 0) 4 3 H0 TMAP_A_g_cmd ltac:(lia) ltac:(lia)
  ltac:(cbn [Z.of_nat]; lia) Vst) as H1.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * at_) (TW.OFF_g_q + 4 * at_) 4 s H1
  TMAP_A_g_q ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Vq) as H2.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 TW.OFF_g_ncmd 4
  ((TW.g_ncmd Bw + 1) mod 2 ^ 32) H2 TMAP_A_g_ncmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TA_g_ncmd + 0 + Z.of_nat j) with (TA_g_ncmd + Z.of_nat j) by lia; exact (Vn j Hj))) as H3.
apply (ios_tw_end rdF rd0 _ _ H3).
intros x Hx HP. ios_unP HP. apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* The append: g_nq + 1, g_q[old g_nq] = s, then g_ncmd + 1. *)
Lemma o4_w_app : forall (Bw : list byte) (rd0 rdF : Z -> option Z) (s : Z),
  tw_at TMAP_A rd0 Bw -> 0 <= TW.g_nq Bw < 1024 ->
  (forall j, (j < 4)%nat -> rdF (TA_g_nq + Z.of_nat j) = Some (YO0f.le_byte (TW.g_nq Bw + 1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_g_q + 4 * TW.g_nq Bw + Z.of_nat j) = Some (YO0f.le_byte s 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_g_ncmd + Z.of_nat j) = Some (YO0f.le_byte (TW.g_ncmd Bw + 1) 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_nq <= x < TA_g_nq + 4) ->
     ~ (TA_g_q + 4 * TW.g_nq Bw <= x < TA_g_q + 4 * TW.g_nq Bw + 4) -> ~ (TA_g_ncmd <= x < TA_g_ncmd + 4) ->
     rdF x = rd0 x) ->
  tw_at TMAP_A rdF (o4_b7 (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32))).
Proof.
intros Bw rd0 rdF s Htw Hnq Vnq Vq Vn Hk.
pose proof (tw_len TMAP_A rd0 Bw Htw) as HL.
assert (EW : TW.W_LEN = 65616) by reflexivity. assert (EQ : TW.OFF_g_q = 60872) by reflexivity.
assert (EN : TW.OFF_g_nq = 64980) by reflexivity. assert (EM : TW.OFF_g_ncmd = 64984) by reflexivity.
assert (SQ : TW.SZ_g_q = 4096) by reflexivity. assert (SNQ : TW.SZ_g_nq = 4) by reflexivity.
assert (SN : TW.SZ_g_ncmd = 4) by reflexivity.
assert (EN6 : TW.g_ncmd (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32)) =
  TW.g_ncmd Bw).
{ unfold TW.g_ncmd, TW.set_g_nq, TW.set_Q_at. o4w_uout HL. reflexivity. }
unfold o4_b7. rewrite EN6.
unfold TW.set_g_ncmd, TW.set_g_nq, TW.set_Q_at.
pose proof (ios_tw_start rdF rd0 Bw Htw) as H0.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * TW.g_nq Bw) (TW.OFF_g_q + 4 * TW.g_nq Bw) 4 s
  H0 TMAP_A_g_q ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Vq) as H1.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 TW.OFF_g_nq 4
  ((TW.g_nq Bw + 1) mod 2 ^ 32) H1 TMAP_A_g_nq ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TA_g_nq + 0 + Z.of_nat j) with (TA_g_nq + Z.of_nat j) by lia; exact (Vnq j Hj))) as H2.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 TW.OFF_g_ncmd 4
  ((TW.g_ncmd Bw + 1) mod 2 ^ 32) H2 TMAP_A_g_ncmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TA_g_ncmd + 0 + Z.of_nat j) with (TA_g_ncmd + Z.of_nat j) by lia; exact (Vn j Hj))) as H3.
apply (ios_tw_end rdF rd0 _ _ H3).
intros x Hx HP. ios_unP HP. apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* o4_cmdw writes only g_cmd[s]: g_nq and g_ncmd keep their values. *)
Lemma o4_cmdw_keep : forall (B5 : list byte) (s key disp len : Z) (cb : list byte),
  length B5 = Z.to_nat TW.W_LEN -> 0 <= s < 1024 -> 0 <= len <= 24 -> length cb = 24%nat ->
  TW.g_nq (o4_cmdw B5 s key disp len cb) = TW.g_nq B5 /\ TW.g_ncmd (o4_cmdw B5 s key disp len cb) = TW.g_ncmd B5.
Proof.
intros B5 s key disp len cb HL Hs Hlen Hcb.
assert (HLs : length (firstn (Z.to_nat len) cb) = Z.to_nat len) by (apply firstn_length_le; lia).
assert (EW : TW.W_LEN = 65616) by reflexivity. assert (EC : TW.OFF_g_cmd = 19912) by reflexivity.
assert (EN : TW.OFF_g_nq = 64980) by reflexivity. assert (EM : TW.OFF_g_ncmd = 64984) by reflexivity.
unfold o4_cmdw, TW.g_nq, TW.g_ncmd, TW.set_Cmd_bytes, TW.set_Cmd_len, TW.set_Cmd_display, TW.set_Cmd_key,
  TW.set_Cmd_st, TW.A_Cmd_bytes, TW.A_Cmd_len, TW.A_Cmd_display, TW.A_Cmd_key, TW.A_Cmd_st.
o4w_uout HL. split; reflexivity.
Qed.


(* ------------------------------------------------------------------ *)
(* The model lemmas of the segment                                     *)
(* ------------------------------------------------------------------ *)

(* The cursor after the op byte, and after the key and display bytes, stays in range (QueueFacts.v fuzz_u8_ok). *)
Lemma o4m_oc_ok : forall (D : list byte) (c : TOP.fuzz_in), QF.fuzz_in_ok D c -> QF.fuzz_in_ok D (lc_oc D c).
Proof.
intros D c Hc. destruct (QF.fuzz_u8_ok D c Hc) as (c1 & v & E & Hc1 & _).
unfold lc_oc. rewrite E. exact Hc1.
Qed.

Lemma o4m_kd_ok : forall (D : list byte) (c1 : TOP.fuzz_in),
  QF.fuzz_in_ok D c1 -> QF.fuzz_in_ok D (sv_c (lc_sub_kd D c1)).
Proof.
intros D c1 Hc1. unfold lc_sub_kd.
destruct (QF.fuzz_u8_ok D c1 Hc1) as (c1' & kb & E1 & Hc1' & _). rewrite E1. cbv beta iota zeta.
destruct (QF.fuzz_u8_ok D c1' Hc1') as (c2 & ab & E2 & Hc2 & _). rewrite E2. cbv beta iota zeta.
destruct (QF.fuzz_u8_ok D c2 Hc2) as (c3 & db & E3 & Hc3 & _). rewrite E3. cbv beta iota zeta.
cbn [sv_c]. exact Hc3.
Qed.

(* lc_tag_vals from a cursor in range: len, the 24 bytes of c, the take's length and the cursors around it. *)
Lemma o4m_tag : forall (D B1 : list byte) (c3 : TOP.fuzz_in),
  QF.fuzz_in_ok D c3 ->
  let tv := lc_tag_vals D B1 c3 in
  3 <= tg_len tv <= 24 /\ length (tg_cbytes tv) = 24%nat /\ 0 <= tg_n tv <= tg_len tv - 3 /\
  0 <= TOP.fi_off (tg_c4 tv) /\ 0 <= TOP.fi_n (tg_c4 tv) /\ tg_n tv <= TOP.fi_n (tg_c4 tv) /\
  TOP.fi_off (tg_c tv) = TOP.fi_off (tg_c4 tv) + tg_n tv /\
  TOP.fi_n (tg_c tv) = TOP.fi_n (tg_c4 tv) - tg_n tv.
Proof.
intros D B1 c3 Hc3. cbv zeta. unfold lc_tag_vals.
destruct (QF.fuzz_u8_ok D c3 Hc3) as (c4 & lb & E4 & (H0 & H1 & H2) & Hlb). rewrite E4.
cbv beta iota zeta. unfold TOP.fuzz_take_m. cbv beta iota zeta.
cbn [tg_len tg_cbytes tg_n tg_c4 tg_c TOP.fi_off TOP.fi_n].
pose proof (Z.mod_pos_bound lb 22 ltac:(lia)) as Hm.
destruct (Z.ltb_spec (lb mod 22 + 3 - 3) (TOP.fi_n c4)) as [Hlt|Hge]; cbv beta iota;
  (split; [lia|]);
  (split; [rewrite !length_app, repeat_length, QF.length_sub_D by lia; cbn [length]; lia|]);
  repeat split; lia.
Qed.

(* The bytes and the cursor of the tagged mode. *)
Lemma o4_tag_facts : forall (D B1 : list byte) (c0 : TOP.fuzz_in),
  QF.fuzz_in_ok D c0 ->
  let tv := lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0))) in
  3 <= tg_len tv <= 24 /\ length (tg_cbytes tv) = 24%nat /\ 0 <= tg_n tv <= tg_len tv - 3 /\
  0 <= TOP.fi_off (tg_c4 tv) /\ 0 <= TOP.fi_n (tg_c4 tv) /\ tg_n tv <= TOP.fi_n (tg_c4 tv) /\
  TOP.fi_off (tg_c tv) = TOP.fi_off (tg_c4 tv) + tg_n tv /\
  TOP.fi_n (tg_c tv) = TOP.fi_n (tg_c4 tv) - tg_n tv.
Proof.
intros D B1 c0 Hc0.
exact (o4m_tag D B1 _ (o4m_kd_ok D _ (o4m_oc_ok D c0 Hc0))).
Qed.

(* Z.lor of two u32 values is a u32. *)
Lemma o4m_lor32 : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= Z.lor x y < 2 ^ 32.
Proof.
intros x y Hx Hy.
assert (H0 : 0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
split; [exact H0|].
destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [rewrite E; lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lor x y) 32 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec x 0) as [E0|E0].
  + rewrite E0. change (Z.log2 0) with 0. lia.
  + apply (proj1 (Z.log2_lt_pow2 x 32 ltac:(lia))). lia.
- destruct (Z.eq_dec y 0) as [E0|E0].
  + rewrite E0. change (Z.log2 0) with 0. lia.
  + apply (proj1 (Z.log2_lt_pow2 y 32 ltac:(lia))). lia.
Qed.

(* The key and display bytes. *)
Lemma o4_kd_facts : forall (D : list byte) (c1 : TOP.fuzz_in),
  0 <= sv_key (lc_sub_kd D c1) < 2 ^ 32 /\ (sv_display (lc_sub_kd D c1) = 0 \/ sv_display (lc_sub_kd D c1) = 1).
Proof.
intros D c1. unfold lc_sub_kd.
destruct (TOP.fuzz_u8_m D c1) as [c1' kb].
destruct (TOP.fuzz_u8_m D c1') as [c2 ab].
destruct (TOP.fuzz_u8_m D c2) as [c3 db].
cbv zeta. cbn [sv_key sv_display].
split.
- unfold DSpec.KEY. apply o4m_lor32.
  + pose proof (Z.mod_pos_bound kb 9 ltac:(lia)). lia.
  + change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound ab (2 ^ 16) ltac:(lia)). lia.
- assert (E : Z.land db 1 = db mod 2).
  { change (Z.land db 1) with (Z.land db (Z.ones 1)). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound db 2 ltac:(lia)) as Hm.
  destruct (Z.eq_dec (db mod 2) 0) as [E0|E0]; [left; exact E0|right; lia].
Qed.

(* submit_find_at answers -1 or an index below CMDS_MAX. *)
Lemma o4m_find_range : forall (fuel : nat) (B : list byte) (key i r : Z),
  0 <= i -> TOP.submit_find_at fuel B key i = Some r -> r = -1 \/ 0 <= r < TC.CMDS_MAX.
Proof.
induction fuel as [|f IH]; intros B key i r Hi H; cbn [TOP.submit_find_at] in H; [discriminate H|].
destruct (i <? TW.g_nq B).
- destruct (TC.CMDS_MAX <=? i) eqn:E1; [discriminate H|].
  destruct (TC.CMDS_MAX <=? TW.Q_at B i); [discriminate H|].
  destruct (TW.Cmd_key B (TW.Q_at B i) =? key); cbv beta iota in H.
  + right. apply Z.leb_gt in E1. injection H as E. subst r. lia.
  + exact (IH B key (i + 1) r ltac:(lia) H).
- left. cbv beta iota in H. injection H as E. subst r. reflexivity.
Qed.

(* at is -1 or an index below CMDS_MAX. *)
Lemma o4_at_range : forall (tv : ltg) (key at_ : Z), lc_at tv key = Some at_ -> at_ = -1 \/ 0 <= at_ < TC.CMDS_MAX.
Proof.
intros tv key at_ H. unfold lc_at in H.
destruct (negb (TC.h_coalescable_m key =? 0)); cbv beta iota in H.
- exact (o4m_find_range _ _ _ 0 at_ (Z.le_refl 0) H).
- left. injection H as E. subst at_. reflexivity.
Qed.

(* want is one of three codes. *)
Lemma o4_want_cases : forall (tv : ltg) (at_ : Z),
  lc_want tv at_ = DSpec.SPEC_OK \/ lc_want tv at_ = DSpec.SPEC_E_REFUSED \/ lc_want tv at_ = DSpec.SPEC_E_SPACE.
Proof.
intros tv at_. unfold lc_want.
destruct (lc_sys tv); [right; left; reflexivity|].
destruct ((at_ <? 0) && (TW.g_nq (tg_B2 tv) =? TC.QUEUE_MAX)); [right; right; reflexivity|left; reflexivity].
Qed.

(* The end of op_submit's tagged mode (TOps.v :274-275) under op 4's match (:311-312): a Some answer is settle's
   Some at B7, which keeps B7 (LLVMFuzzerTestOneInput_st.v lc_settle_world). *)
Lemma o4m_settle_tail : forall (Y : list byte) (cn : TOP.fuzz_in) (k : nat) (B' : list byte) (c' : TOP.fuzz_in)
    (k' : nat),
  match
    match TC.settle_m Y 0 with
    | None => None
    | Some (B8, _) => Some (B8, cn)
    end
  with
  | Some (B1, c2) => Some (B1, (c2, k))
  | None => None
  end = Some (B', (c', k')) ->
  TC.settle_m Y 0 = Some (Y, tt) /\ B' = Y /\ c' = cn /\ k' = k.
Proof.
intros Y cn k B' c' k' E.
destruct (TC.settle_m Y 0) as [[B8 u]|] eqn:Es; [|discriminate E].
pose proof (lc_settle_world Y B8 0 u Es) as EB. subst B8. destruct u.
cbv beta iota in E.
destruct (lc_some3 _ Y B' cn c' k k' eq_refl E) as (E1 & E2 & E3).
split; [first [exact Es | reflexivity]|].
split; [symmetry; exact E1|]. split; [symmetry; exact E2|]. symmetry; exact E3.
Qed.

(* The stores of g_cmd[serial] and of the queue (TOps.v :258-272), g_ncmd + 1 and settle (:273-275): a Some answer
   fixes the replace / append bounds, the world B7 and the cursor. *)
Lemma o4m_tail : forall (B5 : list byte) (s key disp len : Z) (cb : list byte) (want at_ : Z)
    (cn : TOP.fuzz_in) (k : nat) (B' : list byte) (c' : TOP.fuzz_in) (k' : nat),
  match
    match
      (if want =? DSpec.SPEC_OK then
         if 0 <=? at_ then
           if TC.CMDS_MAX <=? TW.Q_at (o4_cmdw B5 s key disp len cb) at_ then None
           else Some (TW.set_Q_at (TW.set_Cmd_st (o4_cmdw B5 s key disp len cb)
                                     (TW.Q_at (o4_cmdw B5 s key disp len cb) at_) TC.REPLACED) at_ s)
         else
           if TC.CMDS_MAX <=? TW.g_nq (o4_cmdw B5 s key disp len cb) then None
           else Some (TW.set_g_nq (TW.set_Q_at (o4_cmdw B5 s key disp len cb)
                                     (TW.g_nq (o4_cmdw B5 s key disp len cb)) s)
                        ((TW.g_nq (o4_cmdw B5 s key disp len cb) + 1) mod 2 ^ 32))
       else Some B5)
    with
    | None => None
    | Some B6 =>
        match TC.settle_m (TW.set_g_ncmd B6 ((TW.g_ncmd B6 + 1) mod 2 ^ 32)) 0 with
        | None => None
        | Some (B8, _) => Some (B8, cn)
        end
    end
  with
  | Some (B1, c2) => Some (B1, (c2, k))
  | None => None
  end = Some (B', (c', k')) ->
  (want = DSpec.SPEC_OK -> 0 <= at_ -> TW.Q_at (o4_cmdw B5 s key disp len cb) at_ < TC.CMDS_MAX) /\
  (want = DSpec.SPEC_OK -> at_ < 0 -> TW.g_nq (o4_cmdw B5 s key disp len cb) < TC.CMDS_MAX) /\
  TC.settle_m (o4_b7 (o4_b6 B5 (o4_cmdw B5 s key disp len cb) want at_ s)) 0 =
    Some (o4_b7 (o4_b6 B5 (o4_cmdw B5 s key disp len cb) want at_ s), tt) /\
  B' = o4_b7 (o4_b6 B5 (o4_cmdw B5 s key disp len cb) want at_ s) /\ c' = cn /\ k' = k.
Proof.
intros B5 s key disp len cb want at_ cn k B' c' k' E.
set (Bw := o4_cmdw B5 s key disp len cb) in *.
unfold o4_b6. revert E.
destruct (want =? DSpec.SPEC_OK) eqn:Ew.
- apply Z.eqb_eq in Ew.
  destruct (0 <=? at_) eqn:Ea.
  + apply Z.leb_le in Ea.
    destruct (TC.CMDS_MAX <=? TW.Q_at Bw at_) eqn:Eq; cbv beta iota; intros E; [discriminate E|].
    apply Z.leb_gt in Eq.
    destruct (o4m_settle_tail _ cn k B' c' k' E) as (Es & EB & EC & EK).
    split; [intros _ _; exact Eq|]. split; [intros _ Hn; lia|].
    split; [exact Es|]. split; [exact EB|]. exact (conj EC EK).
  + apply Z.leb_gt in Ea.
    destruct (TC.CMDS_MAX <=? TW.g_nq Bw) eqn:Eq; cbv beta iota; intros E; [discriminate E|].
    apply Z.leb_gt in Eq.
    destruct (o4m_settle_tail _ cn k B' c' k' E) as (Es & EB & EC & EK).
    split; [intros _ Hp; lia|]. split; [intros _ _; exact Eq|].
    split; [exact Es|]. split; [exact EB|]. exact (conj EC EK).
- apply Z.eqb_neq in Ew. cbv beta iota. intros E.
  destruct (o4m_settle_tail _ cn k B' c' k' E) as (Es & EB & EC & EK).
  split; [intros Hw; exfalso; exact (Ew Hw)|]. split; [intros Hw; exfalso; exact (Ew Hw)|].
  split; [exact Es|]. split; [exact EB|]. exact (conj EC EK).
Qed.

(* The segment's model: from the CMDW cut's equations and the operation's simulation facts, the model's Some
   (LoopOk.op_ok) fixes the replace / append bounds, settle keeps B7, and the operation's equation at every
   stream ends at B7 with the cursor tg_c. *)
Lemma o4_model : forall (D B0 B1 B3 B4 B5 : list byte) (c0 : TOP.fuzz_in) (k0 : nat) (ops at_ rc : Z),
  AG.agree timg_A ops B0 -> 0 <= ops < TC.OPS_MAX -> QF.fuzz_in_ok D c0 -> TOP.fi_n c0 <> 0 ->
  lc_opc D c0 = 4 ->
  TC.op_begin_m B0 = Some (B1, tt) -> TW.g_raw B1 = 0 ->
  let kd := lc_sub_kd D (lc_oc D c0) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  let cs := TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd) in
  let want := lc_want tv at_ in
  let Bw := o4_cmdw B5 (tg_serial tv) (sv_key kd) (sv_display kd) (tg_len tv) (tg_cbytes tv) in
  let B7 := o4_b7 (o4_b6 B5 Bw want at_ (tg_serial tv)) in
  0 <= tg_serial tv < TC.CMDS_MAX ->
  lc_at tv (sv_key kd) = Some at_ ->
  TS0.diginet_session_submit_m (tg_B2 tv) cs = Some (B3, rc) ->
  TC.check_refusal_submit_m B3 cs rc (TW.S_queued B0) = Some (B4, tt) ->
  (if lc_sys tv then B5 = B4 else TC.check_latest_submit_m B4 rc want = Some (B5, tt)) ->
  (want = DSpec.SPEC_OK -> 0 <= at_ -> 0 <= TW.Q_at Bw at_ < TC.CMDS_MAX) /\
  (want = DSpec.SPEC_OK -> at_ < 0 -> 0 <= TW.g_nq Bw < TC.CMDS_MAX) /\
  TC.settle_m B7 0 = Some (B7, tt) /\
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 A D c0 k0 = Some (B7, (tg_c tv, k0))).
Proof.
intros D B0 B1 B3 B4 B5 c0 k0 ops at_ rc HA Hops Hc Hn Ho HOB HR.
cbv zeta. intros Hser Hat Hsub Href Hlat.
destruct (LOK.op_ok LP.links_holds timg_A ops B0 (fun _ => 1) D c0 k0 HA Hops Hc Hn
            ltac:(cbv beta; lia) ltac:(cbv beta; lia)) as (B' & c' & k' & E0 & _ & _).
assert (Hany : forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 A D c0 k0 =
                         TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 (fun _ => 1) D c0 k0).
{ intros A. rewrite (lc_op4_eq timg_A B0 A D c0 k0 Ho), (lc_op4_eq timg_A B0 (fun _ => 1) D c0 k0 Ho).
  reflexivity. }
pose proof E0 as E'.
rewrite (lc_op4_eq timg_A B0 (fun _ => 1) D c0 k0 Ho) in E'.
rewrite (lc_submit_tag_eq B0 B1 D (lc_oc D c0) HOB HR) in E'.
cbv zeta in E'.
set (kd := lc_sub_kd D (lc_oc D c0)) in *.
set (tv := lc_tag_vals D B1 (sv_c kd)) in *.
rewrite (proj2 (Z.leb_gt TC.CMDS_MAX (tg_serial tv)) (proj2 Hser)) in E'. cbv beta iota in E'.
rewrite Hat in E'. cbv beta iota in E'.
rewrite Hsub in E'. cbv beta iota in E'.
rewrite Href in E'. cbv beta iota in E'.
assert (H5 : (if lc_sys tv then Some (B4, tt) else TC.check_latest_submit_m B4 rc (lc_want tv at_)) =
             Some (B5, tt)).
{ revert Hlat. destruct (lc_sys tv); intros Hlat; [rewrite Hlat; reflexivity|exact Hlat]. }
rewrite H5 in E'. cbv beta iota in E'.
destruct (o4m_tail B5 (tg_serial tv) (sv_key kd) (sv_display kd) (tg_len tv) (tg_cbytes tv) (lc_want tv at_) at_
            (tg_c tv) k0 B' c' k' E') as (Hq & Hg & Hs & EB & EC & EK).
split; [intros Hw Ha; split; [unfold TW.Q_at; apply QF.u_at_nonneg|exact (Hq Hw Ha)]|].
split; [intros Hw Ha; split; [unfold TW.g_nq; apply QF.u_at_nonneg|exact (Hg Hw Ha)]|].
split; [exact Hs|].
intros A. rewrite (Hany A), E0, EB, EC, EK. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at CMDW                                          *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at CMDW; 32 c = F + 32; 33 serial (72(s1)); 34 the bytes left before the take
   (56(s1)); 35 c.key; 36 c.display; 37 c.len; 38 g_ncmd and 39 g_nq of the CMDW world. Regions: the spill slots
   [s1 + 8, s1 + 192) the segment reloads (read only), c's len, display and key (read only), g_cmd[serial]'s st, key,
   display [s11, s11 + 12) and len [s11 + 36, s11 + 37) (written), g_ncmd (written). The pages transport_hi 10, 14, 15
   of the spill slots 160, 24, 80 hold g_fail_next's, g_nq's and g_ncmd's pages (the loads at 944(page) / 972(page) are
   g_nq / g_ncmd). *)
Definition o4_rg_sp : YP09.region := YP09.mkRegion (Some 9%nat) 8 192 0 0
  [YP09.mkChunk 24 (CVal 8 (SLit (transport_hi 14))); YP09.mkChunk 56 (CVal 8 (SOff 34 0));
   YP09.mkChunk 64 (CVal 8 (SLit TA_g_cmd)); YP09.mkChunk 72 (CVal 8 (SOff 33 0));
   YP09.mkChunk 80 (CVal 8 (SLit (transport_hi 15))); YP09.mkChunk 160 (CVal 8 (SLit (transport_hi 10)));
   YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition o4_rg_c : YP09.region := YP09.mkRegion (Some 32%nat) 24 32 0 0
  [YP09.mkChunk 24 (CVal 1 (SOff 37 0)); YP09.mkChunk 25 (CVal 1 (SOff 36 0)); YP09.mkChunk 28 (CVal 4 (SOff 35 0))].
Definition o4_rg_cmda : YP09.region := YP09.mkRegion (Some 27%nat) 0 12 0 12 [].
Definition o4_rg_cmdb : YP09.region := YP09.mkRegion (Some 27%nat) 36 37 36 37 [].
Definition o4_rg_ncmd : YP09.region := YP09.mkRegion None TA_g_ncmd (TA_g_ncmd + 4) TA_g_ncmd (TA_g_ncmd + 4)
  [YP09.mkChunk TA_g_ncmd (CVal 4 (SOff 38 0))].
Definition o4_rg_nq : YP09.region := YP09.mkRegion None TA_g_nq (TA_g_nq + 4) TA_g_nq (TA_g_nq + 4)
  [YP09.mkChunk TA_g_nq (CVal 4 (SOff 39 0))].
Definition o4_facts1 : facts :=
  mkFacts [(2%nat, mkAF (140735332483072 + 32432) (2 ^ 47) 5); (9%nat, mkAF (140735332483072 + 32432) (2 ^ 47) 5);
           (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (27%nat, mkAF TA_g_cmd (TA_g_cmd + 40 * 1023) 3);
           (32%nat, mkAF 4096 140737479966720 5);
           (35%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0);
           (38%nat, mkAF 0 (2 ^ 32 - 1) 0); (39%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition o4_ss1 : sstate := mkSS LO_CMDW sr_atoms [o4_rg_sp; o4_rg_c] None o4_facts1.
(* The shadow base s10 and the shadow entry of g_cmd[serial]'s 40 bytes. *)
Definition O4_Bx : sv := SOff 26 0.
Definition O4_SH1 : list shent := [mkSHE 27 0 40].

(* The extra atoms 32 .. 39. *)
Definition o4_extra (F serial fin key disp len ncmd nq : Z) : list word :=
  [w64 (F + 32); w64 serial; w64 fin; w64 key; w64 disp; w64 len; w64 ncmd; w64 nq].

(* The atoms a run state may not use for the generalization at j, j + 1. *)
Definition o4_P (j : nat) (n : nat) : bool := negb (Nat.eqb n j) && negb (Nat.eqb n (S j)).

Section mach. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition o4_E1 (regs : bvmap 5 word) (F serial fin key disp len ncmd nq : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs (o4_extra F serial fin key disp len ncmd nq)).

Lemma o4_vals : VAL (A_OBJ 20) = TA_g_q /\ BASE = transport_text.
Proof. vm_compute. split; reflexivity. Qed.

(* A register's value becomes the fresh atom j (and the atom j + 1 is given the value v): the state's other atoms
   keep their values. *)
Lemma o4_gen : forall E ss ms (r : bv 5) (j : nat) (v : word),
  st_ok_pi segs VAL E ss ms -> bv_eqb r 0 = false ->
  ss_atoms_p (o4_P j) (abs_ss VAL ss) = true ->
  st_ok_pi segs VAL (ewset (ewset E j (YK11.getr (ms_regs ms) r)) (S j) v)
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff j 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r j v HS Hr0 Hat.
set (E' := ewset (ewset E j (YK11.getr (ms_regs ms) r)) (S j) v).
assert (HA : env_agree_p (o4_P j) E E').
{ split; [|reflexivity]. intros n Hn. unfold o4_P in Hn. apply andb_prop in Hn as [H1 H2].
  apply negb_true_iff, Nat.eqb_neq in H1. apply negb_true_iff, Nat.eqb_neq in H2.
  unfold E'. rewrite !ew_ewset_other by assumption. reflexivity. }
pose proof (st_ok_agree_p (o4_P j) segs E E' _ ms HS HA Hat) as HS'.
unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs segs E' _ ms (sr_set (ss_regs ss) r (SOff j 0)) HS').
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0.
  pose proof (st_ok_reg segs E' _ ms r HS') as Hq. cbn [ss_regs] in Hq. rewrite <- Hq.
  cbn [sv_denot]. unfold E'. rewrite ew_ewset_other by lia. rewrite ew_ewset_same, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* The same at a run's (absolute) state. *)
Lemma o4_gen_abs : forall E ss ms (r : bv 5) (j : nat) (v : word),
  st_ok segs E ss ms -> bv_eqb r 0 = false -> ss_atoms_p (o4_P j) ss = true ->
  st_ok segs (ewset (ewset E j (YK11.getr (ms_regs ms) r)) (S j) v)
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff j 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r j v HS Hr0 Hat.
set (E' := ewset (ewset E j (YK11.getr (ms_regs ms) r)) (S j) v).
assert (HA : env_agree_p (o4_P j) E E').
{ split; [|reflexivity]. intros n Hn. unfold o4_P in Hn. apply andb_prop in Hn as [H1 H2].
  apply negb_true_iff, Nat.eqb_neq in H1. apply negb_true_iff, Nat.eqb_neq in H2.
  unfold E'. rewrite !ew_ewset_other by assumption. reflexivity. }
pose proof (st_ok_agree_p (o4_P j) segs E E' _ ms HS HA Hat) as HS'.
apply (st_ok_regs segs E' _ ms (sr_set (ss_regs ss) r (SOff j 0)) HS').
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0.
  pose proof (st_ok_reg segs E' _ ms r HS') as Hq. rewrite <- Hq.
  cbn [sv_denot]. unfold E'. rewrite ew_ewset_other by lia. rewrite ew_ewset_same, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* c's len, display and key bytes from c's struct. *)
Lemma o4_c_vals : forall (m : word -> option byte) (c : Z) (cb : list byte) (len disp key : Z),
  garr8 segs m c (TW.zs (TOP.cmd_struct cb len disp key)) -> length cb = 24%nat ->
  0 <= len < 256 -> 0 <= disp < 256 ->
  YI04.val_mem segs m (c + 24) 1 len /\ YI04.val_mem segs m (c + 25) 1 disp /\ YI04.val_mem segs m (c + 28) 4 key.
Proof.
intros m c cb len disp key HG Hcb Hl Hd.
assert (HL : length (TW.zs (TOP.cmd_struct cb len disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hcb, TWL.length_put. reflexivity. }
assert (HN : forall i, (24 <= i < 32)%nat ->
  nth i (TW.zs (TOP.cmd_struct cb len disp key)) 0 =
  bv_unsigned (nth (i - 24) ([DSpec.b8 len; DSpec.b8 disp; DSpec.b8 0; DSpec.b8 0] ++ TW.put 4 key) (Z_to_bv 8 0))).
{ intros i Hi. unfold TW.zs, TOP.cmd_struct.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, !length_app, Hcb, TWL.length_put; cbn; lia).
  rewrite map_nth. rewrite app_nth2 by lia. rewrite Hcb. reflexivity. }
assert (V : forall i, (i < 32)%nat -> YI04.val_mem segs m (c + Z.of_nat i) 1 (nth i (TW.zs (TOP.cmd_struct cb len disp key)) 0))
  by (intros i Hi; exact (proj1 (HG i ltac:(rewrite HL; lia)))).
split; [|split].
- pose proof (V 24%nat ltac:(lia)) as H. rewrite HN in H by lia. cbn in H.
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap, bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H.
  rewrite Z.mod_small in H by lia. exact H.
- pose proof (V 25%nat ltac:(lia)) as H. rewrite HN in H by lia. cbn in H.
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap, bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H.
  rewrite Z.mod_small in H by lia. exact H.
- intros k Hk. pose proof (V (28 + k)%nat ltac:(lia)) as H. rewrite HN in H by lia.
  replace (28 + k - 24)%nat with (4 + k)%nat in H by lia.
  change ([DSpec.b8 len; DSpec.b8 disp; DSpec.b8 0; DSpec.b8 0] ++ TW.put 4 key) with
    ([DSpec.b8 len; DSpec.b8 disp; DSpec.b8 0; DSpec.b8 0] ++ TW.put 4 key) in H.
  rewrite app_nth2 in H by (cbn; lia). cbn [length] in H. replace (4 + k - 4)%nat with k in H by lia.
  rewrite tw_le_byte_put in H by exact Hk.
  specialize (H 0%nat ltac:(lia)). cbn [Z.of_nat] in H. rewrite Z.add_0_r in H.
  replace (c + Z.of_nat (28 + k)) with (c + 28 + Z.of_nat k) in H by lia. rewrite H. do 2 f_equal.
  apply tw_le_byte1. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* A payload byte of g_cmd, g_q, g_nq or g_ncmd is a byte of G. *)
Lemma o4_inG_cmd : forall a, TA_g_cmd <= a < TA_g_cmd + 40960 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (ios_inG_row _ _ _ a TMAP_A_g_cmd). unfold TW.SZ_g_cmd. lia. Qed.
Lemma o4_inG_q : forall a, TA_g_q <= a < TA_g_q + 4096 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (ios_inG_row _ _ _ a TMAP_A_g_q). unfold TW.SZ_g_q. lia. Qed.
Lemma o4_inG_nq : forall a, TA_g_nq <= a < TA_g_nq + 4 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (ios_inG_row _ _ _ a TMAP_A_g_nq). unfold TW.SZ_g_nq. lia. Qed.
Lemma o4_inG_ncmd : forall a, TA_g_ncmd <= a < TA_g_ncmd + 4 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (ios_inG_row _ _ _ a TMAP_A_g_ncmd). unfold TW.SZ_g_ncmd. lia. Qed.

(* A shadow entry inside a zero-shadow payload of G. *)
Lemma o4_she : forall ly S (W : world segs) mem md (E : env) (mt : nat) (p lo hi glo ghi : Z),
  @AR rc segs B ly S W mem md -> decode_zshadow_at B glo ghi ->
  U E O4_Bx = SHADOW_OFF -> U E (SOff mt 0) = p -> 0 <= lo < hi ->
  glo <= (p + lo) / 64 * 64 -> (p + hi - 1) / 64 * 64 + 64 <= ghi -> 0 <= p -> p + hi <= SHADOW_OFF ->
  shent_ok segs O4_Bx E (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros ly S W mem md E mt p lo hi glo ghi HAR HZ HB Hp Hlh Hglo Hghi Hp0 HpS.
apply (shent_ok_of_range segs (w_H W) mem E O4_Bx mt (p + lo) (hi - lo) p lo hi).
- exact (proj1 (decode_zshadow_ra B ly S W mem md glo ghi (p + lo) (hi - lo) HAR HZ ltac:(lia) Hglo
    ltac:(replace (p + lo + (hi - lo) - 1) with (p + hi - 1) by lia; exact Hghi))).
- exact HB.
- exact Hp.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
Qed.

(* The bounds of g_cmd[s]'s 40 bytes in g_cmd's 64-byte blocks. *)
Lemma o4_cmd_blk : forall s lo hi, 0 <= s < 1024 -> 0 <= lo -> lo < hi <= 40 ->
  TA_g_cmd <= (TA_g_cmd + 40 * s + lo) / 64 * 64 /\ (TA_g_cmd + 40 * s + hi - 1) / 64 * 64 + 64 <= TA_g_cmd + 40960.
Proof.
intros s lo hi Hs Hl Hh. unfold TA_g_cmd. split.
- assert (H : 6181888 / 64 <= (6181888 + 40 * s + lo) / 64) by (apply Z.div_le_mono; lia).
  change (6181888 / 64) with 96592 in H. lia.
- assert (H : (6181888 + 40 * s + hi - 1) / 64 <= 6222847 / 64) by (apply Z.div_le_mono; lia).
  change (6222847 / 64) with 97231 in H. lia.
Qed.

Lemma o4_q_blk : forall i, 0 <= i < 1024 ->
  TA_g_q <= (TA_g_q + 4 * i + 0) / 64 * 64 /\ (TA_g_q + 4 * i + 4 - 1) / 64 * 64 + 64 <= TA_g_q + 4096.
Proof.
intros i Hi. unfold TA_g_q. split.
- assert (H : 6232064 / 64 <= (6232064 + 4 * i + 0) / 64) by (apply Z.div_le_mono; lia).
  change (6232064 / 64) with 97376 in H. lia.
- assert (H : (6232064 + 4 * i + 4 - 1) / 64 <= 6236159 / 64) by (apply Z.div_le_mono; lia).
  change (6236159 / 64) with 97439 in H. lia.
Qed.

(* The state at CMDW holds of the machine state there. *)
Lemma o4_entry1 : forall (W : world segs) (regs : bvmap 5 word) mem (sp1 F serial fin key disp len ncmd nq : Z),
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 27 = w64 (TA_g_cmd + 40 * serial) ->
  YM05.alloc_ceiling + 32432 <= sp1 <= 2 ^ 47 - 320 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= YM05.alloc_ceiling ->
  0 <= serial < 1024 -> 0 <= fin < 2 ^ 64 -> 0 <= key < 2 ^ 32 -> 0 <= disp < 256 -> 0 <= len < 256 ->
  0 <= ncmd < 2 ^ 32 -> 0 <= nq < 2 ^ 32 ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some (transport_hi 14) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some fin ->
  rdword (aview segs (w_H W) mem) (sp1 + 64) = Some TA_g_cmd ->
  rdword (aview segs (w_H W) mem) (sp1 + 72) = Some serial ->
  rdword (aview segs (w_H W) mem) (sp1 + 80) = Some (transport_hi 15) ->
  rdword (aview segs (w_H W) mem) (sp1 + 160) = Some (transport_hi 10) ->
  rdword (aview segs (w_H W) mem) (sp1 + 168) = Some (F + 32) ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (F + 32 + 24) 1 len ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (F + 32 + 25) 1 disp ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (F + 32 + 28) 4 key ->
  st_ok_pi segs VAL (o4_E1 regs F serial fin key disp len ncmd nq) o4_ss1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_CMDW)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp1 F serial fin key disp len ncmd nq R2 R9 R26 R27 Hsp1 Hsp32 HF0 HF64 HFg Hs Hfin Hkey
  Hdisp Hlen Hncmd Hnq S24 S56 S64 S72 S80 S160 S168 Vlen Vdisp Vkey.
pose proof YM05.alloc_ceiling_value as Hce.
set (E := o4_E1 regs F serial fin key disp len ncmd nq).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, o4_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (o4_extra F serial fin key disp len ncmd nq) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, o4_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
cbn [Nat.add nth o4_extra] in E32, E33, E34, E35, E36, E37, E38, E39. clear EX.
assert (U2 : bv_unsigned (ew E 2) = sp1)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = TA_g_cmd + 40 * serial)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; unfold TA_g_cmd; lia).
assert (U32 : bv_unsigned (ew E 32) = F + 32) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = key) by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = disp) by (rewrite E36; unfold w64; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = len) by (rewrite E37; unfold w64; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = ncmd) by (rewrite E38; unfold w64; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E 39) = nq) by (rewrite E39; unfold w64; apply unsigned_lit_small; lia).
assert (CH : forall (a : nat) (base off v : Z), ew E a = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (base + off) = Some v ->
  YP09.chunk_ok segs E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff a 0)))).
{ intros a base off v Ha Hv Hr. apply (chunk_ok_val segs E _ base off 8 (SOff a 0) v);
    [cbn [sv_denot]; rewrite Ha; unfold w64; rewrite unsigned_lit_small by exact Hv; rewrite Z.add_0_r; reflexivity
    | exact Hv | cbn; lia | exact (val_mem_of_rdword segs _ _ _ _ Hr)]. }
assert (CL : forall (base off v : Z), 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (base + off) = Some v ->
  YP09.chunk_ok segs E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SLit v)))).
{ intros base off v Hv Hr. apply (chunk_ok_val segs E _ base off 8 (SLit v) v);
    [reflexivity | exact Hv | cbn; lia | exact (val_mem_of_rdword segs _ _ _ _ Hr)]. }
destruct lf_spill_pages as (P8 & P9 & P10 & P11 & P14 & P15).
rewrite restrict_mkst_fx. unfold o4_ss1.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks o4_rg_sp o4_rg_c base_val];
    rewrite ?U9, ?U32.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply CL; [rewrite P14; lia | exact S24].
    * apply (CH 34%nat _ _ fin); [exact E34 | exact Hfin | exact S56].
    * apply CL; [unfold TA_g_cmd; lia | exact S64].
    * apply (CH 33%nat _ _ serial); [exact E33 | lia | exact S72].
    * apply CL; [rewrite P15; lia | exact S80].
    * apply CL; [rewrite P10; lia | exact S160].
    * apply (CH 32%nat _ _ (F + 32)); [exact E32 | lia | exact S168].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val segs E _ (F + 32) 24 1 (SOff 37 0) len);
        [cbn [sv_denot]; rewrite E37; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | lia | cbn; lia | exact Vlen].
    * apply (chunk_ok_val segs E _ (F + 32) 25 1 (SOff 36 0) disp);
        [cbn [sv_denot]; rewrite E36; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | lia | cbn; lia | exact Vdisp].
    * apply (chunk_ok_val segs E _ (F + 32) 28 4 (SOff 35 0) key);
        [cbn [sv_denot]; rewrite E35; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | lia | cbn; lia | exact Vkey].
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, o4_rg_sp, o4_rg_c.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold o4_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U26, U27, U32, U35, U36, U37, U38, U39.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (H8 : (TA_g_cmd + 40 * serial) mod 8 = 0).
  { unfold TA_g_cmd. replace (6181888 + 40 * serial) with ((772736 + 5 * serial) * 8) by lia. apply Z_mod_mult. }
  assert (H32 : (F + 32) mod 32 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
    replace (F + 32) with ((2 * (F / 64) + 1) * 32) by lia. apply Z_mod_mult. }
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF, TA_g_cmd in *; lia].
Qed.

(* The state at the return of __asan_memcpy (+0x121c): the spill slots, g_ncmd and g_nq (atoms 38, 39). *)
Definition LO_RCPY : Z := 0x121c.
Definition o4_ss2 : sstate := mkSS LO_RCPY sr_atoms [o4_rg_sp; o4_rg_ncmd; o4_rg_nq] None o4_facts1.

Lemma o4_entry2 : forall (W : world segs) (regs : bvmap 5 word) mem (sp1 F serial fin key disp len ncmd nq : Z),
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 27 = w64 (TA_g_cmd + 40 * serial) ->
  YM05.alloc_ceiling + 32432 <= sp1 <= 2 ^ 47 - 320 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= YM05.alloc_ceiling ->
  0 <= serial < 1024 -> 0 <= fin < 2 ^ 64 -> 0 <= key < 2 ^ 32 -> 0 <= disp < 256 -> 0 <= len < 256 ->
  0 <= ncmd < 2 ^ 32 -> 0 <= nq < 2 ^ 32 ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some (transport_hi 14) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some fin ->
  rdword (aview segs (w_H W) mem) (sp1 + 64) = Some TA_g_cmd ->
  rdword (aview segs (w_H W) mem) (sp1 + 72) = Some serial ->
  rdword (aview segs (w_H W) mem) (sp1 + 80) = Some (transport_hi 15) ->
  rdword (aview segs (w_H W) mem) (sp1 + 160) = Some (transport_hi 10) ->
  rdword (aview segs (w_H W) mem) (sp1 + 168) = Some (F + 32) ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (0 + TA_g_ncmd) 4 ncmd ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (0 + TA_g_nq) 4 nq ->
  st_ok_pi segs VAL (o4_E1 regs F serial fin key disp len ncmd nq) o4_ss2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_RCPY)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp1 F serial fin key disp len ncmd nq R2 R9 R26 R27 Hsp1 Hsp32 HF0 HF64 HFg Hs Hfin Hkey
  Hdisp Hlen Hncmd Hnq S24 S56 S64 S72 S80 S160 S168 Vncmd Vnq.
pose proof YM05.alloc_ceiling_value as Hce.
set (E := o4_E1 regs F serial fin key disp len ncmd nq).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, o4_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (o4_extra F serial fin key disp len ncmd nq) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, o4_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
cbn [Nat.add nth o4_extra] in E32, E33, E34, E35, E36, E37, E38, E39. clear EX.
assert (U2 : bv_unsigned (ew E 2) = sp1)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = TA_g_cmd + 40 * serial)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; unfold TA_g_cmd; lia).
assert (U32 : bv_unsigned (ew E 32) = F + 32) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = key) by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = disp) by (rewrite E36; unfold w64; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = len) by (rewrite E37; unfold w64; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = ncmd) by (rewrite E38; unfold w64; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E 39) = nq) by (rewrite E39; unfold w64; apply unsigned_lit_small; lia).
assert (CH : forall (a : nat) (base off v : Z), ew E a = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (base + off) = Some v ->
  YP09.chunk_ok segs E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff a 0)))).
{ intros a base off v Ha Hv Hr. apply (chunk_ok_val segs E _ base off 8 (SOff a 0) v);
    [cbn [sv_denot]; rewrite Ha; unfold w64; rewrite unsigned_lit_small by exact Hv; rewrite Z.add_0_r; reflexivity
    | exact Hv | cbn; lia | exact (val_mem_of_rdword segs _ _ _ _ Hr)]. }
assert (CL : forall (base off v : Z), 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (base + off) = Some v ->
  YP09.chunk_ok segs E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SLit v)))).
{ intros base off v Hv Hr. apply (chunk_ok_val segs E _ base off 8 (SLit v) v);
    [reflexivity | exact Hv | cbn; lia | exact (val_mem_of_rdword segs _ _ _ _ Hr)]. }
destruct lf_spill_pages as (P8 & P9 & P10 & P11 & P14 & P15).
rewrite restrict_mkst_fx. unfold o4_ss2.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks o4_rg_sp o4_rg_ncmd o4_rg_nq base_val];
    rewrite ?U9.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply CL; [rewrite P14; lia | exact S24].
    * apply (CH 34%nat _ _ fin); [exact E34 | exact Hfin | exact S56].
    * apply CL; [unfold TA_g_cmd; lia | exact S64].
    * apply (CH 33%nat _ _ serial); [exact E33 | lia | exact S72].
    * apply CL; [rewrite P15; lia | exact S80].
    * apply CL; [rewrite P10; lia | exact S160].
    * apply (CH 32%nat _ _ (F + 32)); [exact E32 | lia | exact S168].
  + split; [unfold TA_g_ncmd; lia|]. split; [unfold TA_g_ncmd; lia|].
    split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw); apply o4_inG_ncmd; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 TA_g_ncmd 4 (SOff 38 0) ncmd);
      [cbn [sv_denot]; rewrite E38; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
      | lia | cbn; lia | exact Vncmd].
  + split; [unfold TA_g_nq; lia|]. split; [unfold TA_g_nq; lia|].
    split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw); apply o4_inG_nq; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 TA_g_nq 4 (SOff 39 0) nq);
      [cbn [sv_denot]; rewrite E39; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
      | lia | cbn; lia | exact Vnq].
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, o4_rg_sp, o4_rg_ncmd, o4_rg_nq.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TA_g_ncmd, TA_g_nq.
  repeat split; first [exact I | lia].
- unfold o4_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U26, U27, U32, U35, U36, U37, U38, U39.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (H8 : (TA_g_cmd + 40 * serial) mod 8 = 0).
  { unfold TA_g_cmd. replace (6181888 + 40 * serial) with ((772736 + 5 * serial) * 8) by lia. apply Z_mod_mult. }
  assert (H32 : (F + 32) mod 32 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
    replace (F + 32) with ((2 * (F / 64) + 1) * 32) by lia. apply Z_mod_mult. }
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF, TA_g_cmd in *; lia].
Qed.

(* The shadow entry of the first run. *)
Lemma o4_shok1 : forall ly S (W : world segs) mem md (E : env) serial,
  trans_settle_cells B -> @AR rc segs B ly S W mem md -> 0 <= serial < 1024 ->
  ew E 27 = w64 (TA_g_cmd + 40 * serial) -> ew E 26 = w64 SHADOW_OFF ->
  sh_ok segs O4_Bx O4_SH1 E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E serial (_ & _ & _ & HZc) HAR Hs E27 E26.
unfold sh_ok, O4_SH1. constructor; [|constructor].
destruct (o4_cmd_blk serial 0 40 Hs ltac:(lia) ltac:(lia)) as [Hb1 Hb2].
apply (o4_she ly S W mem md E 27 (TA_g_cmd + 40 * serial) 0 40 TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) HAR HZc).
- unfold U, O4_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold w64. apply unsigned_lit_small. unfold TA_g_cmd. lia.
- lia.
- exact Hb1.
- unfold TW.SZ_g_cmd. exact Hb2.
- unfold TA_g_cmd. lia.
- unfold TA_g_cmd, SHADOW_OFF. lia.
Qed.
(* A written region of G bytes at an atom's address, with no chunk. *)
Lemma o4_rgw_ok : forall E (m : word -> option byte) (n : nat) b lo hi,
  bv_unsigned (ew E n) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 -> lo <= hi ->
  (forall o, lo <= o < hi -> inG TG.G_HARNESS (b + o)) ->
  region_ok segs E m (YP09.mkRegion (Some n) lo hi lo hi []).
Proof.
intros E m n b lo hi Hn H0 H1 Hlh HG. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw). apply HG. lia.
Qed.

(* A written 4-byte G cell at its address, holding the value of atom a. *)
Lemma o4_rgabs_ok : forall E (m : word -> option byte) (a : nat) g v,
  bv_unsigned (ew E a) = v -> 0 <= v < 2 ^ 32 -> 0 <= g -> g + 4 <= 2 ^ 64 ->
  (forall o, g <= o < g + 4 -> inG TG.G_HARNESS o) ->
  YI04.val_mem segs m (0 + g) 4 v ->
  region_ok segs E m (YP09.mkRegion None g (g + 4) g (g + 4) [YP09.mkChunk g (CVal 4 (SOff a 0))]).
Proof.
intros E m a g v Ha Hv Hg0 Hg1 HG V. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|].
split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw); apply HG; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val segs E _ 0 g 4 (SOff a 0) v);
  [cbn [sv_denot]; rewrite Ha, Z.add_0_r; reflexivity | lia | cbn; lia | exact V].
Qed.

(* A written 4-byte G cell at atom n's address, holding the value of atom k. *)
Lemma o4_rgc_ok : forall E (m : word -> option byte) (n k : nat) b v,
  bv_unsigned (ew E n) = b -> bv_unsigned (ew E k) = v -> 0 <= v < 2 ^ 32 -> 0 <= b -> b + 4 <= 2 ^ 64 ->
  (forall o, 0 <= o < 4 -> inG TG.G_HARNESS (b + o)) -> YI04.val_mem segs m (b + 0) 4 v ->
  region_ok segs E m (YP09.mkRegion (Some n) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff k 0))]).
Proof.
intros E m n k b v Hb Hv Hvr Hb0 Hb1 HG V. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
split; [lia|]. split; [lia|].
split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw); apply HG; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val segs E _ b 0 4 (SOff k 0) v);
  [cbn [sv_denot]; rewrite Hv, Z.add_0_r; reflexivity | lia | cbn; lia | exact V].
Qed.

(* A word the view reads is below 2 ^ 64. *)
Lemma o4_rdword_range : forall H (m : word -> option byte) a v, rdword (aview segs H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H m a v Hr. unfold rdword in Hr.
assert (BY : forall x, match aview segs H m x with Some b => 0 <= b < 256 | None => True end).
{ intros x. change (aview segs H m x) with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H m) x)).
  destruct (YP09.mbyte segs (mrestrict H m) x) as [b|]; cbn [option_map]; [|exact I].
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
pose proof (BY a) as B0. pose proof (BY (a + 1)) as B1. pose proof (BY (a + 2)) as B2. pose proof (BY (a + 3)) as B3.
pose proof (BY (a + 4)) as B4. pose proof (BY (a + 5)) as B5. pose proof (BY (a + 6)) as B6. pose proof (BY (a + 7)) as B7.
destruct (aview segs H m a); [|discriminate Hr]. destruct (aview segs H m (a + 1)); [|discriminate Hr].
destruct (aview segs H m (a + 2)); [|discriminate Hr]. destruct (aview segs H m (a + 3)); [|discriminate Hr].
destruct (aview segs H m (a + 4)); [|discriminate Hr]. destruct (aview segs H m (a + 5)); [|discriminate Hr].
destruct (aview segs H m (a + 6)); [|discriminate Hr]. destruct (aview segs H m (a + 7)); [|discriminate Hr].
injection Hr as <-. lia.
Qed.

(* An aview equality carries a val_mem fact. *)
Lemma o4_val_mem_xfer : forall H (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview segs H m' (a + Z.of_nat k) = aview segs H m (a + Z.of_nat k)) ->
  YI04.val_mem segs (mrestrict H m) a n v -> YI04.val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hk V k Hkn. rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat k) (Hk k Hkn)). exact (V k Hkn).
Qed.

(* The view of a byte val_mem fixes. *)
Lemma o4_aview_of_val : forall H (m : word -> option byte) a n v k,
  YI04.val_mem segs (mrestrict H m) a n v -> (k < n)%nat -> aview segs H m (a + Z.of_nat k) = Some (YO0f.le_byte v n k).
Proof.
intros H m a n v k V Hk.
change (aview segs H m (a + Z.of_nat k)) with
  (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H m) (a + Z.of_nat k))).
rewrite (V k Hk). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. unfold YO0f.le_byte. change (2 ^ 8) with 256.
apply Z.mod_pos_bound. lia.
Qed.

Lemma o4_le_mod : forall x (n k : nat), YO0f.le_byte (x mod 2 ^ (8 * Z.of_nat n)) n k = YO0f.le_byte x n k.
Proof. intros x n k. unfold YO0f.le_byte. rewrite Zmod_mod. reflexivity. Qed.

Lemma o4_le_eqv : forall x y (n k : nat), x mod 2 ^ (8 * Z.of_nat n) = y mod 2 ^ (8 * Z.of_nat n) ->
  YO0f.le_byte x n k = YO0f.le_byte y n k.
Proof. intros x y n k H. unfold YO0f.le_byte. rewrite H. reflexivity. Qed.

(* The bytes of a chunk, through the view, as the bytes of a value x it agrees with. *)
Lemma o4_chunk_bytes : forall E H (m : word -> option byte) base od (w : N) (wn : nat) e x,
  YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk od (CVal w e)) -> Z.of_N w = Z.of_nat wn -> (wn <= 8)%nat ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_nat wn) = x mod 2 ^ (8 * Z.of_nat wn) ->
  forall k, (k < wn)%nat -> aview segs H m (base + od + Z.of_nat k) = Some (YO0f.le_byte x wn k).
Proof.
intros E H m base od w wn e x HC Hw Hwn Hx k Hk.
pose proof (val_of_chunk_any segs E (mrestrict H m) base od w e HC ltac:(lia)) as V.
assert (Ew : N.to_nat w = wn) by lia. rewrite Ew in V.
replace (8 * Z.of_N w) with (8 * Z.of_nat wn) in V by lia.
rewrite (o4_aview_of_val H m (base + od) wn _ k V Hk). f_equal.
rewrite o4_le_mod. apply o4_le_eqv. exact Hx.
Qed.

(* `bnez s6` on want. *)
Lemma o4_br_want : forall E want, ew E 22 = w64 want -> (want = 0 \/ want = -10 \/ want = -5) ->
  branch_taken BC_NE (sv_denot E (SOff 22 0)) (sv_denot E (SLit 0)) = negb (want =? 0).
Proof.
intros E want H Hw. cbn [sv_denot]. rewrite H, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
destruct Hw as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

(* s3 = s8 + s9 and s7 = 56(s1) - s9 at the end of the segment. *)
Lemma o4_den_add : forall E (x y : nat) a b, ew E x = w64 a -> ew E y = w64 b ->
  sv_denot E (SAlu ALU_ADD (SOff x 0) (SOff y 0)) = w64 (a + b).
Proof.
intros E x y a b Ha Hb. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff x 0) (SOff y 0)))) with (U E (SAlu ALU_ADD (SOff x 0) (SOff y 0))).
rewrite U_SAlu, !U_SOff. cbn [zalu_raw]. rewrite Ha, Hb. unfold w64, zcanon, M64. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z.add_0_r.
repeat rewrite ?Zmod_mod, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma o4_den_sub : forall E (x y : nat) a b, ew E x = w64 a -> ew E y = w64 b ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff y 0) (SLit (-1))) (SOff x 0)) = w64 (a - b).
Proof.
intros E x y a b Ha Hb. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff y 0) (SLit (-1))) (SOff x 0))))
  with (U E (SAlu ALU_ADD (SMd M_MUL (SOff y 0) (SLit (-1))) (SOff x 0))).
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw]. rewrite Ha, Hb. unfold w64, zcanon, M64.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z.add_0_r.
repeat rewrite ?Zmod_mod, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r.
rewrite <- (Zplus_mod_idemp_l (b mod 2 ^ 64 * (-1 mod 2 ^ 64))), <- Zmult_mod, Zplus_mod_idemp_l.
f_equal. ring.
Qed.

(* x mod (c * d) mod c, x mod 2 ^ 64 mod 2 ^ 32 and the 32-bit signed wrap. *)
Lemma o4_mod_mul : forall x c d, 0 < c -> 0 < d -> x mod (c * d) mod c = x mod c.
Proof.
intros x c d Hc Hd. rewrite (Z.mod_eq x (c * d)) by lia.
replace (x - c * d * (x / (c * d))) with (x + (- (d * (x / (c * d)))) * c) by ring. apply Z_mod_plus_full.
Qed.
Lemma o4_mod64_32 : forall x, x mod 2 ^ 64 mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. apply o4_mod_mul; lia. Qed.
Lemma o4_swrap32 : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. unfold bv_swrap, bv_wrap, bv_modulus, bv_half_modulus. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.

(* lw, + 1, sw: the 4 bytes of (v + 1). *)
Lemma o4_den_inc : forall E (n : nat) v, bv_unsigned (ew E n) = v ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))) mod 2 ^ (8 * Z.of_nat 4) =
  (v + 1) mod 2 ^ (8 * Z.of_nat 4).
Proof.
intros E n v Hv. change (8 * Z.of_nat 4) with 32.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))))
  with (U E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))).
rewrite U_SAlu, U_SExt, U_SOff, U_SLit. cbn [zalu_raw]. rewrite Hv. unfold zcanon, M64.
change (Z.of_N 32) with 32. rewrite !o4_mod64_32.
rewrite Zplus_mod, o4_mod64_32, o4_swrap32, o4_mod64_32, Z.add_0_r, Zmod_mod, <- Zplus_mod.
rewrite (Zplus_mod v 1), <- (Zplus_mod v 1). reflexivity.
Qed.

(* lw (sign-extended), sw: the 4 bytes of v. *)
Lemma o4_den_sext : forall E (n : nat) v, bv_unsigned (ew E n) = v ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ (8 * Z.of_nat 4) = v mod 2 ^ (8 * Z.of_nat 4).
Proof.
intros E n v Hv. change (8 * Z.of_nat 4) with 32.
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite U_SExt, U_SOff. rewrite Hv. unfold zcanon, M64. change (Z.of_N 32) with 32.
rewrite o4_mod64_32, o4_swrap32, Zmod_mod, Z.add_0_r, o4_mod64_32. reflexivity.
Qed.

(* A plain atom or literal stored in w <= 8 bytes. *)
Lemma o4_mod64_w : forall x (w : nat), (w <= 8)%nat -> x mod 2 ^ 64 mod 2 ^ (8 * Z.of_nat w) = x mod 2 ^ (8 * Z.of_nat w).
Proof.
intros x w Hw. replace (2 ^ 64) with (2 ^ (8 * Z.of_nat w) * 2 ^ (64 - 8 * Z.of_nat w))
  by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
apply o4_mod_mul; apply Z.pow_pos_nonneg; lia.
Qed.
Lemma o4_den_off : forall E (n : nat) v (w : nat) z, bv_unsigned (ew E n) = v -> (w <= 8)%nat ->
  bv_unsigned (sv_denot E (SOff n z)) mod 2 ^ (8 * Z.of_nat w) = (v + z) mod 2 ^ (8 * Z.of_nat w).
Proof.
intros E n v w z Hv Hw. cbn [sv_denot]. rewrite Hv, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). exact (o4_mod64_w (v + z) w Hw).
Qed.
Lemma o4_den_lit : forall E z (w : nat), (w <= 8)%nat ->
  bv_unsigned (sv_denot E (SLit z)) mod 2 ^ (8 * Z.of_nat w) = z mod 2 ^ (8 * Z.of_nat w).
Proof.
intros E z w Hw. cbn [sv_denot]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). exact (o4_mod64_w z w Hw).
Qed.

(* A frame byte is no byte of G. *)
Lemma o4_apart : forall F g n, (forall x, F <= x < F + 256 -> ~ inG TG.G_HARNESS x) ->
  (forall x, g <= x < g + n -> inG TG.G_HARNESS x) -> 0 < n -> F + 256 <= g \/ g + n <= F.
Proof.
intros F g n HF HG Hn. destruct (Z_le_gt_dec (F + 256) g) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (g + n) F) as [H'|H']; [right; exact H'|]. exfalso.
apply (HF (Z.max F g)); [lia|]. apply HG. lia.
Qed.

(* `sext.w a0, s3; bltz a0`: s3 = at mod 2 ^ 32, at = -1 or an index. *)
Lemma o4_br_at : forall E at_, ew E 19 = w64 (at_ mod 2 ^ 32) -> (at_ = -1 \/ 0 <= at_ < 1024) ->
  branch_taken BC_LT (sv_denot E (SAluw ALU_ADD (SOff 19 0) (SLit 0))) (sv_denot E (SLit 0)) = (at_ <? 0).
Proof.
intros E at_ H Ha. destruct Ha as [-> | Ha].
- cbn [sv_denot]. rewrite H. vm_compute. reflexivity.
- cbn [branch_taken]. unfold bv_lts.
  change (bv_signed (sv_denot E (SLit 0))) with 0.
  assert (Hs : bv_signed (sv_denot E (SAluw ALU_ADD (SOff 19 0) (SLit 0))) = at_).
  { change (bv_signed (sv_denot E (SAluw ALU_ADD (SOff 19 0) (SLit 0)))) with (Sg E (SAluw ALU_ADD (SOff 19 0) (SLit 0))).
    rewrite S_SAluw, U_SOff, U_SLit. cbn [zalu_raw]. rewrite H.
    assert (EX : zcanon (bv_unsigned (w64 (at_ mod 2 ^ 32)) + 0) mod 2 ^ 32 + zcanon 0 mod 2 ^ 32 = at_).
    { unfold w64, zcanon, M64. pose proof (Z.mod_pos_bound at_ (2 ^ 32) ltac:(lia)) as Hy.
      rewrite unsigned_lit_small by lia.
      rewrite Z.add_0_r. change ((0 mod 2 ^ 64) mod 2 ^ 32) with 0. rewrite Z.add_0_r.
      rewrite (Z.mod_small (at_ mod 2 ^ 32) (2 ^ 64)) by lia.
      rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
    rewrite EX. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. }
  rewrite Hs. reflexivity.
Qed.

(* The address g_q + 4 i (`slli; auipc/addi; add`), i the value of atom n. *)
Lemma o4_den_gq : forall E (n : nat) v, bv_unsigned (ew E n) = v -> 0 <= v < 1024 -> img_env VAL A_LIM E ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SOff 261 0)) = w64 (TA_g_q + 4 * v).
Proof.
intros E n v Hv Hr HE.
assert (H261 : bv_unsigned (ew E 261) = TA_g_q).
{ rewrite (HE 261%nat ltac:(unfold A_TEXT, A_LIM; lia)). exact (proj1 o4_vals). }
apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SOff 261 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SOff 261 0))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hv, H261.
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
unfold w64. rewrite unsigned_lit_small by (unfold TA_g_q; lia).
unfold zcanon, M64. rewrite !Z.add_0_r.
rewrite (Z.mod_small v) by lia. rewrite (Z.mod_small (v * 4)) by lia.
rewrite (Z.mod_small TA_g_q) by (unfold TA_g_q; lia). rewrite Z.mod_small by (unfold TA_g_q; lia). lia.
Qed.

(* The address g_cmd + 40 q (`mul; ld 64(s1); add`), q the value of atom n. *)
Lemma o4_den_gc : forall E (n : nat) q, bv_unsigned (ew E n) = q -> 0 <= q < 1024 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 40)) (SLit 6181888)) = w64 (TA_g_cmd + 40 * q).
Proof.
intros E n q Hq Hr. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 40)) (SLit 6181888))))
  with (U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 40)) (SLit 6181888))).
rewrite U_SAlu, U_SMd, U_SOff, !U_SLit. cbn [zalu_raw zmd_raw]. rewrite Hq.
unfold w64. rewrite unsigned_lit_small by (unfold TA_g_cmd; lia).
unfold zcanon, M64. rewrite !Z.add_0_r.
rewrite (Z.mod_small q) by lia. change (40 mod 2 ^ 64) with 40. rewrite (Z.mod_small (q * 40)) by lia.
change (6181888 mod 2 ^ 64) with 6181888. rewrite Z.mod_small by lia. unfold TA_g_cmd. lia.
Qed.

(* c's first n <= 24 bytes are addressable (shadow 4 .. 6 of the frame is 0 while c is in scope) and the shadow
   bytes of their hull are the frame's first 8. *)
Lemma o4_c_src : forall cx (rd : reader) n,
  lc_fsh cx rd true false -> 4096 <= lc_F cx -> lc_F cx mod 64 = 0 -> 0 < n <= 24 ->
  range_addressable rd SHADOW_OFF (lc_F cx + 32) n /\ shadow_hull_vis rd (lc_F cx + 32) n.
Proof.
intros cx rd n HS HF0 HF64 Hn.
pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
remember (lc_F cx / 64) as k eqn:Ek. clear Ek.
assert (EF8 : lc_F cx / 8 = 8 * k) by (rewrite D; replace (64 * k) with ((8 * k) * 8) by ring; apply Z.div_mul; lia).
assert (ESH : lc_SH cx = SHADOW_OFF + 8 * k) by (unfold lc_SH; rewrite EF8; reflexivity).
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  assert (Hq : x / 8 = 8 * k + 4 \/ x / 8 = 8 * k + 5 \/ x / 8 = 8 * k + 6).
  { pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. lia. }
  destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq.
  + replace (SHADOW_OFF + (8 * k + 4)) with (lc_SH cx + 4) by (rewrite ESH; ring). exact (HS 4 ltac:(lia)).
  + replace (SHADOW_OFF + (8 * k + 5)) with (lc_SH cx + 5) by (rewrite ESH; ring). exact (HS 5 ltac:(lia)).
  + replace (SHADOW_OFF + (8 * k + 6)) with (lc_SH cx + 6) by (rewrite ESH; ring). exact (HS 6 ltac:(lia)).
- intros s Hs. unfold shadow_addr in Hs.
  assert (Hy1 : (lc_F cx + 32) / 8 = 8 * k + 4).
  { pose proof (Z.div_mod (lc_F cx + 32) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (lc_F cx + 32) 8 ltac:(lia)). lia. }
  assert (Hy2 : 8 * k + 4 <= (lc_F cx + 32 + n - 1) / 8 <= 8 * k + 6).
  { pose proof (Z.div_mod (lc_F cx + 32 + n - 1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (lc_F cx + 32 + n - 1) 8 ltac:(lia)). lia. }
  rewrite Hy1 in Hs. unfold SHADOW_OFF in *.
  assert (Hz1 : (2147450880 + (8 * k + 4)) / 8 = 268431360 + k).
  { pose proof (Z.div_mod (2147450880 + (8 * k + 4)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (8 * k + 4)) 8 ltac:(lia)). lia. }
  assert (Hz2 : (2147450880 + (lc_F cx + 32 + n - 1) / 8) / 8 = 268431360 + k).
  { pose proof (Z.div_mod (2147450880 + (lc_F cx + 32 + n - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (lc_F cx + 32 + n - 1) / 8) 8 ltac:(lia)). lia. }
  rewrite Hz1, Hz2 in Hs.
  replace s with (lc_SH cx + (s - lc_SH cx)) by ring.
  rewrite (HS (s - lc_SH cx) ltac:(rewrite ESH; lia)). discriminate.
Qed.

End mach.

(* A spill slot of the loop holds its value. *)
Lemma o4_spill_get : forall {rc : YM05.RunCeil} cx (r : reader) o v,
  lc_spills cx (lf_spill_loop (lc_F cx)) r -> In (o, v) (lf_spill_loop (lc_F cx)) -> rdword r (lc_sp1 cx + o) = Some v.
Proof. intros rc cx r o v H Hin. unfold lc_spills in H. rewrite Forall_forall in H. exact (H (o, v) Hin). Qed.

Ltac o4_in := unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app];
  repeat (first [left; reflexivity | right]).

(* The low atoms of a run's valuation are those of E0. *)
Ltac o4_low HS E0 HEX :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  end.

(* The value of register r in the machine state of a symbolic state HS, as v. *)
Ltac o4_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

Lemma o4_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. rewrite Ha, Z.add_0_r in Da.
rewrite Zminus_mod, Hb. rewrite Da. replace (32 * (a / 32)) with ((2 * (a / 32)) * 16) by ring.
rewrite Z_mod_mult. reflexivity.
Qed.

(* Register r of a PI state becomes the fresh atom j, and atom j + 1 takes the value v. *)
Ltac o4_genv HS r j v :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss ?ms =>
    let H := fresh "HSg" in
    pose proof (o4_gen Ex ss ms r j v HS eq_refl ltac:(vm_compute; reflexivity)) as H;
    clear HS; rename H into HS
  end.

(* Register r of a PI state becomes the fresh atom j. *)
Ltac o4_genl HS r j :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss ?ms =>
    let H := fresh "HSg" in
    pose proof (o4_gen Ex ss ms r j (Z_to_bv 64 0) HS eq_refl ltac:(vm_compute; reflexivity)) as H;
    clear HS; rename H into HS
  end.

(* Compute a PI state's symbolic part. *)
Ltac o4_norm HS :=
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* The value of register r of a PI state over a restricted machine state, its symbolic value computed. *)
Ltac o4_regq HS H E r Q :=
  lazymatch type of HS with st_ok_pi _ _ _ ?s (restrict _ ?m) =>
    pose proof (st_ok_pi_restrict_reg H E s m r HS) as Q end;
  lazymatch type of Q with _ = sv_denot _ ?ee => let e' := eval vm_compute in ee in change ee with e' in Q end.

Section seg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* What the walk keeps of the CMDW memory, from "every byte not of G and not of the callee's window": the core's
   four kept facts (lc_core_kept's) and the spill slots and frame shadow. *)
Lemma o4_kept3 : forall cx ly' S' (W' : world segs) regs' mem' md' e (mF : word -> option byte) (X : Z),
  lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e -> AR_laws segs B -> 0 <= X <= 4096 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W') mF a = aview segs (w_H W') mem' a) ->
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W') mF a = aview segs (w_H W') mem' a) /\
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W') mF (b + i) = aview segs (w_H W') mem' (b + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') mF a = aview segs (w_H W') mem' a) /\
  (forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') mF a = aview segs (w_H W') mem' a).
Proof.
intros cx ly' S' W' regs' mem' md' e mF X HB HC LAWS HX K.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hnl Hinb Hlive].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & HFal & HFceil & _).
destruct Hstk as (Hs1 & Hs2 & Hs3 & Hs4). destruct Hsp1 as [Hsp1a Hsp1b].
pose proof YM05.alloc_ceiling_value as Hce.
unfold LF_FBYTES, LF_FRAME in *.
assert (GL : forall a, inG TG.G_HARNESS a -> 0 <= a < 2147450880).
{ intros a Ha. pose proof (transport_segs_low a (trans_g_img a Ha)) as H. unfold kLowMemEnd in H. lia. }
assert (HSH : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= YM05.alloc_ceiling).
{ unfold lc_SH. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)) as D0.
  assert (D1 : lc_F cx / 8 <= lc_F cx) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF. lia. }
split; [|split; [|split]].
- intros a Ha Hw. apply K; [lia | intros HG; pose proof (GL a HG); lia | exact Hw].
- intros b m i Hb Hi. destruct (al_blocks _ _ LAWS ly' S' W' mem' md' b m HAR Hb) as (_ & H4096 & Hbc & _).
  apply K; [lia | | lia].
  intros HG. exact (blk_img segs B LAWS ly' S' W' mem' md' b m (b + i) HAR Hb ltac:(lia) (trans_g_img _ HG)).
- intros a [Ha|Ha].
  + apply K; [lia | | lia]. intros HG.
    apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin); [|exact (trans_g_img _ HG)].
    rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
  + apply K; [unfold SHADOW_OFF in HSH; lia | intros HG; pose proof (GL a HG); unfold SHADOW_OFF in HSH; lia | lia].
- intros a [Ha|Ha].
  + apply K; [lia | intros HG; pose proof (GL a HG); lia | lia].
  + apply K; [unfold SHADOW_OFF in HSH; lia | intros HG; pose proof (GL a HG); unfold SHADOW_OFF in HSH; lia | lia].
Qed.

(* The S4 cut from the CMDW cut's loop facts at the final registers and memory: the core at the final memory
   (lc_core_kept at the CMDW registers), the spill slots and the frame's shadow kept, the callee-saved registers the cut
   fixes kept, s3 / s7 the cursor after the take, s4 = g_fail_next's page, the model's world and equations. *)
Lemma o4_close : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e regs2 mem2 md2 Bw c5
    (pcv : word),
  pcv = w64 (transport_text + LO_S4) ->
  lc_lcore B MT cx op true false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_core B cx ly' S' W' regs' mem2 md2 e ->
  (forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 26]%bv -> YK11.getr regs2 r = YK11.getr regs' r) ->
  lc_cur cx regs2 19 23 c5 -> YK11.getr regs2 20 = w64 LF_S4 ->
  lc_opc (l_pl cx) (lo_c op) = 4 ->
  lc_tw W' mem2 Bw -> TC.settle_m Bw 0 = Some (Bw, tt) ->
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_A (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
     Some (Bw, (c5, lo_k op))) ->
  lc_st_s4 B MT cx op W' (mkCfg (@YK11.mkst (l_fx cx) regs2 pcv mem2 (YK11.seg_rom segs)) md2).
Proof.
intros cx op ly' S' W' regs' mem' md' e regs2 mem2 md2 Bw c5 pcv Hpc HL HC2 KM KR HCUR R20 Hopc HTW HSET HOP.
subst pcv.
destruct HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFceil & _).
pose proof YM05.alloc_ceiling_value as Hce.
exists ly', S', regs2, mem2, md2, e, Bw, c5.
split; [reflexivity|]. split; [exact Hopc|].
split.
{ split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - unfold lc_core in HC2 |- *.
    rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
      (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)).
    exact HC2.
  - destruct HFR as (R18 & R26). split.
    + rewrite (KR 18%bv ltac:(cbn; tauto)). exact R18.
    + rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26.
  - eapply lc_spills_kept; [| | exact HSP].
    + intros o Ho. unfold LF_FBYTES in HFceil.
      pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as V.
      rewrite Forall_forall in V. destruct (V o Ho) as (_ & _ & H8 & H192). lia.
    + intros a Ha. apply KM. left. exact Ha.
  - eapply lc_fsh_kept; [| exact HFSH]. intros a Ha. apply KM. right. exact Ha.
  - exact HOK.
  - exact He.
  - exact HMT.
  - rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21. }
split; [exact HTW|]. split; [exact HSET|]. split; [exact HOP|]. split; [exact HCUR | exact R20].
Qed.

(* The registers the segment keeps across __asan_memcpy are callee-saved. *)
Lemma o4_cs : forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] -> acallee_saved r.
Proof.
intros r Hr. unfold acallee_saved. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [lia|]). destruct Hr.
Qed.

(* The S4 cut from the CMDW cut's loop facts, the journal at the final memory and "every byte that is not of G and not
   of the ESTACK window below sp1 is kept". *)
Lemma o4_closeG : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e regsF mF mdF Bf c5
    (pcv : word),
  lc_base B MT XL RLO RHI cx -> AR_laws segs B ->
  pcv = w64 (transport_text + LO_S4) ->
  lc_lcore B MT cx op true false (lo_k op) ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' mF mdF e ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
     aview segs (w_H W') mF a = aview segs (w_H W') mem' a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 26]%bv -> YK11.getr regsF r = YK11.getr regs' r) ->
  lc_cur cx regsF 19 23 c5 -> YK11.getr regsF 20 = w64 LF_S4 ->
  lc_opc (l_pl cx) (lo_c op) = 4 ->
  lc_tw W' mF Bf -> TC.settle_m Bf 0 = Some (Bf, tt) ->
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_A (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
     Some (Bf, (c5, lo_k op))) ->
  lc_st_s4 B MT cx op W' (mkCfg (@YK11.mkst (l_fx cx) regsF pcv mF (YK11.seg_rom segs)) mdF).
Proof.
intros cx op ly' S' W' regs' mem' md' e regsF mF mdF Bf c5 pcv HB LAWS Hpc HL HJF K KR HCUR R20 Hopc HTW HSET HOP.
pose proof HL as (HC0 & _).
destruct (o4_kept3 cx ly' S' W' regs' mem' md' e mF 4096 HB HC0 LAWS ltac:(lia) K) as (KA & KB & KF & KM).
pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e 4096 ly' S' W' regs' mF mdF e
  LAWS HB HC0 HJF eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia) KA KB KF) as HC2.
exact (o4_close cx op ly' S' W' regs' mem' md' e regsF mF mdF Bf c5 pcv Hpc HL HC2 KM KR HCUR R20 Hopc HTW HSET HOP).
Qed.

(* want = SPEC_OK: the replace (at >= 0) or the append (at < 0). *)
Lemma o4_b6_rep : forall B5 Bw want at_ s, want = 0 -> 0 <= at_ ->
  o4_b6 B5 Bw want at_ s = TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s.
Proof.
intros B5 Bw want at_ s H Ha. unfold o4_b6, DSpec.SPEC_OK. rewrite H, Z.eqb_refl.
rewrite (proj2 (Z.leb_le 0 at_) Ha). reflexivity.
Qed.
Lemma o4_b6_app : forall B5 Bw want at_ s, want = 0 -> at_ < 0 ->
  o4_b6 B5 Bw want at_ s = TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32).
Proof.
intros B5 Bw want at_ s H Ha. unfold o4_b6, DSpec.SPEC_OK. rewrite H, Z.eqb_refl.
rewrite (proj2 (Z.leb_gt 0 at_) Ha). reflexivity.
Qed.

(* want <> SPEC_OK keeps B5. *)
Lemma o4_b6_skip : forall B5 Bw want at_ s, want <> 0 -> o4_b6 B5 Bw want at_ s = B5.
Proof. intros B5 Bw want at_ s H. unfold o4_b6, DSpec.SPEC_OK. rewrite (proj2 (Z.eqb_neq want 0) H). reflexivity. Qed.

(* The frame lies in the application's low or high memory. *)
Lemma o4_F_range : forall cx ly S W regs mem md e, AR_laws segs B -> lc_base B MT XL RLO RHI cx ->
  lc_core B cx ly S W regs mem md e -> lc_F cx + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= lc_F cx.
Proof.
intros cx ly S W regs mem md e LAWS HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as G.
destruct G as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof asan_consts as ((C1 & C2) & _).
destruct (frames_bounds segs B LAWS ly S W mem md LF_CID (l_fpos cx) HAR HFin) as (F1 & F2 & F3).
rewrite HFaddr in F1, F2, F3. rewrite lf_fbytes in F2, F3. unfold LF_FBYTES in F2, F3.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
lia.
Qed.

(* c's 32 bytes are present. *)
Lemma o4_c_some : forall (H : word -> bool) (m : word -> option byte) (c : Z) (cb : list byte) (len disp key : Z),
  garr8 segs (mrestrict H m) c (TW.zs (TOP.cmd_struct cb len disp key)) -> length cb = 24%nat ->
  forall i, 0 <= i < 32 -> aview segs H m (c + i) <> None.
Proof.
intros H m c cb len disp key HG Hcb i Hi.
assert (HL : length (TW.zs (TOP.cmd_struct cb len disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hcb, TWL.length_put. reflexivity. }
pose proof (proj1 (HG (Z.to_nat i) ltac:(rewrite HL; lia))) as V.
rewrite Z2Nat.id in V by lia.
pose proof (o4_aview_of_val H m (c + i) 1 _ 0%nat V ltac:(lia)) as A.
cbn [Z.of_nat] in A. rewrite Z.add_0_r in A. rewrite A. discriminate.
Qed.

(* c's first 24 bytes are cb's. *)
Lemma o4_c_byte : forall (H : word -> bool) (m : word -> option byte) (c : Z) (cb : list byte) (len disp key : Z),
  garr8 segs (mrestrict H m) c (TW.zs (TOP.cmd_struct cb len disp key)) -> length cb = 24%nat ->
  forall i, 0 <= i < 24 -> aview segs H m (c + i) = Some (bv_unsigned (nth (Z.to_nat i) cb (Z_to_bv 8 0))).
Proof.
intros H m c cb len disp key HG Hcb i Hi.
assert (HL : length (TW.zs (TOP.cmd_struct cb len disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hcb, TWL.length_put. reflexivity. }
pose proof (proj1 (HG (Z.to_nat i) ltac:(rewrite HL; lia))) as V.
rewrite Z2Nat.id in V by lia.
pose proof (o4_aview_of_val H m (c + i) 1 _ 0%nat V ltac:(lia)) as A.
cbn [Z.of_nat] in A. rewrite Z.add_0_r in A. rewrite A. f_equal.
assert (HN : nth (Z.to_nat i) (TW.zs (TOP.cmd_struct cb len disp key)) 0 =
  bv_unsigned (nth (Z.to_nat i) cb (Z_to_bv 8 0))).
{ unfold TW.zs, TOP.cmd_struct.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, !length_app, Hcb, TWL.length_put; cbn; lia).
  rewrite map_nth. rewrite app_nth1 by (rewrite Hcb; lia). reflexivity. }
rewrite HN. apply tw_le_byte1. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) cb (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.

(* The cells the runs after __asan_memcpy may write: g_nq and g_ncmd; with g_q[i] (the append); with g_q[i] and
   g_cmd[q].st (the replace). *)
Definition o4_Z2 (x : Z) : Prop := TA_g_nq <= x < TA_g_nq + 4 \/ TA_g_ncmd <= x < TA_g_ncmd + 4.
Definition o4_Z3 (i x : Z) : Prop := o4_Z2 x \/ TA_g_q + 4 * i <= x < TA_g_q + 4 * i + 4.
Definition o4_Z4 (i q x : Z) : Prop := o4_Z3 i x \/ TA_g_cmd + 40 * q <= x < TA_g_cmd + 40 * q + 4.

Lemma o4_Z4_G : forall i q x, 0 <= i < 1024 -> 0 <= q < 1024 -> o4_Z4 i q x -> inG TG.G_HARNESS x.
Proof.
intros i q x Hi Hq [[[H|H]|H]|H].
- apply o4_inG_nq. exact H.
- apply o4_inG_ncmd. exact H.
- apply o4_inG_q. lia.
- apply o4_inG_cmd. lia.
Qed.

Lemma o4_cs20 : acallee_saved 20.
Proof. unfold acallee_saved. lia. Qed.

(* What a run keeps: every byte outside the cells Zs (the run's windows lie in Zs). *)
Ltac o4_keep K E Zs :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict ?H ?m) (mrestrict _ ?m') |- _ =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs H m' a = aview tfibsegs H m a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let HnZ := fresh "HnZ" in
      intros a Ha HnZ; apply (kept_of_frame E _ H m m' Zs HFr); [| exact Ha | exact HnZ];
      let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hin := fresh "Hin" in let Hx := fresh "Hx" in
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx;
         try (match goal with U : bv_unsigned (ew _ 3000%nat) = _ |- _ => rewrite U in Hx end);
         try (match goal with U : bv_unsigned (ew _ 3002%nat) = _ |- _ => rewrite U in Hx end);
         clear - Hx; unfold o4_Z4, o4_Z3, o4_Z2, TA_g_nq, TA_g_ncmd in *; lia |]);
      destruct Hin
    | clear HFr ]
  end.

(* After __asan_memcpy (+0x121c) to S4: the branch on at, then the append (g_nq + 1, g_q[old g_nq] = serial) or the
   replace (g_cmd[g_q[at]].st = REPLACED, g_q[at] = serial), and g_ncmd + 1. *)
Lemma o4_lt64 : forall a, 0 <= a < 2147450880 -> 0 <= a < 2 ^ 64.
Proof. intros a H. lia. Qed.

Lemma o4_tail : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e regs3 mem3 md3
    (B5 Bw : list byte) (at_ sn key disp len n0 : Z) (c4 c5 : TOP.fuzz_in),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op true false (lo_k op) ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' mem3 md3 e ->
  lc_opc (l_pl cx) (lo_c op) = 4 ->
  (forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
     YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  YK11.getr regs3 (Z_to_bv 5 20) = w64 LF_S4 ->
  YK11.getr regs' 19 = w64 (at_ mod 2 ^ 32) ->
  YK11.getr regs' 24 = w64 (l_p cx + TOP.fi_off c4) -> YK11.getr regs' 25 = w64 n0 ->
  YK11.getr regs' 27 = w64 (TA_g_cmd + 40 * sn) ->
  TOP.fi_off c5 = TOP.fi_off c4 + n0 -> TOP.fi_n c5 = TOP.fi_n c4 - n0 ->
  (forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') mem3 a = aview segs (w_H W') mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
     aview segs (w_H W') mem3 a = aview segs (w_H W') mem' a) ->
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 56) = Some (TOP.fi_n c4) ->
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some TA_g_cmd ->
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 72) = Some sn ->
  0 <= sn < 1024 -> 0 <= key < 2 ^ 32 -> 0 <= disp < 256 -> 0 <= len < 256 ->
  (at_ = -1 \/ 0 <= at_ < 1024) ->
  lc_tw W' mem3 Bw ->
  (0 <= at_ -> 0 <= TW.Q_at Bw at_ < 1024) -> (at_ < 0 -> 0 <= TW.g_nq Bw < 1024) ->
  TC.settle_m (o4_b7 (o4_b6 B5 Bw 0 at_ sn)) 0 = Some (o4_b7 (o4_b6 B5 Bw 0 at_ sn), tt) ->
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_A (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
     Some (o4_b7 (o4_b6 B5 Bw 0 at_ sn), (c5, lo_k op))) ->
  SRr segs W' (mkCfg (@YK11.mkst (l_fx cx) regs3 (Z_to_bv 64 (BASE + LO_RCPY)) mem3 (YK11.seg_rom segs)) md3)
    (lc_st_s4 B MT cx op).
Proof.
intros cx op ly' S' W' regs' mem' md' e regs3 mem3 md3 B5 Bw at_ sn key disp len n0 c4 c5 HP HB HL HJ3 Hopc KR3 R20c
  R19 R24 R25 R27 Hoff5 Hfi5 KS3 KM3 S56 S64 S72 Hs Hkey Hdisp' Hlen HATR' HTW3 Hrep Happ HSET HOP.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_settle_cells B MT XL RLO RHI HP) as HSC.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC0 & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC0) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hnl Hinb Hlive].
pose proof HC0 as (HJ & Hfrs & HlyF & HPERM & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HFR as (R18 & R26).
pose proof YM05.alloc_ceiling_value as Hce.
unfold LF_FBYTES in HFceil.
destruct Hstk as (Hstk1 & Hstk2 & Hstk3 & Hstk4).
assert (Hsp1b : YM05.alloc_ceiling + 32432 <= lc_sp1 cx <= 2 ^ 47 - 320)
  by (unfold LF_FRAME in Hsp1; destruct Hsp1 as [Hsp1a Hsp1b']; split; [exact Hsp1c | lia]).
assert (EST : ESTACK = 4096) by reflexivity.
assert (GL : forall a, inG TG.G_HARNESS a -> 0 <= a < 2147450880).
{ intros a Ha. pose proof (transport_segs_low a (trans_g_img a Ha)) as H. unfold kLowMemEnd in H. lia. }
pose proof (o4_rdword_range _ _ _ _ S56) as Hfin.
pose proof (@paj_run_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
  assert (HSP3 : lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W') mem3)).
  { apply (lc_spills_kept cx _ (aview segs (w_H W') mem') (aview segs (w_H W') mem3)); [| | exact HSP].
    - intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(clear - HF4096 HFceil Hce; unfold LF_FBYTES in *; lia)
        ltac:(clear - HF4096 HFceil Hce; unfold LF_FBYTES in *; lia)) as V.
      rewrite Forall_forall in V. destruct (V o Ho) as (_ & _ & V3 & V4). clear - V3 V4. lia.
    - intros a Ha. apply KS3. left. exact Ha. }
  pose proof (o4_spill_get cx _ 24 (transport_hi 14) HSP3 ltac:(o4_in)) as S24c.
  pose proof (o4_spill_get cx _ 80 (transport_hi 15) HSP3 ltac:(o4_in)) as S80c.
  pose proof (o4_spill_get cx _ 160 (transport_hi 10) HSP3 ltac:(o4_in)) as S160c.
  pose proof (o4_spill_get cx _ 168 (lc_F cx + 32) HSP3 ltac:(o4_in)) as S168c.
  assert (S56c : rdword (aview segs (w_H W') mem3) (lc_sp1 cx + 56) = Some (TOP.fi_n c4)).
  { rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem3) (lc_sp1 cx + 56))
      by (intros j Hj; apply KS3; left; clear - Hj; lia). exact S56. }
  assert (S64c : rdword (aview segs (w_H W') mem3) (lc_sp1 cx + 64) = Some TA_g_cmd).
  { rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem3) (lc_sp1 cx + 64))
      by (intros j Hj; apply KS3; left; clear - Hj; lia). exact S64. }
  assert (S72c : rdword (aview segs (w_H W') mem3) (lc_sp1 cx + 72) = Some sn).
  { rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem3) (lc_sp1 cx + 72))
      by (intros j Hj; apply KS3; left; clear - Hj; lia). exact S72. }
  pose proof (tw_read_val segs (mrestrict (w_H W') mem3) TMAP_A Bw TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 4
    TMAP_A_ok HTW3 TMAP_A_g_ncmd (Z.le_refl 0) ltac:(unfold TW.SZ_g_ncmd; clear - Hs; lia)) as V38c.
  rewrite !Z.add_0_r in V38c.
  pose proof (tw_read_val segs (mrestrict (w_H W') mem3) TMAP_A Bw TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4
    TMAP_A_ok HTW3 TMAP_A_g_nq (Z.le_refl 0) ltac:(unfold TW.SZ_g_nq; clear - Hs; lia)) as V39c.
  rewrite !Z.add_0_r in V39c.
  pose proof (TWL.u_at_range Bw TW.OFF_g_ncmd 4) as Hncmd3. change (8 * Z.of_nat 4) with 32 in Hncmd3.
  pose proof (TWL.u_at_range Bw TW.OFF_g_nq 4) as Hnq3. change (8 * Z.of_nat 4) with 32 in Hnq3.
  assert (R2c : YK11.getr regs3 2 = w64 (lc_sp1 cx)) by exact (eq_trans (KR3 2 ltac:(cbn; tauto)) R2).
  assert (R9c : YK11.getr regs3 9 = w64 (lc_sp1 cx)) by exact (eq_trans (KR3 9 ltac:(cbn; tauto)) R9).
  assert (R26c : YK11.getr regs3 26 = w64 SHADOW_OFF) by exact (eq_trans (KR3 26 ltac:(cbn; tauto)) R26).
  assert (R27c : YK11.getr regs3 27 = w64 (TA_g_cmd + 40 * sn))
    by exact (eq_trans (KR3 27 ltac:(cbn; tauto)) R27).
  pose proof (o4_entry2 (fx := l_fx cx) W' regs3 mem3 (lc_sp1 cx) (lc_F cx) sn (TOP.fi_n c4)
    key disp len (TW.u_at Bw TW.OFF_g_ncmd 4) (TW.u_at Bw TW.OFF_g_nq 4)
    R2c R9c R26c R27c Hsp1b Hsp1al HF4096 HFal HFceil Hs Hfin Hkey Hdisp' ltac:(clear - Hlen; lia) Hncmd3 Hnq3
    S24c S56c S64c S72c S80c S160c S168c ltac:(rewrite Z.add_0_l; exact V38c) ltac:(rewrite Z.add_0_l; exact V39c))
    as HS2.
  set (E2 := o4_E1 regs3 (lc_F cx) sn (TOP.fi_n c4) key disp len
    (TW.u_at Bw TW.OFF_g_ncmd 4) (TW.u_at Bw TW.OFF_g_nq 4)) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, o4_E1; apply Eimg_env).
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regs3 r)
    by (intros n r Hn'; unfold E2, o4_E1; apply ew_Eimg_Ereg_nat; exact Hn').
  assert (SHOK2 : sh_ok segs O4_Bx [] E2 (mrestrict (w_H W') mem3)) by constructor.
  unfold LO_RCPY in HS2 |- *.
  (* run C, +0x121c ..: `sext.w a0, s3; bltz a0` *)
  paj_run_tok RUN HS2 HJ3 SHOK2 YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (first
      [ apply awr_ok_x_cons_g;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
          first [apply o4_inG_ncmd; clear - Ha; unfold TA_g_ncmd in *; lia
                | apply o4_inG_nq; clear - Ha; unfold TA_g_nq in *; lia] |]
      | apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia |] ]).
    apply awr_ok_x_nil. }
  o4_keep KC E2 o4_Z2.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  assert (E19 : ew E2 19 = w64 (at_ mod 2 ^ 32)).
  { rewrite (EE2 19%nat (Z_to_bv 5 19) eq_refl), (KR3 19 ltac:(cbn; tauto)). exact R19. }
  assert (EX2 : forall j, (j < 8)%nat -> ew E2 (32 + j) = nth j (o4_extra (lc_F cx) sn
      (TOP.fi_n c4) key disp len (TW.u_at Bw TW.OFF_g_ncmd 4)
      (TW.u_at Bw TW.OFF_g_nq 4)) (Z_to_bv 64 0))
    by (intros j Hj; unfold E2, o4_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX2 1%nat ltac:(lia)) as F33. pose proof (EX2 2%nat ltac:(lia)) as F34.
  pose proof (EX2 6%nat ltac:(lia)) as F38. pose proof (EX2 7%nat ltac:(lia)) as F39.
  cbn [Nat.add nth o4_extra] in F33, F34, F38, F39. clear EX2.
  assert (U39c : bv_unsigned (ew E2 39) = TW.g_nq Bw)
    by (rewrite F39; unfold w64; apply unsigned_lit_small; unfold TW.g_nq; clear - Hnq3; lia).
  assert (U38c : bv_unsigned (ew E2 38) = TW.g_ncmd Bw)
    by (rewrite F38; unfold w64; apply unsigned_lit_small; unfold TW.g_ncmd; clear - Hncmd3; lia).
  assert (U33c : bv_unsigned (ew E2 33) = sn)
    by (rewrite F33; unfold w64; apply unsigned_lit_small; clear - Hs; lia).
  assert (U9c : bv_unsigned (ew E2 9) = lc_sp1 cx)
    by (rewrite (EE2 9%nat 9%bv eq_refl), R9c; unfold w64; apply unsigned_lit_small; clear - Hsp1b Hce; lia).
  assert (U26c : ew E2 26 = w64 SHADOW_OFF) by (rewrite (EE2 26%nat 26%bv eq_refl); exact R26c).
  pose proof HSC as (_ & _ & HZq & _).
  psrr_branch_tok RUN BR HS2 SHOK2 YC4b.Bspan.
  + (* at < 0: the append *)
    rewrite (o4_br_at E2 at_ E19 HATR') in Hc. apply Z.ltb_lt in Hc. rename Hc into Hat0.
    paj_run_to_tok RUNTO HS2 HJ3 SHOK2 YC4b.Bspan 0x1294.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (first
        [ apply awr_ok_x_cons_g;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
            first [apply o4_inG_ncmd; clear - Ha; unfold TA_g_ncmd in *; lia
                  | apply o4_inG_nq; clear - Ha; unfold TA_g_nq in *; lia] |]
        | apply awr_ok_x_cons;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia |] ]).
      apply awr_ok_x_nil. }
    o4_keep KP1 E2 o4_Z2.
    pose proof (Happ Hat0) as Hnqb.
    o4_regq HS2 (w_H W') E2 (Z_to_bv 5 10) Q10.
    rewrite (o4_den_gq E2 39 (TW.g_nq Bw) U39c Hnqb HEI2) in Q10.
    o4_genl HS2 (Z_to_bv 5 10) 3000%nat.
    lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ => set (E3 := Ex) in HS2 end.
    assert (HEX3 : forall n, (n < 1024)%nat -> ew E3 n = ew E2 n)
      by (intros n Hn; unfold E3; rewrite !ew_ewset_other by lia; reflexivity).
    assert (HEIq : img_env VAL A_LIM E3)
      by (intros n Hn; rewrite HEX3 by (unfold A_TEXT, A_LIM in *; lia); exact (HEI2 n Hn)).
    assert (U3000 : bv_unsigned (ew E3 3000) = TA_g_q + 4 * TW.g_nq Bw).
    { unfold E3. rewrite ew_ewset_other by lia. rewrite ew_ewset_same. cbn [ms_regs restrict]. rewrite Q10. unfold w64.
      apply unsigned_lit_small. clear - Hnqb. unfold TA_g_q. lia. }
    o4_norm HS2.
    pose proof (st_ok_pi_add_fact (PI := PI_transport) E3 _ _ 3000%nat (mkAF TA_g_q (TA_g_q + 4092) 2) HS2
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U3000; clear - Hnqb; unfold TA_g_q;
            repeat split; lia)) as HS3.
    clear HS2. o4_norm HS3.
    lazymatch type of HS3 with st_ok_pi _ _ _ ?s _ =>
      assert (Hdis : all_disjoint E3 (YP09.mkRegion (Some 3000%nat) 0 4 0 4 []) (ss_mem s)) end.
    { cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U3000, (HEX3 9%nat ltac:(lia)), U9c.
      clear - Hnqb Hsp1b Hce. unfold TA_g_q. repeat split; lia. }
    pose proof (st_ok_pi_add_region (PI := PI_transport) E3 _ _ (YP09.mkRegion (Some 3000%nat) 0 4 0 4 []) HS3
      ltac:(vm_compute; reflexivity)
      (o4_rgw_ok E3 _ 3000 (TA_g_q + 4 * TW.g_nq Bw) 0 4 U3000 ltac:(clear - Hnqb; unfold TA_g_q; lia)
         ltac:(clear - Hnqb; unfold TA_g_q; lia) ltac:(clear - Hnqb; lia)
         ltac:(intros o Ho; apply o4_inG_q; clear - Hnqb Ho; lia))
      Hdis) as HS4.
    clear HS3 Hdis. o4_norm HS4.
    pose proof HJ3 as (_ & _ & (memSc & HJdc & _) & _). pose proof HJdc as (HARc & _).
    destruct (o4_q_blk (TW.g_nq Bw) Hnqb) as [Hq1 Hq2].
    lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
      assert (SHOK3 : sh_ok segs O4_Bx [mkSHE 3000 0 4] E3 (mrestrict (w_H W') (ms_mem m))) end.
    { unfold sh_ok. constructor; [|constructor].
      apply (o4_she B ly' S' W' _ _ E3 3000 (TA_g_q + 4 * TW.g_nq Bw) 0 4 TA_g_q (TA_g_q + TW.SZ_g_q) HARc HZq).
      - unfold U, O4_Bx. cbn [sv_denot]. rewrite (HEX3 26%nat ltac:(lia)), U26c, Z.add_0_r, Z_to_bv_bv_unsigned.
        unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
      - unfold U. cbn [sv_denot]. rewrite U3000, Z.add_0_r. apply unsigned_lit_small.
        clear - Hnqb. unfold TA_g_q. lia.
      - clear - Hnqb; lia.
      - exact Hq1.
      - unfold TW.SZ_g_q. exact Hq2.
      - clear - Hnqb. unfold TA_g_q. lia.
      - clear - Hnqb. unfold TA_g_q, SHADOW_OFF. lia. }
    clear SHOK2.
    (* run P2, +0x1294 .. S4: the checked store of g_q[old g_nq], g_ncmd + 1 *)
    paj_run_to_tok RUNTO HS4 HJ3 SHOK3 YC4b.Bspan LO_S4.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (first
        [ apply awr_ok_x_cons_g;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
            first [apply o4_inG_ncmd; clear - Ha; unfold TA_g_ncmd in *; lia
                  | apply o4_inG_nq; clear - Ha; unfold TA_g_nq in *; lia
                  | rewrite U3000 in Ha; apply o4_inG_q; clear - Ha Hnqb; lia] |]
        | apply awr_ok_x_cons;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia |] ]).
      apply awr_ok_x_nil. }
    o4_keep KP2 E3 (o4_Z3 (TW.g_nq Bw)).
    lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => set (E4 := Ex) in HS4 end.
    assert (HEX4 : forall n, (n < 1024 \/ n = 3000)%nat -> ew E4 n = ew E3 n)
      by (intros n Hn; unfold E4; repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia;
          reflexivity).
    (* the stored cells, from the run's last state *)
    assert (U33q : bv_unsigned (ew E4 33) = sn) by (rewrite HEX4, HEX3 by lia; exact U33c).
    assert (U38q : bv_unsigned (ew E4 38) = TW.g_ncmd Bw) by (rewrite HEX4, HEX3 by lia; exact U38c).
    assert (U39q : bv_unsigned (ew E4 39) = TW.g_nq Bw) by (rewrite HEX4, HEX3 by lia; exact U39c).
    o4_norm HS4.
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 0 _ HS4 eq_refl) as RGq.
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 2 _ HS4 eq_refl) as RGn.
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 3 _ HS4 eq_refl) as RGv.
    cbn [ms_mem restrict] in RGq, RGn, RGv.
    destruct RGq as (_ & _ & _ & RGq). destruct RGn as (_ & _ & _ & RGn). destruct RGv as (_ & _ & _ & RGv).
    cbn [YP09.r_chunks YP09.r_base base_val] in RGq, RGn, RGv.
    rewrite (HEX4 3000%nat ltac:(lia)), U3000 in RGq.
    apply Forall_inv in RGq. apply Forall_inv in RGn. apply Forall_inv in RGv.
    lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (Wq : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem m) (TA_g_q + 4 * TW.g_nq Bw + Z.of_nat j) =
      Some (YO0f.le_byte sn 4 j));
    [ intros j Hj;
      pose proof (o4_den_off E4 33 sn 4 0 U33q ltac:(lia)) as Hd; rewrite Z.add_0_r in Hd;
      pose proof (o4_chunk_bytes E4 (w_H W') (ms_mem m) _ 0 4 4 _ sn RGq eq_refl ltac:(lia) Hd j Hj) as Hb;
      rewrite Z.add_0_r in Hb; exact Hb
    | assert (Wn : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem m) (TA_g_ncmd + Z.of_nat j) =
        Some (YO0f.le_byte (TW.g_ncmd Bw + 1) 4 j));
      [ intros j Hj;
        replace (TA_g_ncmd + Z.of_nat j) with (0 + 6158720 + Z.of_nat j) by (unfold TA_g_ncmd; lia);
        exact (o4_chunk_bytes E4 (w_H W') (ms_mem m) _ _ 4 4 _ (TW.g_ncmd Bw + 1) RGn eq_refl ltac:(lia)
          (o4_den_inc E4 38 (TW.g_ncmd Bw) U38q) j Hj)
      | assert (Wv : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem m) (TA_g_nq + Z.of_nat j) =
          Some (YO0f.le_byte (TW.g_nq Bw + 1) 4 j));
        [ intros j Hj;
          replace (TA_g_nq + Z.of_nat j) with (0 + 6158688 + Z.of_nat j) by (unfold TA_g_nq; lia);
          exact (o4_chunk_bytes E4 (w_H W') (ms_mem m) _ _ 4 4 _ (TW.g_nq Bw + 1) RGv eq_refl ltac:(lia)
            (o4_den_off E4 39 (TW.g_nq Bw) 4 1 U39q ltac:(lia)) j Hj)
        | ] ] ] end.
    lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (Woth2 : forall x, tw_in TMAP_A x -> ~ (TA_g_nq <= x < TA_g_nq + 4) ->
      ~ (TA_g_q + 4 * TW.g_nq Bw <= x < TA_g_q + 4 * TW.g_nq Bw + 4) -> ~ (TA_g_ncmd <= x < TA_g_ncmd + 4) ->
      aview segs (w_H W') (ms_mem m) x = aview segs (w_H W') mem3 x) end.
    { intros x Hx H1 H2 H3. pose proof (GL x (ios_tw_in_G x Hx)) as Hl.
      pose proof (o4_lt64 x Hl) as Hl64.
      assert (HnZ3 : ~ o4_Z3 (TW.g_nq Bw) x) by (clear - H1 H2 H3; unfold o4_Z3, o4_Z2; tauto).
      assert (HnZ2 : ~ o4_Z2 x) by (clear - H1 H3; unfold o4_Z2; tauto).
      etransitivity; [exact (KP2 x Hl64 HnZ3)|].
      etransitivity; [exact (KP1 x Hl64 HnZ2)|].
      exact (KC x Hl64 HnZ2). }
    pose proof (o4_w_app Bw (aview segs (w_H W') mem3) _ sn HTW3 Hnqb Wv Wq Wn Woth2) as HTWF.
    lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
      aview segs (w_H W') (ms_mem m) a = aview segs (w_H W') mem' a) end.
    { intros a Ha HnG Hw.
      assert (HnZ3 : ~ o4_Z3 (TW.g_nq Bw) a)
        by (intros Hz; apply HnG; apply (o4_Z4_G (TW.g_nq Bw) 0 a Hnqb ltac:(lia)); left; exact Hz).
      assert (HnZ2 : ~ o4_Z2 a) by (intros Hz; apply HnZ3; left; exact Hz).
      etransitivity; [exact (KP2 a Ha HnZ3)|]. etransitivity; [exact (KP1 a Ha HnZ2)|].
      etransitivity; [exact (KC a Ha HnZ2)|]. exact (KM3 a Ha HnG Hw). }
    lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (KRF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 26]%bv -> YK11.getr (ms_regs m) r = YK11.getr regs' r);
    [ intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W') E4 _ m r HS4); cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr];
        [ lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
          cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEX4, HEX3 by lia;
          lazymatch goal with |- ew E2 ?n = YK11.getr regs' ?rr =>
            rewrite (EE2 n rr eq_refl); exact (KR3 (Z.of_nat n) ltac:(cbn; tauto)) end |]);
      destruct Hr
    | assert (R19F : YK11.getr (ms_regs m) (Z_to_bv 5 19) = w64 (l_p cx + TOP.fi_off c5));
      [ rewrite (st_ok_pi_restrict_reg (w_H W') E4 _ m _ HS4);
        lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
        rewrite (o4_den_add E4 24 25 (l_p cx + TOP.fi_off c4) n0);
        [ rewrite Hoff5; f_equal; ring
        | rewrite HEX4, HEX3 by lia; rewrite (EE2 24%nat (Z_to_bv 5 24) eq_refl), (KR3 24 ltac:(cbn; tauto)); exact R24
        | rewrite HEX4, HEX3 by lia; rewrite (EE2 25%nat (Z_to_bv 5 25) eq_refl), (KR3 25 ltac:(cbn; tauto)); exact R25 ]
      | assert (R23F : YK11.getr (ms_regs m) (Z_to_bv 5 23) = w64 (TOP.fi_n c5));
        [ rewrite (st_ok_pi_restrict_reg (w_H W') E4 _ m _ HS4);
          lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
          rewrite (o4_den_sub E4 34 25 (TOP.fi_n c4) n0);
          [ rewrite Hfi5; reflexivity
          | rewrite HEX4, HEX3 by lia; exact F34
          | rewrite HEX4, HEX3 by lia; rewrite (EE2 25%nat (Z_to_bv 5 25) eq_refl), (KR3 25 ltac:(cbn; tauto)); exact R25 ]
        | assert (R20F : YK11.getr (ms_regs m) (Z_to_bv 5 20) = w64 LF_S4);
          [ rewrite (st_ok_pi_restrict_reg (w_H W') E4 _ m _ HS4);
            lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
            cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEX4, HEX3 by lia;
            rewrite (EE2 20%nat (Z_to_bv 5 20) eq_refl); exact R20c
          | ] ] ] ] end.
    rewrite (o4_b6_app B5 Bw 0 at_ sn eq_refl Hat0) in HSET, HOP.
    pmkst HS4.
    apply SRr_ret.
    refine (o4_closeG cx op ly' S' W' regs' mem' md' e _ _ _ _ c5 _ HB LAWS _ HL HJ3 KF KRF
      (conj R19F R23F) R20F Hopc HTWF HSET HOP).
    vm_compute. reflexivity.
  + (* at >= 0: the replace *)
    rewrite (o4_br_at E2 at_ E19 HATR') in Hc. apply Z.ltb_ge in Hc. rename Hc into Hat0.
    paj_run_to_tok RUNTO HS2 HJ3 SHOK2 YC4b.Bspan 0x1234.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (first
        [ apply awr_ok_x_cons_g;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
            first [apply o4_inG_ncmd; clear - Ha; unfold TA_g_ncmd in *; lia
                  | apply o4_inG_nq; clear - Ha; unfold TA_g_nq in *; lia] |]
        | apply awr_ok_x_cons;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia |] ]).
      apply awr_ok_x_nil. }
    o4_keep KQ1 E2 o4_Z2.
    pose proof (Hrep Hat0) as Hq.
    assert (Hat1 : 0 <= at_ < 1024) by (destruct HATR' as [H|H]; [clear - H Hat0; lia | exact H]).
    assert (U19c : bv_unsigned (ew E2 19) = at_).
    { rewrite E19. unfold w64. rewrite (Z.mod_small at_ (2 ^ 32)) by (clear - Hat1; lia).
      apply unsigned_lit_small. clear - Hat1. lia. }
    o4_regq HS2 (w_H W') E2 (Z_to_bv 5 10) Q10.
    rewrite (o4_den_gq E2 19 at_ U19c Hat1 HEI2) in Q10.
    o4_genv HS2 (Z_to_bv 5 10) 3000%nat (w64 (TW.Q_at Bw at_)).
    lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ => set (E3 := Ex) in HS2 end.
    assert (HEX3 : forall n, (n < 1024)%nat -> ew E3 n = ew E2 n)
      by (intros n Hn; unfold E3; rewrite !ew_ewset_other by lia; reflexivity).
    assert (HEIq : img_env VAL A_LIM E3)
      by (intros n Hn; rewrite HEX3 by (unfold A_TEXT, A_LIM in *; lia); exact (HEI2 n Hn)).
    assert (U3000 : bv_unsigned (ew E3 3000) = TA_g_q + 4 * at_).
    { unfold E3. rewrite ew_ewset_other by lia. rewrite ew_ewset_same. cbn [ms_regs restrict]. rewrite Q10. unfold w64.
      apply unsigned_lit_small. clear - Hat1. unfold TA_g_q. lia. }
    assert (U3001 : bv_unsigned (ew E3 3001) = TW.Q_at Bw at_).
    { unfold E3. rewrite ew_ewset_same. unfold w64. apply unsigned_lit_small. clear - Hq. lia. }
    o4_norm HS2.
    pose proof (st_ok_pi_add_fact (PI := PI_transport) E3 _ _ 3000%nat (mkAF TA_g_q (TA_g_q + 4092) 2) HS2
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U3000; clear - Hat1; unfold TA_g_q;
            repeat split; lia)) as HS3.
    clear HS2. o4_norm HS3.
    pose proof (st_ok_pi_add_fact (PI := PI_transport) E3 _ _ 3001%nat (mkAF 0 1023 0) HS3
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U3001; clear - Hq; repeat split; lia)) as HS2.
    clear HS3. o4_norm HS2.
    (* g_q[at]'s bytes at the run's memory *)
    pose proof (tw_read_val segs (mrestrict (w_H W') mem3) TMAP_A Bw TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * at_) 4
      TMAP_A_ok HTW3 TMAP_A_g_q ltac:(clear - Hat1; lia) ltac:(unfold TW.SZ_g_q; clear - Hat1; lia)) as Vq.
    lazymatch type of HS2 with st_ok_pi _ _ _ ?s (restrict _ ?m) =>
      assert (Vq' : YI04.val_mem segs (mrestrict (w_H W') (ms_mem m)) (TA_g_q + 4 * at_ + 0) 4 (TW.Q_at Bw at_));
      [ rewrite Z.add_0_r; apply (o4_val_mem_xfer (w_H W') mem3 (ms_mem m)); [|exact Vq];
        intros kk Hkk;
        assert (HnZ : ~ o4_Z2 (TA_g_q + 4 * at_ + Z.of_nat kk))
          by (clear - Hat1 Hkk; unfold o4_Z2, TA_g_q, TA_g_nq, TA_g_ncmd; lia);
        etransitivity;
          [exact (KQ1 (TA_g_q + 4 * at_ + Z.of_nat kk) ltac:(clear - Hat1 Hkk; unfold TA_g_q; lia) HnZ)|];
        exact (KC (TA_g_q + 4 * at_ + Z.of_nat kk) ltac:(clear - Hat1 Hkk; unfold TA_g_q; lia) HnZ)
      | assert (Hdis : all_disjoint E3 (YP09.mkRegion (Some 3000%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 3001 0))])
          (ss_mem s)) ] end.
    { cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U3000, (HEX3 9%nat ltac:(lia)), U9c.
      clear - Hat1 Hsp1b Hce. unfold TA_g_q. repeat split; lia. }
    pose proof (st_ok_pi_add_region (PI := PI_transport) E3 _ _
      (YP09.mkRegion (Some 3000%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 3001 0))]) HS2
      ltac:(vm_compute; reflexivity)
      (o4_rgc_ok E3 _ 3000 3001 (TA_g_q + 4 * at_) (TW.Q_at Bw at_) U3000 U3001 ltac:(clear - Hq; lia)
         ltac:(clear - Hat1; unfold TA_g_q; lia) ltac:(clear - Hat1; unfold TA_g_q; lia)
         ltac:(intros o Ho; apply o4_inG_q; clear - Hat1 Ho; lia) Vq')
      Hdis) as HS4.
    clear HS2 Hdis. o4_norm HS4.
    pose proof HJ3 as (_ & _ & (memSc & HJdc & _) & _). pose proof HJdc as (HARc & _).
    destruct (o4_q_blk at_ Hat1) as [Hq1 Hq2].
    lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
      assert (SHOK3 : sh_ok segs O4_Bx [mkSHE 3000 0 4] E3 (mrestrict (w_H W') (ms_mem m))) end.
    { unfold sh_ok. constructor; [|constructor].
      apply (o4_she B ly' S' W' _ _ E3 3000 (TA_g_q + 4 * at_) 0 4 TA_g_q (TA_g_q + TW.SZ_g_q) HARc HZq).
      - unfold U, O4_Bx. cbn [sv_denot]. rewrite (HEX3 26%nat ltac:(lia)), U26c, Z.add_0_r, Z_to_bv_bv_unsigned.
        unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
      - unfold U. cbn [sv_denot]. rewrite U3000, Z.add_0_r. apply unsigned_lit_small.
        clear - Hat1. unfold TA_g_q. lia.
      - clear - Hat1; lia.
      - exact Hq1.
      - unfold TW.SZ_g_q. exact Hq2.
      - clear - Hat1. unfold TA_g_q. lia.
      - clear - Hat1. unfold TA_g_q, SHADOW_OFF. lia. }
    clear SHOK2.
    (* run R2, +0x1234 .. +0x1258: the checked load of g_q[at], g_cmd + 40 g_q[at] *)
    paj_run_to_tok RUNTO HS4 HJ3 SHOK3 YC4b.Bspan 0x1258.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (first
        [ apply awr_ok_x_cons_g;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
            first [apply o4_inG_ncmd; clear - Ha; unfold TA_g_ncmd in *; lia
                  | apply o4_inG_nq; clear - Ha; unfold TA_g_nq in *; lia
                  | rewrite U3000 in Ha; apply o4_inG_q; clear - Ha Hat1; lia] |]
        | apply awr_ok_x_cons;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia |] ]).
      apply awr_ok_x_nil. }
    o4_keep KQ2 E3 (o4_Z3 at_).
    lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => set (E4 := Ex) in HS4 end.
    lazymatch goal with Hi : img_env _ _ E4 |- _ => rename Hi into HEI4 | _ => idtac end.
    assert (HEX4 : forall n, (n < 1024 \/ n = 3000 \/ n = 3001)%nat -> ew E4 n = ew E3 n)
      by (intros n Hn; unfold E4; clear - Hn; repeat rewrite ew_ewset_other by lia; reflexivity).
    assert (U3001d : bv_unsigned (ew E4 3001) = TW.Q_at Bw at_) by (rewrite HEX4 by lia; exact U3001).
    o4_regq HS4 (w_H W') E4 (Z_to_bv 5 11) Q11.
    rewrite (o4_den_gc E4 3001 (TW.Q_at Bw at_) U3001d Hq) in Q11.
    o4_genl HS4 (Z_to_bv 5 11) 3010%nat.
    lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => set (E5 := Ex) in HS4 end.
    assert (HEX5 : forall n, (n < 1024 \/ n = 3000 \/ n = 3001)%nat -> ew E5 n = ew E3 n)
      by (intros n Hn; unfold E5, E4; clear - Hn; repeat rewrite ew_ewset_other by lia; reflexivity).
    assert (HEI5 : img_env VAL A_LIM E5)
      by (intros n Hn; rewrite HEX5 by (unfold A_TEXT, A_LIM in *; lia); exact (HEIq n Hn)).
    assert (U3010 : bv_unsigned (ew E5 3010) = TA_g_cmd + 40 * TW.Q_at Bw at_).
    { unfold E5. rewrite ew_ewset_other by lia. rewrite ew_ewset_same. cbn [ms_regs restrict]. rewrite Q11. unfold w64.
      apply unsigned_lit_small. clear - Hq. unfold TA_g_cmd. lia. }
    assert (U3000e : bv_unsigned (ew E5 3000) = TA_g_q + 4 * at_) by (rewrite HEX5 by lia; exact U3000).
    o4_norm HS4.
    pose proof (st_ok_pi_add_fact (PI := PI_transport) E5 _ _ 3010%nat (mkAF TA_g_cmd (TA_g_cmd + 40 * 1023) 3) HS4
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U3010; clear - Hq; unfold TA_g_cmd;
            repeat split; lia)) as HS5.
    clear HS4. o4_norm HS5.
    lazymatch type of HS5 with st_ok_pi _ _ _ ?s _ =>
      assert (Hdis : all_disjoint E5 (YP09.mkRegion (Some 3010%nat) 0 4 0 4 []) (ss_mem s)) end.
    { cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U3010, U3000e, (HEX5 9%nat ltac:(lia)), (HEX3 9%nat ltac:(lia)), U9c.
      clear - Hat1 Hq Hsp1b Hce. unfold TA_g_q, TA_g_cmd. repeat split; lia. }
    pose proof (st_ok_pi_add_region (PI := PI_transport) E5 _ _ (YP09.mkRegion (Some 3010%nat) 0 4 0 4 []) HS5
      ltac:(vm_compute; reflexivity)
      (o4_rgw_ok E5 _ 3010 (TA_g_cmd + 40 * TW.Q_at Bw at_) 0 4 U3010 ltac:(clear - Hq; unfold TA_g_cmd; lia)
         ltac:(clear - Hq; unfold TA_g_cmd; lia) ltac:(clear - Hq; lia)
         ltac:(intros o Ho; apply o4_inG_cmd; clear - Hq Ho; lia))
      Hdis) as HS6.
    clear HS5 Hdis. o4_norm HS6.
    pose proof HJ3 as (_ & _ & (memSd & HJdd & _) & _). pose proof HJdd as (HARd & _).
    pose proof HSC as (_ & _ & _ & HZc).
    destruct (o4_cmd_blk (TW.Q_at Bw at_) 0 4 Hq ltac:(lia) ltac:(lia)) as [Hk1 Hk2].
    lazymatch type of HS6 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
      assert (SHOK4 : sh_ok segs O4_Bx [mkSHE 3010 0 4] E5 (mrestrict (w_H W') (ms_mem m))) end.
    { unfold sh_ok. constructor; [|constructor].
      apply (o4_she B ly' S' W' _ _ E5 3010 (TA_g_cmd + 40 * TW.Q_at Bw at_) 0 4 TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd)
        HARd HZc).
      - unfold U, O4_Bx. cbn [sv_denot]. rewrite (HEX5 26%nat ltac:(lia)), (HEX3 26%nat ltac:(lia)), U26c, Z.add_0_r,
          Z_to_bv_bv_unsigned.
        unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
      - unfold U. cbn [sv_denot]. rewrite U3010, Z.add_0_r. apply unsigned_lit_small.
        clear - Hq. unfold TA_g_cmd. lia.
      - clear - Hq; lia.
      - exact Hk1.
      - unfold TW.SZ_g_cmd. exact Hk2.
      - clear - Hq. unfold TA_g_cmd. lia.
      - clear - Hq. unfold TA_g_cmd, SHADOW_OFF. lia. }
    clear SHOK3.
    (* run R3, +0x1258 .. S4: the checked store g_cmd[g_q[at]].st = REPLACED, g_q[at] = serial, g_ncmd + 1 *)
    paj_run_to_tok RUNTO HS6 HJ3 SHOK4 YC4b.Bspan LO_S4.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (first
        [ apply awr_ok_x_cons_g;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
            first [apply o4_inG_ncmd; clear - Ha; unfold TA_g_ncmd in *; lia
                  | apply o4_inG_nq; clear - Ha; unfold TA_g_nq in *; lia
                  | rewrite U3000e in Ha; apply o4_inG_q; clear - Ha Hat1; lia
                  | rewrite U3010 in Ha; apply o4_inG_cmd; clear - Ha Hq; lia] |]
        | apply awr_ok_x_cons;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; clear - Ha; lia |] ]).
      apply awr_ok_x_nil. }
    lazymatch goal with HFr : frame_of _ _ (mrestrict ?Hh ?mA) (mrestrict _ ?mB) |- _ =>
      assert (KQall : forall a, 0 <= a < 2 ^ 64 -> ~ o4_Z4 at_ (TW.Q_at Bw at_) a ->
        aview segs Hh mB a = aview segs (w_H W') mem3 a);
      [ intros a Ha HnZ4;
        assert (HnZ3 : ~ o4_Z3 at_ a) by (intros Hz; apply HnZ4; left; exact Hz);
        assert (HnZ2 : ~ o4_Z2 a) by (intros Hz; apply HnZ3; left; exact Hz);
        etransitivity;
        [ apply (kept_of_frame E5 _ Hh mA mB (o4_Z4 at_ (TW.Q_at Bw at_)) HFr); [| exact Ha | exact HnZ4];
          intros b wlo whi x Hin Hx;
          lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
          cbn [In] in Hin;
          repeat (destruct Hin as [Hin | Hin];
            [injection Hin as <- <- <-; cbn [base_val] in Hx; try rewrite U3000e in Hx; try rewrite U3010 in Hx;
             clear - Hx; unfold o4_Z4, o4_Z3, o4_Z2, TA_g_nq, TA_g_ncmd in *; lia |]);
          destruct Hin |];
        etransitivity; [exact (KQ2 a Ha HnZ3)|];
        etransitivity; [exact (KQ1 a Ha HnZ2)|]; exact (KC a Ha HnZ2)
      | clear HFr ] end.
    lazymatch type of HS6 with st_ok_pi _ _ ?Ex _ _ => set (E6 := Ex) in HS6 end.
    assert (HEX6 : forall n, (n < 1024 \/ n = 3000 \/ n = 3001 \/ n = 3010)%nat -> ew E6 n = ew E5 n)
      by (intros n Hn; unfold E6; clear - Hn; repeat rewrite ew_ewset_other by lia; reflexivity).
    assert (U33f : bv_unsigned (ew E6 33) = sn)
      by (rewrite HEX6, HEX5, HEX3 by lia; exact U33c).
    assert (U38f : bv_unsigned (ew E6 38) = TW.g_ncmd Bw)
      by (rewrite HEX6, HEX5, HEX3 by lia; exact U38c).
    assert (U39f : bv_unsigned (ew E6 39) = TW.g_nq Bw)
      by (rewrite HEX6, HEX5, HEX3 by lia; exact U39c).
    assert (U3000f : bv_unsigned (ew E6 3000) = TA_g_q + 4 * at_) by (rewrite HEX6 by lia; exact U3000e).
    assert (U3010f : bv_unsigned (ew E6 3010) = TA_g_cmd + 40 * TW.Q_at Bw at_) by (rewrite HEX6 by lia; exact U3010).
    o4_norm HS6.
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 0 _ HS6 eq_refl) as RGk.
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 1 _ HS6 eq_refl) as RGq.
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 3 _ HS6 eq_refl) as RGn.
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 4 _ HS6 eq_refl) as RGv.
    cbn [ms_mem restrict] in RGk, RGq, RGn, RGv.
    destruct RGk as (_ & _ & _ & RGk). destruct RGq as (_ & _ & _ & RGq).
    destruct RGn as (_ & _ & _ & RGn). destruct RGv as (_ & _ & _ & RGv).
    cbn [YP09.r_chunks YP09.r_base base_val] in RGk, RGq, RGn, RGv.
    rewrite U3010f in RGk. rewrite U3000f in RGq.
    apply Forall_inv in RGk. apply Forall_inv in RGq. apply Forall_inv in RGn. apply Forall_inv in RGv.
    lazymatch type of HS6 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (Wk : forall j, (j < 4)%nat ->
      aview segs (w_H W') (ms_mem m) (TA_g_cmd + 40 * TW.Q_at Bw at_ + Z.of_nat j) = Some (YO0f.le_byte 3 4 j));
    [ intros j Hj;
      pose proof (o4_chunk_bytes E6 (w_H W') (ms_mem m) _ 0 4 4 (SLit 3) 3 RGk eq_refl ltac:(lia)
        (o4_den_lit E6 3 4 ltac:(lia)) j Hj) as Hb;
      rewrite Z.add_0_r in Hb; exact Hb
    | assert (Wq : forall j, (j < 4)%nat ->
        aview segs (w_H W') (ms_mem m) (TA_g_q + 4 * at_ + Z.of_nat j) = Some (YO0f.le_byte sn 4 j));
      [ intros j Hj;
        pose proof (o4_den_off E6 33 sn 4 0 U33f ltac:(lia)) as Hd; rewrite Z.add_0_r in Hd;
        pose proof (o4_chunk_bytes E6 (w_H W') (ms_mem m) _ 0 4 4 _ sn RGq eq_refl ltac:(lia) Hd j Hj) as Hb;
        rewrite Z.add_0_r in Hb; exact Hb
      | assert (Wn : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem m) (TA_g_ncmd + Z.of_nat j) =
          Some (YO0f.le_byte (TW.g_ncmd Bw + 1) 4 j));
        [ intros j Hj;
          replace (TA_g_ncmd + Z.of_nat j) with (0 + 6158720 + Z.of_nat j) by (unfold TA_g_ncmd; lia);
          exact (o4_chunk_bytes E6 (w_H W') (ms_mem m) _ _ 4 4 _ (TW.g_ncmd Bw + 1) RGn eq_refl ltac:(lia)
            (o4_den_inc E6 38 (TW.g_ncmd Bw) U38f) j Hj)
        | assert (Wv : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem m) (TA_g_nq + Z.of_nat j) =
            Some (YO0f.le_byte (TW.g_nq Bw) 4 j));
          [ intros j Hj;
            pose proof (o4_den_off E6 39 (TW.g_nq Bw) 4 0 U39f ltac:(lia)) as Hd0;
            rewrite Z.add_0_r in Hd0;
            replace (TA_g_nq + Z.of_nat j) with (0 + 6158688 + Z.of_nat j) by (unfold TA_g_nq; lia);
            exact (o4_chunk_bytes E6 (w_H W') (ms_mem m) _ _ 4 4 _ (TW.g_nq Bw) RGv eq_refl ltac:(lia) Hd0 j Hj)
          | ] ] ] ] end.
    (* g_nq's bytes are the same at mem3 *)
    pose proof (tw_read_val segs (mrestrict (w_H W') mem3) TMAP_A Bw TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4
      TMAP_A_ok HTW3 TMAP_A_g_nq (Z.le_refl 0) ltac:(unfold TW.SZ_g_nq; clear - Hs; lia)) as V39d.
    rewrite !Z.add_0_r in V39d.
    assert (Wv0 : forall j, (j < 4)%nat ->
      aview segs (w_H W') mem3 (TA_g_nq + Z.of_nat j) = Some (YO0f.le_byte (TW.g_nq Bw) 4 j))
      by (intros j Hj; exact (o4_aview_of_val (w_H W') mem3 TA_g_nq 4 _ j V39d Hj)).
    lazymatch type of HS6 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (Woth3 : forall x, tw_in TMAP_A x ->
      ~ (TA_g_cmd + 40 * TW.Q_at Bw at_ <= x < TA_g_cmd + 40 * TW.Q_at Bw at_ + 4) ->
      ~ (TA_g_q + 4 * at_ <= x < TA_g_q + 4 * at_ + 4) -> ~ (TA_g_ncmd <= x < TA_g_ncmd + 4) ->
      aview segs (w_H W') (ms_mem m) x = aview segs (w_H W') mem3 x) end.
    { intros xx Hxq H1 H2 H3. pose proof (GL xx (ios_tw_in_G xx Hxq)) as Hl.
      pose proof (o4_lt64 xx Hl) as Hl64.
      destruct (Z_le_gt_dec TA_g_nq xx) as [Hq1b|Hq1b]; [destruct (Z_lt_ge_dec xx (TA_g_nq + 4)) as [Hq2b|Hq2b]|].
      - replace xx with (TA_g_nq + Z.of_nat (Z.to_nat (xx - TA_g_nq))) by (clear - Hq1b Hq2b; lia).
        rewrite (Wv (Z.to_nat (xx - TA_g_nq)) ltac:(clear - Hq1b Hq2b; lia)),
          (Wv0 (Z.to_nat (xx - TA_g_nq)) ltac:(clear - Hq1b Hq2b; lia)). reflexivity.
      - assert (HnZ4 : ~ o4_Z4 at_ (TW.Q_at Bw at_) xx).
        { intros [[[Hz|Hz]|Hz]|Hz];
            [clear - Hz Hq2b; unfold TA_g_nq in *; lia | exact (H3 Hz) | exact (H2 Hz) | exact (H1 Hz)]. }
        assert (HnZ3 : ~ o4_Z3 at_ xx) by (intros Hz; apply HnZ4; left; exact Hz).
        assert (HnZ2 : ~ o4_Z2 xx) by (intros Hz; apply HnZ3; left; exact Hz).
        exact (KQall xx Hl64 HnZ4).
      - assert (HnZ4 : ~ o4_Z4 at_ (TW.Q_at Bw at_) xx).
        { intros [[[Hz|Hz]|Hz]|Hz];
            [clear - Hz Hq1b; unfold TA_g_nq in *; lia | exact (H3 Hz) | exact (H2 Hz) | exact (H1 Hz)]. }
        assert (HnZ3 : ~ o4_Z3 at_ xx) by (intros Hz; apply HnZ4; left; exact Hz).
        assert (HnZ2 : ~ o4_Z2 xx) by (intros Hz; apply HnZ3; left; exact Hz).
        exact (KQall xx Hl64 HnZ4). }
    pose proof (o4_w_rep Bw (aview segs (w_H W') mem3) _ at_ sn HTW3 Hat1 Hq Wk Wq Wn Woth3) as HTWF.
    lazymatch type of HS6 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
      aview segs (w_H W') (ms_mem m) a = aview segs (w_H W') mem' a) end.
    { intros a Ha HnG Hw.
      assert (HnZ4 : ~ o4_Z4 at_ (TW.Q_at Bw at_) a)
        by (intros Hz; apply HnG; exact (o4_Z4_G at_ (TW.Q_at Bw at_) a Hat1 Hq Hz)).
      assert (HnZ3 : ~ o4_Z3 at_ a) by (intros Hz; apply HnZ4; left; exact Hz).
      assert (HnZ2 : ~ o4_Z2 a) by (intros Hz; apply HnZ3; left; exact Hz).
      etransitivity; [exact (KQall a Ha HnZ4)|]. exact (KM3 a Ha HnG Hw). }
    lazymatch type of HS6 with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    assert (KRF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 26]%bv -> YK11.getr (ms_regs m) r = YK11.getr regs' r);
    [ intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W') E6 _ m r HS6); cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr];
        [ lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
          cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEX6, HEX5, HEX3 by lia;
          lazymatch goal with |- ew E2 ?n = YK11.getr regs' ?rr =>
            rewrite (EE2 n rr eq_refl); exact (KR3 (Z.of_nat n) ltac:(cbn; tauto)) end |]);
      destruct Hr
    | assert (R19F : YK11.getr (ms_regs m) (Z_to_bv 5 19) = w64 (l_p cx + TOP.fi_off c5));
      [ rewrite (st_ok_pi_restrict_reg (w_H W') E6 _ m _ HS6);
        lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
        rewrite (o4_den_add E6 24 25 (l_p cx + TOP.fi_off c4) n0);
        [ rewrite Hoff5; f_equal; ring
        | rewrite HEX6, HEX5, HEX3 by lia; rewrite (EE2 24%nat (Z_to_bv 5 24) eq_refl), (KR3 24 ltac:(cbn; tauto)); exact R24
        | rewrite HEX6, HEX5, HEX3 by lia; rewrite (EE2 25%nat (Z_to_bv 5 25) eq_refl), (KR3 25 ltac:(cbn; tauto)); exact R25 ]
      | assert (R23F : YK11.getr (ms_regs m) (Z_to_bv 5 23) = w64 (TOP.fi_n c5));
        [ rewrite (st_ok_pi_restrict_reg (w_H W') E6 _ m _ HS6);
          lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
          rewrite (o4_den_sub E6 34 25 (TOP.fi_n c4) n0);
          [ rewrite Hfi5; reflexivity
          | rewrite HEX6, HEX5, HEX3 by lia; exact F34
          | rewrite HEX6, HEX5, HEX3 by lia; rewrite (EE2 25%nat (Z_to_bv 5 25) eq_refl), (KR3 25 ltac:(cbn; tauto));
            exact R25 ]
        | assert (R20F : YK11.getr (ms_regs m) (Z_to_bv 5 20) = w64 LF_S4);
          [ rewrite (st_ok_pi_restrict_reg (w_H W') E6 _ m _ HS6);
            lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
            cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEX6, HEX5, HEX3 by lia;
            rewrite (EE2 20%nat (Z_to_bv 5 20) eq_refl); exact R20c
          | ] ] ] ] end.
    rewrite (o4_b6_rep B5 Bw 0 at_ sn eq_refl Hat0) in HSET, HOP.
    pmkst HS6.
    apply SRr_ret.
    refine (o4_closeG cx op ly' S' W' regs' mem' md' e _ _ _ _ c5 _ HB LAWS _ HL HJ3 KF KRF
      (conj R19F R23F) R20F Hopc HTWF HSET HOP).
    vm_compute. reflexivity.
Qed.

Lemma lc_op4st_ok : lc_op4st_stmt B MT XL RLO RHI.
Proof.
intros HP cx op W' c' HB HCW.
destruct HCW as (ly' & S' & regs' & mem' & md' & e & B1 & at_ & B3 & rc0 & B4 & B5 & HCW).
cbv zeta in HCW.
destruct HCW as (-> & Hopc & HL & HOB & HRAW & Hser & HAT & HSUB & HREF & HLAT & HTW & HCS & S56 & S64 & S72 &
  R22 & R19 & R24 & R25 & R27).
pose proof HL as (HC0 & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof HOK as (HAG & Hops & HFI & Hfin0 & Hk).
pose proof (o4_model (l_pl cx) (lo_B op) B1 B3 B4 B5 (lo_c op) (lo_k op) (lo_ops op) at_ rc0 HAG Hops HFI Hfin0 Hopc
  HOB HRAW Hser HAT HSUB HREF HLAT) as HM.
cbv zeta in HM.
pose proof (o4_tag_facts (l_pl cx) B1 (lo_c op) HFI) as HTF. cbv zeta in HTF.
pose proof (o4_kd_facts (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) as HKD.
pose proof (o4_at_range _ _ _ HAT) as HATR.
pose proof (o4_want_cases (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) at_)
  as HWC.
set (kd := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) in *.
set (tv := lc_tag_vals (l_pl cx) B1 (sv_c kd)) in *.
set (want := lc_want tv at_) in *.
destruct HTF as (Hlen & Hcb & Hntk & Hoff4 & Hfi4 & Hn4 & Hoff5 & Hfi5).
destruct HKD as (Hkey & Hdisp).
destruct HM as (HMrep & HMapp & HSET & HOP).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_settle_cells B MT XL RLO RHI HP) as HSC.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC0) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hnl Hinb Hlive].
pose proof HC0 as (HJ & Hfrs & HlyF & HPERM & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HFR as (R18 & R26).
pose proof YM05.alloc_ceiling_value as Hce.
assert (Hs : 0 <= tg_serial tv < 1024) by (unfold TC.CMDS_MAX in Hser; lia).
pose proof (o4_spill_get cx _ 24 (transport_hi 14) HSP ltac:(o4_in)) as S24.
pose proof (o4_spill_get cx _ 80 (transport_hi 15) HSP ltac:(o4_in)) as S80.
pose proof (o4_spill_get cx _ 160 (transport_hi 10) HSP ltac:(o4_in)) as S160.
pose proof (o4_spill_get cx _ 168 (lc_F cx + 32) HSP ltac:(o4_in)) as S168.
pose proof (o4_c_vals _ (lc_F cx + 32) (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd) HCS Hcb
  ltac:(lia) ltac:(destruct Hdisp as [Hd|Hd]; rewrite Hd; lia)) as (Vlen & Vdisp & Vkey).
pose proof (o4_rdword_range _ _ _ _ S56) as Hfin.
pose proof (TWL.u_at_range B5 TW.OFF_g_ncmd 4) as Hncmd. change (8 * Z.of_nat 4) with 32 in Hncmd.
pose proof (TWL.u_at_range B5 TW.OFF_g_nq 4) as Hnq. change (8 * Z.of_nat 4) with 32 in Hnq.
unfold LF_FBYTES in HFceil.
destruct Hstk as (Hstk1 & Hstk2 & Hstk3 & Hstk4).
assert (Hsp1b : YM05.alloc_ceiling + 32432 <= lc_sp1 cx <= 2 ^ 47 - 320)
  by (unfold LF_FRAME in Hsp1; destruct Hsp1 as [Hsp1a Hsp1b']; split; [exact Hsp1c | lia]).
pose proof (o4_entry1 (fx := l_fx cx) W' regs' mem' (lc_sp1 cx) (lc_F cx) (tg_serial tv) (TOP.fi_n (tg_c4 tv))
  (sv_key kd) (sv_display kd) (tg_len tv) (TW.u_at B5 TW.OFF_g_ncmd 4) (TW.u_at B5 TW.OFF_g_nq 4)
  R2 R9 R26 R27 Hsp1b Hsp1al HF4096 HFal HFceil Hs Hfin Hkey
  ltac:(destruct Hdisp as [Hd|Hd]; rewrite Hd; lia) ltac:(lia) Hncmd Hnq S24 S56 S64 S72 S80 S160 S168
  Vlen Vdisp Vkey) as HS.
set (E1 := o4_E1 regs' (lc_F cx) (tg_serial tv) (TOP.fi_n (tg_c4 tv)) (sv_key kd) (sv_display kd) (tg_len tv)
  (TW.u_at B5 TW.OFF_g_ncmd 4) (TW.u_at B5 TW.OFF_g_nq 4)) in HS.
assert (HEI : img_env VAL A_LIM E1) by (unfold E1, o4_E1; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr regs' r)
  by (intros n r Hn'; unfold E1, o4_E1; apply ew_Eimg_Ereg_nat; exact Hn').
pose proof (o4_shok1 B ly' S' W' mem' md' E1 (tg_serial tv) HSC HAR Hs
  ltac:(rewrite (EE 27%nat 27%bv eq_refl); exact R27) ltac:(rewrite (EE 26%nat 26%bv eq_refl); exact R26)) as SHOK.
pose proof (@paj_run_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
unfold lc_cfg.
replace (w64 (transport_text + LO_CMDW)) with (Z_to_bv 64 (BASE + LO_CMDW)) by (rewrite (proj2 o4_vals); reflexivity).
(* run 1, +0x119c .. +0x11a0: s4 = 160(s1), `bnez s6` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
(* the frame is no byte of G *)
assert (HFG : forall x, lc_F cx <= x < lc_F cx + 256 -> ~ inG TG.G_HARNESS x).
{ intros x Hx HGx. apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) x HAR HFin);
    [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | exact (trans_g_img _ HGx)]. }
assert (EX : forall j, (j < 8)%nat -> ew E1 (32 + j) =
  nth j (o4_extra (lc_F cx) (tg_serial tv) (TOP.fi_n (tg_c4 tv)) (sv_key kd) (sv_display kd) (tg_len tv)
    (TW.u_at B5 TW.OFF_g_ncmd 4) (TW.u_at B5 TW.OFF_g_nq 4)) (Z_to_bv 64 0))
  by (intros j Hj; unfold E1, o4_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U9 : bv_unsigned (ew E1 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
cbn [Nat.add nth o4_extra] in E32, E33, E34, E35, E36, E37, E38, E39. clear EX.
assert (U32 : bv_unsigned (ew E1 32) = lc_F cx + 32) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E1 38) = TW.u_at B5 TW.OFF_g_ncmd 4)
  by (rewrite E38; unfold w64; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E1 39) = TW.u_at B5 TW.OFF_g_nq 4)
  by (rewrite E39; unfold w64; apply unsigned_lit_small; lia).
assert (E22 : ew E1 22 = w64 want) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (HWC' : want = 0 \/ want = -10 \/ want = -5)
  by (unfold DSpec.SPEC_OK, DSpec.SPEC_E_REFUSED, DSpec.SPEC_E_SPACE in HWC; exact HWC).
(* the memory of run 1 is the CMDW memory (no window) *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. apply (kept_of_frame E1 _ (w_H W') mem' (ms_mem ms) (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
  destruct Hin. }
set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
clear HF HFr HG.
assert (GL : forall a, inG TG.G_HARNESS a -> 0 <= a < 2147450880).
{ intros a Ha. pose proof (transport_segs_low a (trans_g_img a Ha)) as H. unfold kLowMemEnd in H. lia. }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* want <> SPEC_OK: g_ncmd + 1 only *)
  rewrite (o4_br_want E1 want E22 HWC') in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hw0.
  assert (V38 : YI04.val_mem segs (mrestrict (w_H W') (ms_mem ms)) (0 + TA_g_ncmd) 4 (TW.u_at B5 TW.OFF_g_ncmd 4)).
  { apply (o4_val_mem_xfer (w_H W') mem' (ms_mem ms)); [intros kk Hkk; apply K1; unfold TA_g_ncmd; lia|].
    pose proof (tw_read_val segs (mrestrict (w_H W') mem') TMAP_A B5 TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 4
      TMAP_A_ok HTW TMAP_A_g_ncmd ltac:(lia) ltac:(unfold TW.SZ_g_ncmd; lia)) as V.
    rewrite !Z.add_0_r in V. rewrite Z.add_0_l. exact V. }
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    assert (Hdis : all_disjoint E1 o4_rg_ncmd (ss_mem s)) end.
  { cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_ncmd.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    pose proof (o4_apart (lc_F cx) TA_g_ncmd 4 HFG o4_inG_ncmd ltac:(lia)) as Hap.
    unfold TA_g_ncmd in *. split; [lia | split; [lia | exact I]]. }
  pose proof (st_ok_pi_add_region (PI := PI_transport) E1 _ _ o4_rg_ncmd HS ltac:(vm_compute; reflexivity)
    (o4_rgabs_ok E1 _ 38 TA_g_ncmd _ U38 Hncmd ltac:(unfold TA_g_ncmd; lia) ltac:(unfold TA_g_ncmd; lia)
       o4_inG_ncmd V38) Hdis) as HS2.
  clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  assert (SHOK2 : sh_ok segs O4_Bx [] E1 (mrestrict (w_H W') (ms_mem ms))) by constructor.
  clear SHOK. rename SHOK2 into SHOK.
  (* run A, +0x12ac .. +0x12c8: g_ncmd + 1, s3, s7 *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_S4.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. apply o4_inG_ncmd. unfold TA_g_ncmd. lia. }
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  (* only g_ncmd's 4 bytes changed in run A *)
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_g_ncmd <= a < TA_g_ncmd + 4) ->
    aview segs (w_H W') (ms_mem ms0) a = aview segs (w_H W') mem' a).
  { intros a Ha Hn. rewrite <- (K1 a Ha).
    apply (kept_of_frame E1 _ (w_H W') (ms_mem ms) (ms_mem ms0) (fun x => TA_g_ncmd <= x < TA_g_ncmd + 4) HFr);
      [|exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; cbv beta;
      unfold TA_g_ncmd; lia |]).
    destruct Hin. }
  (* the 4 bytes of g_ncmd + 1 *)
  pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 0 _ HS eq_refl) as RG.
  cbn [ms_mem restrict] in RG. destruct RG as (_ & _ & _ & RGc).
  cbn [YP09.r_chunks YP09.r_base base_val] in RGc. apply Forall_inv in RGc.
  assert (VN : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem ms0) (TA_g_ncmd + Z.of_nat j) =
    Some (YO0f.le_byte (TW.u_at B5 TW.OFF_g_ncmd 4 + 1) 4 j)).
  { intros j Hj. pose proof (o4_chunk_bytes E1 (w_H W') (ms_mem ms0) 0 TA_g_ncmd 4 4 _
      (TW.u_at B5 TW.OFF_g_ncmd 4 + 1) RGc eq_refl ltac:(lia) (o4_den_inc E1 38 _ U38) j Hj) as Hb.
    rewrite Z.add_0_l in Hb. exact Hb. }
  assert (HTWF : lc_tw W' (ms_mem ms0) (o4_b7 B5)).
  { apply (o4_w_ncmd B5 (aview segs (w_H W') mem') (aview segs (w_H W') (ms_mem ms0)) HTW VN).
    intros x Hx Hn. pose proof (GL x (ios_tw_in_G x Hx)) as Hl. apply K2; [lia | exact Hn]. }
  rewrite (o4_b6_skip B5 _ want at_ (tg_serial tv) Hw0) in HSET, HOP.
  (* the registers *)
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 26]%bv -> YK11.getr (ms_regs ms0) r = YK11.getr regs' r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W') E1 _ ms0 r HS).
    cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
        cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EE; reflexivity |]).
    destruct Hr. }
  assert (R19F : YK11.getr (ms_regs ms0) (Z_to_bv 5 19) = w64 (l_p cx + TOP.fi_off (tg_c tv))).
  { rewrite (st_ok_pi_restrict_reg (w_H W') E1 _ ms0 _ HS).
    lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
    rewrite (o4_den_add E1 24 25 (l_p cx + TOP.fi_off (tg_c4 tv)) (tg_n tv)).
    - rewrite Hoff5. f_equal. ring.
    - rewrite (EE 24%nat 24%bv eq_refl). exact R24.
    - rewrite (EE 25%nat 25%bv eq_refl). exact R25. }
  assert (R23F : YK11.getr (ms_regs ms0) (Z_to_bv 5 23) = w64 (TOP.fi_n (tg_c tv))).
  { rewrite (st_ok_pi_restrict_reg (w_H W') E1 _ ms0 _ HS).
    lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
    rewrite (o4_den_sub E1 34 25 (TOP.fi_n (tg_c4 tv)) (tg_n tv) E34).
    - rewrite Hfi5. reflexivity.
    - rewrite (EE 25%nat 25%bv eq_refl). exact R25. }
  assert (R20F : YK11.getr (ms_regs ms0) 20 = w64 LF_S4).
  { rewrite (st_ok_pi_restrict_reg (w_H W') E1 _ ms0 _ HS).
    lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
    destruct lf_spill_pages as (_ & _ & P10 & _). unfold LF_S4, w64. rewrite P10. reflexivity. }
  (* the core at the final memory *)
  destruct (o4_kept3 cx ly' S' W' regs' mem' md' e (ms_mem ms0) 0 HB HC0 LAWS ltac:(lia)
    ltac:(intros a Ha HnG _; apply K2; [exact Ha | intros Hn; apply HnG; apply o4_inG_ncmd; exact Hn]))
    as (KA & KB & KF & KM).
  pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e 0 ly' S' W' regs' (ms_mem ms0) md2 e
    LAWS HB HC0 HJ eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia) KA KB KF) as HC2.
  pmkst HS.
  apply SRr_ret.
  refine (o4_close cx op ly' S' W' regs' mem' md' e (ms_regs ms0) (ms_mem ms0) md2 (o4_b7 B5) (tg_c tv) _ _
    HL HC2 KM KR (conj R19F R23F) R20F Hopc HTWF HSET HOP).
  vm_compute. reflexivity.
- (* want = SPEC_OK: the stores of g_cmd[serial], the copy, then the replace or the append *)
  rewrite (o4_br_want E1 want E22 HWC') in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hw0.
  assert (U27 : bv_unsigned (ew E1 27) = TA_g_cmd + 40 * tg_serial tv)
    by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; unfold TA_g_cmd; lia).
  pose proof (o4_apart (lc_F cx) (TA_g_cmd + 40 * tg_serial tv) 40 HFG
    ltac:(intros x Hx; apply o4_inG_cmd; lia) ltac:(lia)) as HapC.
  (* g_cmd[serial]'s two written stretches into the state *)
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    assert (HdisA : all_disjoint E1 o4_rg_cmda (ss_mem s)) end.
  { cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_cmda.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27, U32.
    unfold TA_g_cmd in *. split; [lia | split; [lia | exact I]]. }
  pose proof (st_ok_pi_add_region (PI := PI_transport) E1 _ _ o4_rg_cmda HS ltac:(vm_compute; reflexivity)
    (o4_rgw_ok E1 _ 27 (TA_g_cmd + 40 * tg_serial tv) 0 12 U27 ltac:(unfold TA_g_cmd; lia)
       ltac:(unfold TA_g_cmd; lia) ltac:(lia) ltac:(intros o Ho; apply o4_inG_cmd; lia)) HdisA) as HS2.
  clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    assert (HdisB : all_disjoint E1 o4_rg_cmdb (ss_mem s)) end.
  { cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_cmdb.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27, U32.
    unfold TA_g_cmd in *. split; [lia | split; [lia | split; [lia | exact I]]]. }
  pose proof (st_ok_pi_add_region (PI := PI_transport) E1 _ _ o4_rg_cmdb HS ltac:(vm_compute; reflexivity)
    (o4_rgw_ok E1 _ 27 (TA_g_cmd + 40 * tg_serial tv) 36 37 U27 ltac:(unfold TA_g_cmd; lia)
       ltac:(unfold TA_g_cmd; lia) ltac:(lia) ltac:(intros o Ho; apply o4_inG_cmd; lia)) HdisB) as HS2.
  clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  (* run B1, +0x11a4 .. +0x1218: the four checked stores into g_cmd[serial] of c's len, display and key and of
     PENDING, the copy's arguments, `jal __asan_memcpy` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (first
      [ apply awr_ok_x_cons_g;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U27 in Ha; apply o4_inG_cmd; lia |]
      | apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |] ]).
    apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  o4_low HS E1 HEXb.
  (* run B1 changed g_cmd[serial]'s two stretches only *)
  assert (KB1 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (TA_g_cmd + 40 * tg_serial tv <= a < TA_g_cmd + 40 * tg_serial tv + 12) ->
    a <> TA_g_cmd + 40 * tg_serial tv + 36 -> aview segs (w_H W') (ms_mem ms0) a = aview segs (w_H W') mem' a).
  { intros a Ha Hn1 Hn2. rewrite <- (K1 a Ha).
    apply (kept_of_frame E1 _ (w_H W') (ms_mem ms) (ms_mem ms0)
      (fun x => TA_g_cmd + 40 * tg_serial tv <= x < TA_g_cmd + 40 * tg_serial tv + 12 \/
                x = TA_g_cmd + 40 * tg_serial tv + 36) HFr);
      [|exact Ha | intros [Hx|Hx]; [exact (Hn1 Hx) | exact (Hn2 Hx)]].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U27 in Hx; cbv beta;
       first [lia | left; lia | right; lia] |]).
    destruct Hin. }
  try clear HF; try clear HFr; try clear HG.
  (* the stored bytes, from the chunks of the run's last state *)
  lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ =>
    set (Eb := Ex) in * end.
  assert (U27b : bv_unsigned (ew Eb 27) = TA_g_cmd + 40 * tg_serial tv) by (rewrite HEXb by lia; exact U27).
  assert (HEIb : img_env VAL A_LIM Eb)
    by (intros n Hn; rewrite HEXb by (unfold A_TEXT, A_LIM in *; lia); exact (HEI n Hn)).
  assert (U32b : bv_unsigned (ew Eb 32) = lc_F cx + 32) by (rewrite HEXb by lia; exact U32).
  assert (U37 : bv_unsigned (ew E1 37) = tg_len tv) by (rewrite E37; unfold w64; apply unsigned_lit_small; lia).
  assert (U37b : bv_unsigned (ew Eb 37) = tg_len tv) by (rewrite HEXb by lia; exact U37).
  (* the registers at the call of __asan_memcpy *)
  o4_reg HS (Z_to_bv 5 10) (w64 (TA_g_cmd + 40 * tg_serial tv + 12)) Ra0
    ltac:(cbn [sv_denot]; rewrite U27b; reflexivity).
  o4_reg HS (Z_to_bv 5 11) (w64 (lc_F cx + 32)) Ra1 ltac:(cbn [sv_denot]; rewrite U32b, Z.add_0_r; reflexivity).
  o4_reg HS (Z_to_bv 5 12) (w64 (tg_len tv)) Ra2 ltac:(cbn [sv_denot]; rewrite U37b, Z.add_0_r; reflexivity).
  o4_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 4636)) Rra ltac:(apply codeptr_val; exact HEIb).
  o4_reg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) Rsp
    ltac:(cbn [sv_denot]; rewrite HEXb by lia; rewrite (EE 2%nat 2%bv eq_refl), R2, Z.add_0_r;
          apply Z_to_bv_bv_unsigned).
  o4_reg HS (3%bv : bv 5) (w64 (as_gp B)) Rgp
    ltac:(cbn [sv_denot]; rewrite HEXb by lia; rewrite (EE 3%nat 3%bv eq_refl), R3, Z.add_0_r;
          apply Z_to_bv_bv_unsigned).
  o4_reg HS (4%bv : bv 5) (w64 (as_tp B)) Rtp
    ltac:(cbn [sv_denot]; rewrite HEXb by lia; rewrite (EE 4%nat 4%bv eq_refl), R4, Z.add_0_r;
          apply Z_to_bv_bv_unsigned).
  assert (Usp : spZ (ms_regs ms0) = lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)).
  { unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (EST : ESTACK = 4096) by reflexivity.
  (* the destination g_cmd[serial] + 12: its zero shadow *)
  pose proof HJ as (_ & _ & (memSb & HJdb & _) & _). pose proof HJdb as (HARb & _).
  pose proof HSC as (_ & _ & _ & HZc).
  destruct (o4_cmd_blk (tg_serial tv) 12 (12 + tg_len tv) Hs ltac:(lia) ltac:(lia)) as [Hb1 Hb2].
  assert (Hb2' : (TA_g_cmd + 40 * tg_serial tv + 12 + tg_len tv - 1) / 64 * 64 + 64 <= TA_g_cmd + TW.SZ_g_cmd).
  { replace (TA_g_cmd + 40 * tg_serial tv + 12 + tg_len tv - 1)
      with (TA_g_cmd + 40 * tg_serial tv + (12 + tg_len tv) - 1) by lia.
    unfold TW.SZ_g_cmd. exact Hb2. }
  destruct (decode_zshadow_ra B ly' S' W' (ms_mem ms0) md2 TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd)
     (TA_g_cmd + 40 * tg_serial tv + 12) (tg_len tv) HARb HZc ltac:(lia) Hb1 Hb2') as (DRA & DHU).
  (* the source c: its shadow (c in scope) and its bytes *)
  assert (HSH : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= YM05.alloc_ceiling).
  { unfold lc_SH. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)) as D0.
    assert (D1 : lc_F cx / 8 <= lc_F cx) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF. lia. }
  assert (HFSHb : lc_fsh cx (aview segs (w_H W') (ms_mem ms0)) true false).
  { apply (lc_fsh_kept cx (aview segs (w_H W') mem') _ true false); [|exact HFSH].
    intros a Ha. apply KB1; unfold SHADOW_OFF, TA_g_cmd in *; lia. }
  destruct (o4_c_src cx (aview segs (w_H W') (ms_mem ms0)) (tg_len tv) HFSHb HF4096 HFal ltac:(lia)) as (SRA & SHU).
  pose proof (o4_F_range cx ly' S' W' regs' mem' md' e LAWS HB HC0) as FRg.
  assert (SRC : src_ok segs W' (ms_regs ms0) (ms_mem ms0) (lc_F cx + 32) (tg_len tv)).
  { intros a Ha. split.
    - rewrite (KB1 a ltac:(lia)) by (destruct HapC; lia).
      replace a with (lc_F cx + 32 + (a - (lc_F cx + 32))) by ring.
      exact (o4_c_some (w_H W') mem' (lc_F cx + 32) _ _ _ _ HCS Hcb (a - (lc_F cx + 32)) ltac:(lia)).
    - rewrite Usp. lia. }
  (* the registers the run keeps and the four stores' chunks, from the run's last state *)
  assert (KRb : forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
    YK11.getr (ms_regs ms0) (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ rewrite (st_ok_restrict_reg segs (w_H W') Eb _ ms0 _ HS);
        lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
        cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEXb by lia; apply EE; reflexivity |]).
    destruct Hr. }
  o4_reg HS (Z_to_bv 5 20) (w64 LF_S4) R20b
    ltac:(destruct lf_spill_pages as (_ & _ & P10 & _); unfold LF_S4, w64; rewrite P10; reflexivity).
  pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RGa.
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RGl.
  cbn [ms_mem restrict] in RGa, RGl.
  destruct RGa as (_ & _ & _ & RGa). destruct RGl as (_ & _ & _ & RGl).
  cbn [YP09.r_chunks YP09.r_base base_val] in RGa, RGl.
  rewrite U27b in RGa, RGl.
  apply Forall_inv in RGl.
  pose proof (Forall_inv RGa) as CHd. apply Forall_inv_tail in RGa.
  pose proof (Forall_inv RGa) as CHk. apply Forall_inv_tail in RGa.
  pose proof (Forall_inv RGa) as CHs. clear RGa.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q)
  end.
  eapply SRr_bind.
  { apply (@gx_intrin_at (l_fx cx) rc AE2k.tfib_sink_head segs B LAWS transport_segs_low OCpy
      (transport_sigma TS___asan_memcpy) (lp_memcpy B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS W' (ms_regs ms0)
      (ms_mem ms0) _ _ _ _ _ _ _ _ _ ly' S' md2 e (TA_g_cmd + 40 * tg_serial tv + 12) (lc_F cx + 32) (tg_len tv)
      (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 4636)) HGX G_HARNESS_rw HJ Ra0 Ra1 Ra2).
    - lia.
    - unfold TA_g_cmd; lia.
    - unfold TA_g_cmd; lia.
    - exact Usp.
    - exact (o4_mod16 _ _ Hsp1al Hsp0al).
    - unfold LF_FRAME in Hsp1. lia.
    - unfold LLVMF_STK, LF_FRAME in *. lia.
    - exact Rgp.
    - exact Rtp.
    - exact Rra.
    - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
    - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply o4_inG_cmd.
      unfold TA_g_cmd in *. lia.
    - unfold amem_range, kLowMemEnd, TA_g_cmd. left. lia.
    - exact DRA.
    - intros _. exact DHU.
    - cbv iota beta. split; [lia|]. split; [lia|]. split; [exact SRC|].
      split; [destruct HapC; lia|].
      split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; destruct FRg; [left | right]; lia|].
      split; [exact SRA | intros _; exact SHU]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcopy & Heff & Hpres3).
  cbv iota in Hcopy.
  (* the bytes of g_cmd[serial] after the call *)
  assert (Hg3 : forall a, TA_g_cmd + 40 * tg_serial tv <= a < TA_g_cmd + 40 * tg_serial tv + 40 ->
    ~ (TA_g_cmd + 40 * tg_serial tv + 12 <= a < TA_g_cmd + 40 * tg_serial tv + 12 + tg_len tv) ->
    aview segs (w_H W') mem3 a = aview segs (w_H W') (ms_mem ms0) a).
  { intros a Ha Hn. apply Heff; [unfold TA_g_cmd in *; lia | exact Hn | unfold TA_g_cmd in *; lia]. }
  assert (U35 : bv_unsigned (ew E1 35) = sv_key kd) by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
  assert (U35b : bv_unsigned (ew Eb 35) = sv_key kd) by (rewrite HEXb by lia; exact U35).
  assert (Hdisp' : 0 <= sv_display kd < 256) by (destruct Hdisp as [Hd|Hd]; rewrite Hd; lia).
  assert (U36 : bv_unsigned (ew E1 36) = sv_display kd) by (rewrite E36; unfold w64; apply unsigned_lit_small; lia).
  assert (U36b : bv_unsigned (ew Eb 36) = sv_display kd) by (rewrite HEXb by lia; exact U36).
  assert (Wst : forall j, (j < 4)%nat ->
    aview segs (w_H W') mem3 (TA_g_cmd + 40 * tg_serial tv + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)).
  { intros j Hj. rewrite Hg3 by lia.
    pose proof (o4_chunk_bytes Eb (w_H W') (ms_mem ms0) _ 0 4 4 (SLit 1) 1 CHs eq_refl ltac:(lia)
      (o4_den_lit Eb 1 4 ltac:(lia)) j Hj) as Hb. rewrite Z.add_0_r in Hb. exact Hb. }
  assert (Wkey : forall j, (j < 4)%nat ->
    aview segs (w_H W') mem3 (TA_g_cmd + 40 * tg_serial tv + 4 + Z.of_nat j) = Some (YO0f.le_byte (sv_key kd) 4 j)).
  { intros j Hj. rewrite Hg3 by lia.
    exact (o4_chunk_bytes Eb (w_H W') (ms_mem ms0) _ 4 4 4 _ (sv_key kd) CHk eq_refl ltac:(lia)
      (o4_den_sext Eb 35 (sv_key kd) U35b) j Hj). }
  assert (Wdisp : forall j, (j < 4)%nat ->
    aview segs (w_H W') mem3 (TA_g_cmd + 40 * tg_serial tv + 8 + Z.of_nat j) =
    Some (YO0f.le_byte (sv_display kd) 4 j)).
  { intros j Hj. rewrite Hg3 by lia.
    pose proof (o4_den_off Eb 36 (sv_display kd) 4 0 U36b ltac:(lia)) as Hd. rewrite Z.add_0_r in Hd.
    exact (o4_chunk_bytes Eb (w_H W') (ms_mem ms0) _ 8 4 4 _ (sv_display kd) CHd eq_refl ltac:(lia) Hd j Hj). }
  assert (Wlen : aview segs (w_H W') mem3 (TA_g_cmd + 40 * tg_serial tv + 36) = Some (YO0f.le_byte (tg_len tv) 1 0)).
  { rewrite Hg3 by lia.
    pose proof (o4_den_off Eb 37 (tg_len tv) 1 0 U37b ltac:(lia)) as Hd. rewrite Z.add_0_r in Hd.
    pose proof (o4_chunk_bytes Eb (w_H W') (ms_mem ms0) _ 36 1 1 _ (tg_len tv) RGl eq_refl ltac:(lia) Hd 0%nat
      ltac:(lia)) as Hb.
    cbn [Z.of_nat] in Hb. rewrite Z.add_0_r in Hb. exact Hb. }
  assert (Wcpy : forall i, 0 <= i < tg_len tv ->
    aview segs (w_H W') mem3 (TA_g_cmd + 40 * tg_serial tv + 12 + i) =
    Some (bv_unsigned (nth (Z.to_nat i) (tg_cbytes tv) (Z_to_bv 8 0)))).
  { intros i Hi. rewrite (Hcopy i Hi). rewrite (KB1 (lc_F cx + 32 + i) ltac:(lia)) by (destruct HapC; lia).
    exact (o4_c_byte (w_H W') mem' (lc_F cx + 32) _ _ _ _ HCS Hcb i ltac:(lia)). }
  assert (Woth : forall x, tw_in TMAP_A x ->
    ~ (TA_g_cmd + 40 * tg_serial tv <= x < TA_g_cmd + 40 * tg_serial tv + 12 + tg_len tv) ->
    x <> TA_g_cmd + 40 * tg_serial tv + 36 -> aview segs (w_H W') mem3 x = aview segs (w_H W') mem' x).
  { intros x Hx Hn1 Hn2. pose proof (GL x (ios_tw_in_G x Hx)) as Hl.
    rewrite Heff; [| clear - Hl; lia | clear - Hn1; lia | clear - Hl Hsp1c Hce EST; lia].
    apply KB1; [clear - Hl; lia | clear - Hn1 Hlen; lia | exact Hn2]. }
  pose (Bw := o4_cmdw B5 (tg_serial tv) (sv_key kd) (sv_display kd) (tg_len tv) (tg_cbytes tv)).
  pose proof (o4_w_cmd B5 (aview segs (w_H W') mem') (aview segs (w_H W') mem3) (tg_serial tv) (sv_key kd)
    (sv_display kd) (tg_len tv) (tg_cbytes tv) HTW Hs ltac:(clear - Hlen; lia) Hcb Wst Wkey Wdisp Wlen Wcpy Woth)
    as HTW3.
  change (lc_tw W' mem3 Bw) in HTW3.
  (* the registers and the spill slots after the call *)
  assert (KR3 : forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
    YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (KRb r Hr). apply HP3. exact (o4_cs r Hr). }
  assert (KS3 : forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 \/ lc_SH cx <= a < lc_SH cx + 32 ->
    aview segs (w_H W') mem3 a = aview segs (w_H W') mem' a).
  { intros a Ha. destruct Ha as [Ha|Ha].
    - rewrite Heff; [| clear - Ha Hsp1b Hce; lia | clear - Ha Hsp1c Hce Hs Hlen; unfold TA_g_cmd; lia | clear - Ha; lia].
      apply KB1; [clear - Ha Hsp1b Hce; lia | clear - Ha Hsp1c Hce Hs; unfold TA_g_cmd; lia |
        clear - Ha Hsp1c Hce Hs; unfold TA_g_cmd; lia].
    - rewrite Heff; [| clear - Ha HSH Hce; unfold SHADOW_OFF in *; lia |
        clear - Ha HSH Hs Hlen; unfold SHADOW_OFF, TA_g_cmd in *; lia | clear - Ha HSH Hsp1c EST; lia].
      apply KB1; [clear - Ha HSH Hce; unfold SHADOW_OFF in *; lia | clear - Ha HSH Hs; unfold SHADOW_OFF, TA_g_cmd in *; lia |
        clear - Ha HSH Hs; unfold SHADOW_OFF, TA_g_cmd in *; lia]. }
  assert (R20c : YK11.getr regs3 (Z_to_bv 5 20) = w64 LF_S4) by (rewrite (HP3 20 o4_cs20); exact R20b).
  assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
      aview segs (w_H W') mem3 a = aview segs (w_H W') mem' a).
  { intros a Ha HnG Hw.
    rewrite Heff; [| exact Ha | intros Hd; apply HnG; apply o4_inG_cmd; clear - Hd Hs Hlen; lia | clear - Hw EST; lia].
    apply KB1; [exact Ha | intros Hd; apply HnG; apply o4_inG_cmd; clear - Hd Hs; lia |
      intros Hd; apply HnG; apply o4_inG_cmd; clear - Hd Hs; lia]. }
  rewrite Hw0 in HSET, HOP.
  assert (HATR'' : at_ = -1 \/ 0 <= at_ < 1024) by (unfold TC.CMDS_MAX in HATR; exact HATR).
  exact (o4_tail cx op ly' S' W' regs' mem' md' e regs3 mem3 md3 B5 Bw at_ (tg_serial tv) (sv_key kd) (sv_display kd)
    (tg_len tv) (tg_n tv) (tg_c4 tv) (tg_c tv) HP HB HL HJ3 Hopc KR3 R20c R19 R24 R25 R27 Hoff5 Hfi5 KS3 KM3
    S56 S64 S72 Hs Hkey Hdisp' ltac:(clear - Hlen; lia) HATR'' HTW3 (fun H => HMrep Hw0 H) (fun H => HMapp Hw0 H)
    HSET HOP).
Qed.


End seg.
Print Assumptions lc_op4st_ok.
