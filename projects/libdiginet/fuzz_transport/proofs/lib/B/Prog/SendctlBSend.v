(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 373 of its 421 lines of code are new or changed and 1876 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBRel.v, with its module paths and module names changed; 751 of its 831 lines of code are new or changed and 341 lines of the source are left out. *)
(* SendctlBSend: Lemma sendctl_send : sendctl_send_stmt (lib/B/Prog/SendctlBCut.v), the send piece of image B's walk
   of send_control, offsets +0x1ec .. +0x25c of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x870c0 .. 0x87130), which falls into the release cut sendctl_rel_at (+0x260, the
   piece's premise); the twin of image A's lib/A/Prog/SendctlSend.v (the same code, 0x14 bytes later, io_send at
   0x82ffc).

   What the code does. +0x1ec .. +0x210: a0 = s + 72 and the shadow byte of it, `bnez` not taken; a1 = s + 64 and its
   shadow byte, `bnez` not taken (both shadow bytes are 0: g_s's payload is a zero-shadow range of the record,
   send_control_cg.v trans_sendctl_cells, read by DgnTransportBCg.v decode_zshadow_ra; so the two errpath_load8 calls
   at +0x3e0 and +0x3e8 are not reached); +0x214 `ld a1, 0(a1)` = S_io_ctx, +0x218 `ld a3, 0(a0)` = S_io_send =
   TI.ti_io_send timg_B (SendctlBCut.v sendctl_model); a0 = ctx, a1 = f = F + 32, a2 = 60; +0x228 `jalr a3`: io_send at
   TI.ti_io_send timg_B (io_send_cg.v transport_io_send_cg, the fourth contract of sendctl_callees); +0x22c s5 = r;
   +0x230 `bnez a0`: r <> 0 goes to the release cut with the world io_send left; else +0x234 .. +0x25c: a0 = s + 18192,
   its shadow byte (0, so errpath_load8 at +0x3f4 is not reached), s5 = 0, the 8-byte load, + 1, the 8-byte store back
   (the model's set_S_stats_tx_frames), to the release cut.

   Two runs of the shadow-token engine over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x): run 1 from +0x1ec stops at the `jalr` (its target is a literal, not a code pointer); its state holds
   g_s's 16 bytes [s + 64, s + 80) read-only (atom 32 = S_io_ctx, the literal 0x82ffc at s + 72) and the shadow entry
   [s + 64, s + 80). The `jalr` is one machine step (DgnTransportBPaLib.v SRr_jalr_call_pi), then io_send's contract
   (SRr_bind). Run 2 from +0x22c: a state with g_s's tx_frames word (atom 32 = its value in io_send's world, writable:
   a byte of G) and the shadow entry [s + 18192, s + 18200); it stops at `bnez a0` (r is an atom), the branch is split
   (DgnTransportBPaLib.v psrr_branch_tok), and each side runs to +0x260.

   What the call kept: the cut's acall_kept_g at the memory with the out cells put back (gover (sendctl_outs kp klp)),
   moved over run 1 (no write), composed with io_send's acall_kept_g lifted to that form (SendctlBCut.v
   acall_kept_g_gover: the out cell klp lies outside io_send's window and is present at the three memories) by
   TransportGCg.v dk_kept_trans_nf_g (io_send's written range iosend_wr 60 lies in sendctl_wr), then carried over run 2's
   8-byte store, a byte of G inside sendctl_wr (lib/A/Prog/TransportGFrame.v dk_kept_step_gw). The world relation: io_send's at B1,
   then TWorldG.v tw_write at tx_frames when r = 0. g_fail_next: 0 after io_send (lib/TModel/TIoSendFail.v
   io_send_m_fail_next), and the store of tx_frames keeps it (scs_gf_tx, the plain walk's sc_gf_tx). The out cells:
   each byte of [kp, kp + 60) and [klp, klp + 8) is an awr_byte of the caller's journal outside G, so io_send keeps it
   (a byte of the caller's stack window outside io_send's window, of a block or of a frame of the call state) and run 2
   keeps it (it is not tx_frames, a byte of G). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg SendctlBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TWorldLemmas TIoSendFail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TIF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoSendFail.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The two symbolic states                                          *)
(* ------------------------------------------------------------------ *)

(* Run 1, +0x1ec .. the `jalr` at +0x228: g_s's io.ctx (atom 32) and io.send (the literal io_send entry), read-only;
   s3 (atom 19) is s, s10 (atom 26) the shadow base. *)
Definition scs_rg_io : YP09.region :=
  YP09.mkRegion (Some 19%nat) 64 80 0 0
    [YP09.mkChunk 64 (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk 72 (YP09.CVal 8 (SLit 0x82ffc))].
Definition scs_facts : facts :=
  mkFacts [(19%nat, mkAF SENDCTL_S SENDCTL_S 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_scs1 : sstate := mkSS SENDCTL_SEND sr_atoms [scs_rg_io] None scs_facts.
Definition SCS_SH1 : list shent := [mkSHE 19 64 80].
Definition SCS_Bx : sv := SOff 26 0.
(* Run 2, +0x22c (io_send's return) .. +0x260: g_s's stats.tx_frames (atom 32, its value in io_send's world),
   written. *)
Definition SCS_C2 : Z := AF_send_control + 0x22c.
Definition scs_rg_tx : YP09.region :=
  YP09.mkRegion (Some 19%nat) 18192 18200 18192 18200 [YP09.mkChunk 18192 (YP09.CVal 8 (SOff 32 0))].
Definition ss_scs2 : sstate := mkSS SCS_C2 sr_atoms [scs_rg_tx] None scs_facts.
Definition SCS_SH2 : list shent := [mkSHE 19 18192 18200].

(* ------------------------------------------------------------------ *)
(* 2. World facts                                                       *)
(* ------------------------------------------------------------------ *)

Lemma scs_tx_set : forall Bw v, TW.set_S_stats_tx_frames Bw v = TW.upd Bw (TW.OFF_g_s + 18192) (TW.put 8 v).
Proof. intros Bw v. reflexivity. Qed.
Lemma scs_tx_get : forall Bw, TW.S_stats_tx_frames Bw = TW.u_at Bw (TW.OFF_g_s + 18192) 8.
Proof. intros Bw. reflexivity. Qed.
Lemma scs_io_get : forall Bw, TW.S_io_send Bw = TW.u_at Bw (TW.OFF_g_s + 72) 8.
Proof. intros Bw. reflexivity. Qed.

(* stats.tx_frames++ leaves g_fail_next alone (lib/Prog/T/send_control.v sc_gf_tx). *)
Lemma scs_gf_tx : forall Bw v, length Bw = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_S_stats_tx_frames Bw v) = TW.g_fail_next Bw.
Proof.
  intros Bw v L. unfold TW.set_S_stats_tx_frames, TW.g_fail_next.
  apply TWL.u_at_upd_out; unfold TW.A_S_stats_tx_frames, TW.OFF_g_fail_next, TW.OFF_g_s;
    rewrite ?TWL.length_put, ?L; unfold TW.W_LEN; lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma scs_inG : forall a, SENDCTL_S <= a < SENDCTL_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, SENDCTL_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* A field of a row of TMAP_B is a range of G. *)
Lemma scs_twa_G : forall o b n A w a, In (o, b, n) TMAP_B -> o <= A -> A + w <= o + n ->
  twb_fld o b A w a -> inG TG.G_HARNESS_B a.
Proof.
intros o b n A w a Hin H1 H2 Ha. unfold twb_fld in Ha. unfold inG. apply Exists_exists.
exists (b, n). split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Ltac scs_leb := apply Z.leb_le; vm_compute; reflexivity.
(* A decoded `jalr`, equal to the stated one up to the proofs inside the bit-vector literals. *)
Ltac scs_dec :=
  vm_compute;
  lazymatch goal with |- Some (Jalr ?a ?b ?c, _) = Some (Jalr ?a' ?b' ?c', _) =>
    replace a with a' by (apply bv_eq; reflexivity);
    replace b with b' by (apply bv_eq; reflexivity);
    replace c with c' by (apply bv_eq; reflexivity); reflexivity end.

(* Every byte io_send may store (iosend_wr) is a byte of G. *)
Lemma scs_iosend_G : forall a, iosend_wr SENDCTL_F a -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold iosend_wr in Ha.
destruct Ha as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]].
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_g_fail_next _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_GOT _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_GOT _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_GOT _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_g_last_counter _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_M _ _ H); scs_leb.
- destruct H as (s & Hs & H). refine (scs_twa_G _ _ _ _ _ _ TMAP_B_g_cmd _ _ H);
    unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TC.CMDS_MAX in *; lia.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_g_q _ _ H); scs_leb.
- refine (scs_twa_G _ _ _ _ _ _ TMAP_B_g_nq _ _ H); scs_leb.
Qed.

(* The thirteen saved words lie 8 .. 96 bytes below the entry sp. *)
Lemma scs_saved_rng : forall o, In o SENDCTL_SAVED -> 8 <= fst o <= 96.
Proof.
intros o Hin. unfold SENDCTL_SAVED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin.
Qed.

(* A write right of the caller's journal at a later state of the call: its blocks contain the call's, its layout puts
   the frames where the call's does, and its own frames contain the call's. *)
Lemma scs_awr_mono : forall STK sp0 FP bl0 blc blc' ly ly' (own own' : list (Z * Z)) a,
  awr_byte STK sp0 FP bl0 blc ly own a ->
  (forall bm, In bm blc -> In bm blc') -> ly_F ly' = ly_F ly -> (forall fr, In fr own -> In fr own') ->
  awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a Hw Hb Hl Ho.
destruct Hw as [Hw | [(Hfp & b & n & Hin & Hr) | [(b & n & Hin & Hn & Hr) | (c & p & Hin & Hr)]]].
- left. exact Hw.
- right; left. split; [exact Hfp|]. exists b, n. split; [exact (Hb _ Hin) | exact Hr].
- right; right; left. exists b, n. split; [exact (Hb _ Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists c, p. split; [exact (Ho _ Hin)|].
  assert (E : frame_addr ly' c p = frame_addr ly c p) by (unfold frame_addr; rewrite Hl; reflexivity).
  rewrite E. exact Hr.
Qed.

Lemma scs_getr_upd_same : forall regs v, YK11.getr (YK11.regupd regs 1 v) 1 = v.
Proof. intros regs v. unfold YK11.getr. cbn [bv_eqb]. apply regupd_same. Qed.

Lemma scs_getr_upd_other : forall regs v (r : bv 5), bv_eqb r 1 = false ->
  YK11.getr (YK11.regupd regs 1 v) r = YK11.getr regs r.
Proof.
intros regs v r Hr. unfold YK11.getr. destruct (bv_eqb r 0); [reflexivity|].
apply regupd_other. intros ->. vm_compute in Hr. discriminate Hr.
Qed.

Lemma scs_z2bv_mod : forall x, Z_to_bv 64 x = Z_to_bv 64 (x mod 2 ^ 64).
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac scs_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac scs_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
(* The awr obligation's regions, computed. *)
Ltac scs_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows a run wrote, each inside the bytes Zs. *)
Ltac scs_win Hin Hx U19 :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite U19 in Hx; lia |]);
  destruct Hin.

Section send. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* ------------------------------------------------------------------ *)
(* 3. The two entry states                                              *)
(* ------------------------------------------------------------------ *)

Definition scs_E1 (regs2 : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 64) 8)]).
Definition scs_E2 (regs3 : bvmap 5 word) (B1 : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs3 [Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 18192) 8)]).

(* g_s's bytes [s + q, s + q + n) are addressable at every AR state when their 64-byte blocks lie in g_s. *)
Lemma scs_ra : forall ly S (W : world segs) mem md q n,
  trans_sendctl_cells B -> @AR rc segs B ly S W mem md -> 0 < n ->
  SENDCTL_S <= (SENDCTL_S + q) / 64 * 64 -> (SENDCTL_S + q + n - 1) / 64 * 64 + 64 <= SENDCTL_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (SENDCTL_S + q) n.
Proof.
intros ly S W mem md q n HSC HAR Hn H1 H2.
exact (proj1 (decode_zshadow_ra B ly S W mem md SENDCTL_S (SENDCTL_S + TW.SZ_g_s) (SENDCTL_S + q) n HAR HSC Hn H1 H2)).
Qed.

Lemma scs_entry1 : forall ly S (W : world segs) regs2 mem md Bw,
  trans_sendctl_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw -> TW.S_io_send Bw = TI.ti_io_send timg_B ->
  YK11.getr regs2 19 = w64 SENDCTL_S -> YK11.getr regs2 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (scs_E1 regs2 Bw) ss_scs1
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SENDCTL_SEND)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SCS_Bx SCS_SH1 (scs_E1 regs2 Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs2 mem md Bw HSC HAR Htw Hio R19 R26.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (scs_E1 regs2 Bw) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold scs_E1; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (scs_E1 regs2 Bw) 32 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 64) 8))
  by (unfold scs_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (CS : SENDCTL_S = 6157888) by reflexivity.
assert (U19 : bv_unsigned (ew (scs_E1 regs2 Bw) 19) = SENDCTL_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew (scs_E1 regs2 Bw) 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R32 : 0 <= TW.u_at Bw (TW.OFF_g_s + 64) 8 < 2 ^ 64) by exact (TWL.u_at_range Bw _ 8).
assert (U32 : bv_unsigned (ew (scs_E1 regs2 Bw) 32) = TW.u_at Bw (TW.OFF_g_s + 64) 8)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (Hio8 : TW.u_at Bw (TW.OFF_g_s + 72) 8 = 0x82ffc)
  by (rewrite <- scs_io_get, Hio; exact (proj1 io_send_at)).
split.
- rewrite restrict_mkst_fx. unfold ss_scs1.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold scs_rg_io, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs _ _ SENDCTL_S 64 8 (SOff 32 0) (TW.u_at Bw (TW.OFF_g_s + 64) 8));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 64 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    * apply (chunk_ok_val segs _ _ SENDCTL_S 72 8 (SLit 0x82ffc) 0x82ffc); [reflexivity | zside | zside |].
      rewrite <- Hio8.
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 72 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold scs_rg_io, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold scs_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U26.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (scs_E1 regs2 Bw) SCS_Bx = SHADOW_OFF).
  { unfold U, SCS_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, SCS_SH1. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SCS_Bx 19 (SENDCTL_S + 64) 16 SENDCTL_S 64 80
    (scs_ra ly S W mem md 64 16 HSC HAR ltac:(lia) ltac:(rewrite CS; scs_leb) ltac:(rewrite CS; scs_leb)) UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma scs_entry2 : forall ly S (W : world segs) regs3 mem md B1,
  trans_sendctl_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) B1 ->
  YK11.getr regs3 19 = w64 SENDCTL_S -> YK11.getr regs3 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (scs_E2 regs3 B1) ss_scs2
    (restrict (w_H W) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + SCS_C2)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SCS_Bx SCS_SH2 (scs_E2 regs3 B1) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs3 mem md B1 HSC HAR Htw R19 R26.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (scs_E2 regs3 B1) n = YK11.getr regs3 r)
  by (intros n r Hn; unfold scs_E2; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (scs_E2 regs3 B1) 32 = Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 18192) 8))
  by (unfold scs_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (CS : SENDCTL_S = 6157888) by reflexivity.
assert (U19 : bv_unsigned (ew (scs_E2 regs3 B1) 19) = SENDCTL_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew (scs_E2 regs3 B1) 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R32 : 0 <= TW.u_at B1 (TW.OFF_g_s + 18192) 8 < 2 ^ 64) by exact (TWL.u_at_range B1 _ 8).
assert (U32 : bv_unsigned (ew (scs_E2 regs3 B1) 32) = TW.u_at B1 (TW.OFF_g_s + 18192) 8)
  by (rewrite E32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_scs2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold scs_rg_tx, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS_B (SENDCTL_S + o) G_HARNESS_B_rw);
            apply scs_inG; unfold TW.SZ_g_s; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ SENDCTL_S 18192 8 (SOff 32 0) (TW.u_at B1 (TW.OFF_g_s + 18192) 8));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
    exact (tw_read_val segs _ TMAP_B B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18192 8 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold scs_rg_tx, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold scs_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U26.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (scs_E2 regs3 B1) SCS_Bx = SHADOW_OFF).
  { unfold U, SCS_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, SCS_SH2. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SCS_Bx 19 (SENDCTL_S + 18192) 8 SENDCTL_S 18192 18200
    (scs_ra ly S W mem md 18192 8 HSC HAR ltac:(lia) ltac:(rewrite CS; scs_leb) ltac:(rewrite CS; scs_leb)) UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The memory lemmas of the walk                                     *)
(* ------------------------------------------------------------------ *)

(* At the memory with the out cells put back, a byte the step keeps is kept: an out byte reads memc on both sides. *)
Lemma scs_gover_view : forall (outs : list (Z * Z)) (H : word -> bool) (m m' mc : word -> option byte) a,
  (inGb outs (bv_unsigned (Z_to_bv 64 a)) = false -> aview segs H m' a = aview segs H m a) ->
  aview segs H (gover outs m' mc) a = aview segs H (gover outs m mc) a.
Proof.
intros outs H m m' mc a Hk. destruct (inGb outs (bv_unsigned (Z_to_bv 64 a))) eqn:Eb.
- apply (aview_eq_of segs). unfold mrestrict, gover. rewrite Eb. reflexivity.
- rewrite (aview_eq_of segs H m' (gover outs m' mc) a) by (unfold mrestrict, gover; rewrite Eb; reflexivity).
  rewrite (aview_eq_of segs H m (gover outs m mc) a) by (unfold mrestrict, gover; rewrite Eb; reflexivity).
  exact (Hk eq_refl).
Qed.

(* Presence that grows over the step grows at the memory with the out cells put back. *)
Lemma scs_gover_pres : forall (outs : list (Z * Z)) (H : word -> bool) (m m' mc : word -> option byte) a,
  (apresent H m a -> apresent H m' a) ->
  apresent H (gover outs m mc) a -> apresent H (gover outs m' mc) a.
Proof.
intros outs H m m' mc a Hg Hp. unfold apresent, gover in Hp |- *. cbv beta in Hp |- *.
destruct Hp as (Hh & b & Hb).
destruct (inGb outs (bv_unsigned (Z_to_bv 64 a))) eqn:Eb.
- split; [exact Hh | exists b; exact Hb].
- destruct (Hg (conj Hh (ex_intro _ b Hb))) as (Hh' & b' & Hb').
  split; [exact Hh' | exists b'; exact Hb'].
Qed.

(* The bytes of a cell the step keeps keep their values. *)
Lemma scs_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) q (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (q + j) = aview segs H m (q + j)) ->
  garr8 segs (mrestrict H m) q l -> garr8 segs (mrestrict H' m') q l.
Proof.
intros H H' m m' q l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (val_mem_kept segs H H' m m' (q + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros i Hi. change (Z.of_nat 1) with 1 in Hi. replace (q + Z.of_nat j + i) with (q + Z.of_nat j) by lia.
apply Hk. lia.
Qed.

(* Two memories that hold the same n-byte value at a are read the same there. *)
Lemma scs_view_of_vals : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v ->
  forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (a + k) = aview segs H m (a + k).
Proof.
intros H H' m m' a n v Hv Hv' k Hk. unfold aview.
rewrite (val_mem_agree segs (mrestrict H m) (mrestrict H' m') a n v Hv Hv' k Hk). reflexivity.
Qed.

(* The store of v at g_s's tx_frames (8 bytes at s + 18192) gives the world relation at set_S_stats_tx_frames. *)
Lemma scs_tw_tx : forall (H : word -> bool) (m m' : word -> option byte) B1 v,
  tw_at TMAP_B (aview segs H m) B1 ->
  val_mem segs (mrestrict H m') (SENDCTL_S + 18192) 8 v ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (SENDCTL_S + 18192 <= x < SENDCTL_S + 18200) ->
     aview segs H m' x = aview segs H m x) ->
  tw_at TMAP_B (aview segs H m') (TW.set_S_stats_tx_frames B1 v).
Proof.
intros H m m' B1 v Htw Hv Hk. rewrite scs_tx_set.
apply (tw_write TMAP_B (aview segs H m) (aview segs H m') B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18192 8 v TMAP_B_ok Htw
  TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. pose proof (Hv j Hj) as Hb. unfold aview. change SENDCTL_S with TB_g_s in Hb. rewrite Hb.
  cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. try unfold YG0f.le_byte. try unfold le_byte. apply Zmod_mod.
- intros x (o & b & n & Hin & Hx) Hn. pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (_ & _ & _ & Hb0 & Hb64).
  apply Hk; [lia|]. change SENDCTL_S with TB_g_s. cbn [Z.of_nat] in Hn. lia.
Qed.

Lemma scs_lyF : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  ly_F ly' = ly_F ly.
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
destruct HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _). exact HF.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma sendctl_send : @sendctl_send_stmt fx rc B MT.
Proof.
unfold sendctl_send_stmt, sendctl_send_at.
intros REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
  pos sp1 F ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HPCS & HCELLS & HSC & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof CALLEES as (_ & _ & _ & IOS0).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & H14 & Hsp16 & Hstk & Hsp0 & Hcmd & Hack &
  HKP & HTW0 & Hgf0 & HM & HROM0 & HI1 & HI4 & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw & HKLP) & HTW2 & HROM2 & Hlenf & HGf &
  HRDf & HOUT).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25 & R27) & R19 & R23 & R26).
clear HCUR HREGS.
(* the model: the build made 60 bytes, so io_send ran at Bw with f *)
destruct (sendctl_model _ _ _ _ _ _ _ _ HM) as [(_ & _ & _ & Hf0) | (_ & _ & _ & Hio & B1 & HIO & HBW)].
{ exfalso. rewrite Hf0 in Hlenf. change (Z.to_nat SENDCTL_F) with 60%nat in Hlenf. discriminate Hlenf. }
assert (LF : Z.of_nat (length f) = SENDCTL_F) by (rewrite Hlenf; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : SENDCTL_S = 6157888) by reflexivity.
assert (EST : SENDCTL_STK = 144 + IOSEND_STK) by reflexivity.
assert (HIS : 0 <= IOSEND_STK) by scs_leb.
assert (FS : SENDCTL_F = 60) by reflexivity.
assert (FO : SENDCTL_FOFF = 32) by reflexivity.
unfold SENDCTL_FBYTES in HFc, HFapp, HFLw.
(* the caller's stack window lies above alloc_ceiling, below 2 ^ 47; the caller's own frames are frames of Sc *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc & _ & _ & _ & _ & HfrsC & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (Hce : alloc_ceiling <= spZ regs - SENDCTL_STK) by lia.
destruct (can_sp1_facts (spZ regs - SENDCTL_FRAME) ltac:(unfold SENDCTL_FRAME; lia)
  ltac:(unfold SENDCTL_FRAME; rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16. unfold SENDCTL_FRAME in Hsp1r.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the own frame at the cut *)
assert (Hin : In (SENDCTL_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFA : frame_addr ly2 SENDCTL_CID pos = F) by (rewrite Efa; symmetry; exact EF).
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ SENDCTL_CID pos a HAR2 Hin
    ltac:(rewrite EFA; change (fs_frame_bytes SENDCTL_CID) with 256; lia) Hi). }
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
assert (HfrSc : forall fr, In fr (frames Sc) -> In fr (frames S2)) by (intros fr Hf; rewrite Hfrs; right; exact Hf).
assert (Hown : forall fr, In fr own -> In fr (frames Sc)) by (intros fr Hf; rewrite HfrsC; apply in_or_app; left; exact Hf).
assert (NTX : forall a, ~ inG TG.G_HARNESS_B a -> ~ (SENDCTL_S + 18192 <= a < SENDCTL_S + 18200)).
{ intros a Hn Ha. apply Hn. apply scs_inG. unfold TW.SZ_g_s. lia. }
(* ---- run 1, +0x1ec .. the `jalr` at +0x228 ---- *)
destruct (scs_entry1 ly2 S2 W2 regs2 mem2 md2 Bw HSC HAR2 HTW2 Hio R19 R26) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (scs_E1 regs2 Bw)) by (unfold scs_E1; apply Eimg_env).
assert (EE1 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (scs_E1 regs2 Bw) n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold scs_E1; apply can_ew_Eimg_Ereg_nat; exact Hn).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
{ scs_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
(* run 1 wrote no byte *)
assert (M1 : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros (rg & Hrg & Hx).
  lazymatch type of Hrg with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hrg end.
  cbn [In] in Hrg. destruct Hrg as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
clear HF HFr HG.
(* the registers at the `jalr` *)
scs_reg HS (2%bv : bv 5) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
scs_reg HS (3%bv : bv 5) (YK11.getr regs 3) Q3
  ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
scs_reg HS (4%bv : bv 5) (YK11.getr regs 4) Q4
  ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
scs_reg HS (8%bv : bv 5) (w64 (spZ regs)) Q8
  ltac:(cbn [sv_denot]; rewrite (EE1 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
scs_reg HS (9%bv : bv 5) (w64 sp1) Q9
  ltac:(cbn [sv_denot]; rewrite (EE1 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
scs_reg HS (11%bv : bv 5) (w64 (F + SENDCTL_FOFF)) Q11
  ltac:(cbn [sv_denot]; rewrite (EE1 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23).
scs_reg HS (12%bv : bv 5) (w64 SENDCTL_F) Q12
  ltac:(cbn [sv_denot]; rewrite (EE1 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R21).
scs_reg HS (13%bv : bv 5) (Z_to_bv 64 0x82ffc) Q13 ltac:(reflexivity).
scs_reg HS (18%bv : bv 5) (w64 F) Q18
  ltac:(cbn [sv_denot]; rewrite (EE1 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
scs_reg HS (19%bv : bv 5) (w64 SENDCTL_S) Q19
  ltac:(cbn [sv_denot]; rewrite (EE1 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R19).
scs_reg HS (24%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) Q24
  ltac:(cbn [sv_denot]; rewrite (EE1 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R24).
scs_reg HS (25%bv : bv 5) (w64 F) Q25
  ltac:(cbn [sv_denot]; rewrite (EE1 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R25).
scs_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) Q26
  ltac:(cbn [sv_denot]; rewrite (EE1 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R26).
scs_reg HS (27%bv : bv 5) (YK11.getr regs 27) Q27
  ltac:(cbn [sv_denot]; rewrite (EE1 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R27).
(* +0x228: `jalr a3`, one machine step to io_send *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  let pcx := eval vm_compute in (ss_pc ssx) in
  let wx := eval vm_compute in (plookup transportb_tpi pcx) in
  lazymatch wx with Some (PW ?w) =>
    apply (SRr_jalr_call_pi (fx := fx) (PL := PL_transportb) (PI := PI_transportb) W2 _ ssx ms md1 _ w
      (1%bv : bv 5) (13%bv : bv 5) 0x82ffc HEI0 HS eq_refl ltac:(vm_compute; reflexivity)
      ltac:(scs_dec) eq_refl ltac:(vm_compute; reflexivity) Q13 ltac:(lia) eq_refl)
  end end.
intros mat' ms1 -> _.
pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ)
  as HJc.
set (md1' := with_vm_backing (m_vm_lazy md1) mat' md1) in *. clearbody md1'.
set (m1 := ms_mem ms) in *. set (rg1 := ms_regs ms) in *.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst (YK11.regupd _ _ ?vr) _ _ _) _) _ =>
  set (regsC := YK11.regupd rg1 1 vr) end.
clearbody m1 rg1. clear HS SHOK HJ HEI0 ms.
assert (V1 : forall (H : word -> bool) a, aview segs H m1 a = aview segs H mem2 a)
  by (intros H a; apply (aview_eq_of segs); unfold mrestrict; rewrite M1; reflexivity).
assert (P1 : forall (H : word -> bool) a, apresent H mem2 a -> apresent H m1 a)
  by (intros H a (Hh & bb & Hb); split; [exact Hh | exists bb; rewrite M1; exact Hb]).
assert (RC1 : YK11.getr regsC 1 = Z_to_bv 64 (BASE + SCS_C2)) by (unfold regsC; apply scs_getr_upd_same).
assert (EB : BASE + SCS_C2 = 0x87100) by reflexivity.
assert (RCo : forall (rr : bv 5), bv_eqb rr 1 = false -> YK11.getr regsC rr = YK11.getr rg1 rr)
  by (intros rr Hr; unfold regsC; apply scs_getr_upd_other; exact Hr).
assert (HspC : spZ regsC = sp1).
{ change (bv_unsigned (YK11.getr regsC 2) = sp1). rewrite (eq_trans (RCo 2%bv eq_refl) Q2).
  unfold w64. apply unsigned_lit_small. lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR1.
(* ---- the call of io_send ---- *)
lazymatch goal with |- SRr ?sg ?Wx _ ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (TI.ti_io_send timg_B) regsC m1 md1') Q) end.
assert (GF1 : garr8 segs (mrestrict (w_H W2) m1) (F + SENDCTL_FOFF) (map DSpec.bz f)).
{ change (map DSpec.bz f) with (TW.zs f).
  apply (scs_garr8_kept (w_H W2) (w_H W2) mem2 m1 _ _); [intros j _; apply V1 | exact HGf]. }
assert (RD1 : decode_rd_ok W2 m1 (F + SENDCTL_FOFF) SENDCTL_F)
  by exact (trans_rd_ok_view W2 W2 mem2 m1 _ _ HRDf (fun a _ => V1 _ a) (fun s _ => V1 _ s)).
assert (SRC1 : trans_src_ok B ly2 S2 W2 m1 (F + SENDCTL_FOFF) (Z.of_nat (length f))).
{ rewrite LF. right. split; [|exact RD1]. left. exists SENDCTL_CID, pos. split; [exact Hin|].
  rewrite EFA. change (fs_frame_bytes SENDCTL_CID) with 256. rewrite FS, FO. lia. }
assert (ROM1 : trans_rom_view_rd W2 m1) by (intros a Ha; rewrite V1; exact (HROM2 a Ha)).
assert (TW1 : tw_at TMAP_B (aview segs (w_H W2) m1) Bw) by (apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW2 | intros x _; apply V1]).
eapply SRr_bind.
{ apply (IOS0 fx STK sp0 FP ly S W0 mem0 md0 ((SENDCTL_CID, pos) :: own) ly2 S2 W2 m1 md1' (k + e) regsC
    (F + SENDCTL_FOFF) r f Bw B1 HJc).
  - rewrite RC1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold SCS_C2, AF_send_control; lia | reflexivity].
  - unfold raZ. rewrite RC1, EB. rewrite unsigned_lit_small by lia. lia.
  - exact (eq_trans (RCo 3%bv eq_refl) (eq_trans Q3 Hgp)).
  - exact (eq_trans (RCo 4%bv eq_refl) (eq_trans Q4 Htp)).
  - exact (eq_trans (RCo 11%bv eq_refl) Q11).
  - rewrite LF. exact (eq_trans (RCo 12%bv eq_refl) Q12).
  - rewrite HspC. exact Hsp1al16.
  - rewrite HspC. lia.
  - rewrite HspC. lia.
  - rewrite FO. lia.
  - exact GF1.
  - exact SRC1.
  - unfold decode_off_win. rewrite HspC, LF, FS, FO. left. lia.
  - left. intros x Hx. rewrite LF, FS, FO in Hx. apply NGF. lia.
  - exact Hgf0.
  - exact ROM1.
  - exact TW1.
  - exact HIO.
  - exact HI1.
  - exact HI4.
  - unfold IOSEND_EV. lia. }
cbv beta. intros W3 c3 _ HPOST.
unfold transport_io_send_post, transport_cg_post in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e' & -> & He' & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & R10_3 &
  HTW3).
assert (E0 : e' = 0) by (unfold IOSEND_EV in He'; lia). subst e'. rewrite Z.add_0_r in HJ3.
rewrite HspC, LF in HK3. rewrite RC1.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (ELF3 : ly_F ly3 = ly_F lyc).
{ rewrite (scs_lyF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3), <- (scs_lyF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1).
  exact ELF. }
(* the callee-saved registers io_send handed back *)
assert (V2 : YK11.getr regs3 2 = w64 sp1)
  by exact (eq_trans (HP3 2 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 2%bv eq_refl) Q2)).
assert (V3 : YK11.getr regs3 3 = YK11.getr regs 3)
  by exact (eq_trans (HP3 3 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 3%bv eq_refl) Q3)).
assert (V4 : YK11.getr regs3 4 = YK11.getr regs 4)
  by exact (eq_trans (HP3 4 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 4%bv eq_refl) Q4)).
assert (V8 : YK11.getr regs3 8 = w64 (spZ regs))
  by exact (eq_trans (HP3 8 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 8%bv eq_refl) Q8)).
assert (V9 : YK11.getr regs3 9 = w64 sp1)
  by exact (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 9%bv eq_refl) Q9)).
assert (V18 : YK11.getr regs3 18 = w64 F)
  by exact (eq_trans (HP3 18 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 18%bv eq_refl) Q18)).
assert (V19 : YK11.getr regs3 19 = w64 SENDCTL_S)
  by exact (eq_trans (HP3 19 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 19%bv eq_refl) Q19)).
assert (V24 : YK11.getr regs3 24 = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (HP3 24 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 24%bv eq_refl) Q24)).
assert (V25 : YK11.getr regs3 25 = w64 F)
  by exact (eq_trans (HP3 25 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 25%bv eq_refl) Q25)).
assert (V26 : YK11.getr regs3 26 = w64 SHADOW_OFF)
  by exact (eq_trans (HP3 26 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 26%bv eq_refl) Q26)).
assert (V27 : YK11.getr regs3 27 = YK11.getr regs 27)
  by exact (eq_trans (HP3 27 ltac:(unfold acallee_saved; lia)) (eq_trans (RCo 27%bv eq_refl) Q27)).
(* the registers the release cut reads *)
assert (REGS : forall regs4 : bvmap 5 word,
  YK11.getr regs4 2 = YK11.getr regs3 2 -> YK11.getr regs4 3 = YK11.getr regs3 3 ->
  YK11.getr regs4 4 = YK11.getr regs3 4 -> YK11.getr regs4 8 = YK11.getr regs3 8 ->
  YK11.getr regs4 9 = YK11.getr regs3 9 -> YK11.getr regs4 18 = YK11.getr regs3 18 ->
  YK11.getr regs4 24 = YK11.getr regs3 24 -> YK11.getr regs4 25 = YK11.getr regs3 25 ->
  YK11.getr regs4 27 = YK11.getr regs3 27 -> YK11.getr regs4 21 = w64 r ->
  sendctl_regs_rel regs regs4 sp1 F r).
{ intros regs4 Y2 Y3 Y4 Y8 Y9 Y18 Y24 Y25 Y27 Y21. unfold sendctl_regs_rel.
  exact (conj (eq_trans Y2 V2) (conj (eq_trans Y3 V3) (conj (eq_trans Y4 V4) (conj (eq_trans Y8 V8)
    (conj (eq_trans Y9 V9) (conj (eq_trans Y18 V18) (conj Y21 (conj (eq_trans Y24 V24) (conj (eq_trans Y25 V25)
    (eq_trans Y27 V27)))))))))). }
(* a write right of the caller is present at every later state of the walk's journal *)
assert (PRES : forall ly' S' (W' : world segs) m' md' a,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((SENDCTL_CID, pos) :: own) ly' S' W' m' md' (k + e) ->
  Permutation (ablocks B ly' S') (ablocks B lyc Sc) -> ly_F ly' = ly_F lyc ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> apresent (w_H W') m' a).
{ intros ly' S' W' m' md' a HJx Hpx Hlx Hw.
  destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) as (memS & HJi & _ & _).
  refine (proj1 (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
  apply (scs_awr_mono _ _ _ _ _ _ lyc _ own _ a Hw).
  - intros bm Hb. exact (Permutation_in _ (Permutation_sym Hpx) Hb).
  - exact Hlx.
  - intros fr Hf. right. exact Hf. }
(* the out cell klp: outside io_send's window, present at the call, after it and at the walk's entry memory *)
assert (HOUTP : forall a, inG (sendctl_outs kp klp) a ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 - IOSEND_STK <= a < sp1) /\ apresent (w_H W2) m1 a /\ apresent (w_H W3) mem3 a /\
  apresent (w_H W2) memc a).
{ intros a. unfold sendctl_outs. destruct (Z.eqb_spec kp 0) as [Hk0 | Hk0]; intros Ha;
    [exfalso; exact (inG_nil a Ha)|].
  apply inG_cons in Ha. destruct Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)]. unfold in_zr in Ha.
  cbn [fst snd] in Ha.
  destruct HKP as [Hk | (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TWKL & RDKL & OWKL & NGKL & _)];
    [exfalso; exact (Hk0 Hk)|].
  destruct HKLP as [Hk | HPK]; [exfalso; exact (Hk0 Hk)|].
  destruct (TWKL a ltac:(lia)) as [(Hw & Hpc & _ & _) | HGa]; [|exfalso; exact (NGKL a ltac:(lia) HGa)].
  destruct RDKL as (_ & _ & _ & _ & Hk0' & Hk63). unfold decode_off_win in OWKL.
  pose proof (HPK (a - klp) ltac:(lia)) as Hp2. replace (klp + (a - klp)) with a in Hp2 by lia.
  split; [lia|]. split; [lia|]. split; [exact (P1 _ a Hp2)|]. split.
  - exact (PRES ly3 S3 W3 mem3 md3 a HJ3 (Permutation_trans Hperm3 Hperm) ELF3 Hw).
  - destruct Hp2 as (Hh & _). destruct Hpc as (_ & bb & Hbb). split; [exact Hh | exists bb; exact Hbb]. }
(* the facts the release cut carries, at any memory that keeps every byte of io_send's but tx_frames *)
assert (CLOSE : forall (m4 : word -> option byte) md4 (Bx : list byte),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((SENDCTL_CID, pos) :: own) ly3 S3 W3 m4 md4 (k + e) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (SENDCTL_S + 18192 <= a < SENDCTL_S + 18200) ->
     aview segs (w_H W3) m4 a = aview segs (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) m4 a) ->
  tw_at TMAP_B (aview segs (w_H W3) m4) Bx -> TW.g_fail_next Bx <= 1 ->
  sendctl_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bx pos F
    ly3 S3 W3 m4 md4 e).
{ intros m4 md4 Bx HJ4 VW4 P4 TW4 GF4.
  (* io_send and the store keep each write right of the caller outside G and outside the call's window *)
  assert (VK : forall a, 0 <= a < 2 ^ 64 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
    ~ inG TG.G_HARNESS_B a -> (a < spZ regs - SENDCTL_STK \/ spZ regs <= a) ->
    aview segs (w_H W3) m4 a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hw HnG Hoff. rewrite (VW4 a Ha (NTX a HnG)). rewrite <- (V1 (w_H W2) a).
    destruct HK3 as (L1 & L2 & _ & L4 & _).
    assert (HnE : ~ iosend_wr SENDCTL_F a) by (intros X; exact (HnG (scs_iosend_G a X))).
    destruct Hw as [Hw | [(_ & b & n & Hb & Hr) | [(b & n & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
    - apply L1; lia.
    - pose proof (L2 b n (a - b) (Hbl _ Hb) ltac:(lia) ltac:(replace (b + (a - b)) with a by lia; exact HnE)) as X.
      replace (b + (a - b)) with a in X by lia. exact X.
    - pose proof (L2 b n (a - b) (Hbl _ Hb) ltac:(lia) ltac:(replace (b + (a - b)) with a by lia; exact HnE)) as X.
      replace (b + (a - b)) with a in X by lia. exact X.
    - apply (L4 c0 p0 a (HfrSc _ (Hown _ Hc))); [|exact HnE].
      unfold frame_rng. cbn [fst snd]. rewrite !Efa. exact Hr. }
  (* the saved words and the frame's bytes *)
  assert (VS : forall a, spZ regs - 96 <= a < spZ regs -> aview segs (w_H W3) m4 a = aview segs (w_H W2) mem2 a).
  { intros a Ha. rewrite (VW4 a ltac:(lia) ltac:(lia)). rewrite <- (V1 (w_H W2) a).
    destruct HK3 as (L1 & _). apply L1; lia. }
  assert (VF : forall a, F <= a < F + 256 -> aview segs (w_H W3) m4 a = aview segs (w_H W2) mem2 a).
  { intros a Ha. pose proof (NGF a Ha) as HnG. rewrite (VW4 a ltac:(lia) (NTX a HnG)). rewrite <- (V1 (w_H W2) a).
    destruct HK3 as (_ & _ & _ & L4 & _).
    apply (L4 SENDCTL_CID pos a Hin); [|intros X; exact (HnG (scs_iosend_G a X))].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes SENDCTL_CID) with 256. lia. }
  (* what the call kept: the cut's, over run 1, io_send's and the store *)
  assert (K1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (gover (sendctl_outs kp klp) m1 memc)
    (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp)).
  { apply (acall_kept_g_mem_ext segs B TG.G_HARNESS_B lyc Sc W memc W2 (gover (sendctl_outs kp klp) mem2 memc));
      [intros x; unfold gover; rewrite M1; reflexivity | exact HK]. }
  assert (L : acall_kept_g segs B TG.G_HARNESS_B ly2 S2 W2 (gover (sendctl_outs kp klp) m1 memc)
    W3 (gover (sendctl_outs kp klp) mem3 memc) (sp1 - IOSEND_STK) sp1 (iosend_wr SENDCTL_F))
    by exact (acall_kept_g_gover B TG.G_HARNESS_B (sendctl_outs kp klp) ly2 S2 W2 W3 m1 mem3 memc md1'
      (sp1 - IOSEND_STK) sp1 (iosend_wr SENDCTL_F) LAWS HAR1 ltac:(lia) ltac:(lia) HOUTP HK3).
  assert (K2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (gover (sendctl_outs kp klp) mem3 memc)
    (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp))
    by exact (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 _ W3 _ (spZ regs - SENDCTL_STK) (spZ regs)
      (sp1 - IOSEND_STK) sp1 (sendctl_wr kp klp) (iosend_wr SENDCTL_F) (fun _ => False)
      Hce ltac:(lia) Efa HfrSc Hbl (fun _ _ _ _ _ X => X) (fun _ _ _ _ _ X => X) K1 L ltac:(lia) ltac:(lia)
      (fun a X => or_introl (or_intror (or_introl X)))).
  unfold sendctl_rel_cur, sendctl_cur.
  refine (conj (conj HJ4 (conj He (conj _ (conj (Permutation_trans Hperm3 Hperm) (conj ELF3 (conj _
    (conj _ (conj _ (conj _ _))))))))) (conj TW4 (conj GF4 _))).
  - rewrite Hfr3. exact Hfrs.
  - exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
  - apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W3
      (gover (sendctl_outs kp klp) mem3 memc) (gover (sendctl_outs kp klp) m4 memc) (spZ regs - SENDCTL_STK) (spZ regs)
      (sendctl_wr kp klp) (fun x => SENDCTL_S + 18192 <= x < SENDCTL_S + 18200) HARc K2).
    + intros a Ha Hn. apply scs_gover_view. intros _. exact (VW4 a Ha Hn).
    + intros a Hp. exact (scs_gover_pres _ (w_H W3) mem3 m4 memc a (P4 a) Hp).
    + intros a Ha Hc. cbv beta in Ha. lia.
    + intros b m i _ _ Ha. cbv beta in Ha. left. unfold twb_fld, TW.A_S_stats_tx_frames, TW.OFF_g_s.
      unfold SENDCTL_S in Ha. lia.
    + intros a Ha _ HnG _ _. cbv beta in Ha. apply HnG. apply scs_inG. unfold TW.SZ_g_s. lia.
    + intros c p a _ _ Ha. cbv beta in Ha. left. unfold twb_fld, TW.A_S_stats_tx_frames, TW.OFF_g_s.
      unfold SENDCTL_S in Ha. lia.
  - apply Forall_forall. intros o Hino. pose proof (scs_saved_rng o Hino) as Ho.
    rewrite <- (proj1 (Forall_forall _ _) Hsaved o Hino). apply rdword_ext. intros i Hi. apply VS. lia.
  - unfold SENDCTL_FBYTES. rewrite <- HFLw. apply rdword_ext. intros i Hi. apply VF. lia.
  - destruct HKP as [Hk0 | (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TWKL & _ & _ & NGKL & _)]; [left; exact Hk0|].
    right. intros i Hi.
    destruct (TWKL (klp + i) ltac:(lia)) as [(Hw & _) | HGa]; [|exfalso; exact (NGKL (klp + i) ltac:(lia) HGa)].
    exact (PRES ly3 S3 W3 m4 md4 _ HJ4 (Permutation_trans Hperm3 Hperm) ELF3 Hw).
  - destruct HOUT as [Hk0 | (GK & GKL)]; [left; exact Hk0|].
    destruct HKP as [Hk0 | (_ & _ & TWK & RDK & OWK & NGK & LK & _ & _ & _ & TWKL & RDKL & OWKL & NGKL & LKL & _ & _)];
      [left; exact Hk0|].
    right.
    destruct RDK as (_ & _ & _ & _ & Hkp0 & Hkpn). destruct RDKL as (_ & _ & _ & _ & Hklp0 & Hklpn).
    unfold decode_off_win in OWK, OWKL. rewrite FS in *.
    assert (LZK : length (TW.zs (match f with [] => K | _ => f end)) = 60%nat).
    { unfold TW.zs. rewrite length_map. clear - Hlenf.
      destruct f as [|b0 f0]; [change (Z.to_nat SENDCTL_F) with 60%nat in Hlenf; discriminate Hlenf | exact Hlenf]. }
    assert (LZKL : length (TW.zs (match f with [] => KL | _ => TW.put 8 (Z.of_nat (length f)) end)) = 8%nat).
    { unfold TW.zs. rewrite length_map. clear - LKL.
      destruct f as [|b0 f0]; [exact LKL | apply TWL.length_put]. }
    split.
    + apply (scs_garr8_kept (w_H W2) (w_H W3) mem2 m4 kp _); [|exact GK].
      intros j Hj. rewrite LZK in Hj. change (Z.of_nat 60) with 60 in Hj.
      destruct (TWK (kp + j) ltac:(lia)) as [(Hw & _) | HGj]; [|exfalso; exact (NGK (kp + j) ltac:(lia) HGj)].
      exact (VK (kp + j) ltac:(lia) Hw (NGK (kp + j) ltac:(lia)) ltac:(lia)).
    + apply (scs_garr8_kept (w_H W2) (w_H W3) mem2 m4 klp _); [|exact GKL].
      intros j Hj. rewrite LZKL in Hj. change (Z.of_nat 8) with 8 in Hj.
      destruct (TWKL (klp + j) ltac:(lia)) as [(Hw & _) | HGj]; [|exfalso; exact (NGKL (klp + j) ltac:(lia) HGj)].
      exact (VK (klp + j) ltac:(lia) Hw (NGKL (klp + j) ltac:(lia)) ltac:(lia)). }
(* ---- run 2, +0x22c .. `bnez a0` at +0x230 ---- *)
clear HEI EE1.
destruct (scs_entry2 ly3 S3 W3 regs3 mem3 md3 B1 HSC HAR3 HTW3 V19 V26) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (scs_E2 regs3 B1)) by (unfold scs_E2; apply Eimg_env).
assert (EE2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (scs_E2 regs3 B1) n = YK11.getr regs3 rr)
  by (intros n rr Hn; unfold scs_E2; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U19b : bv_unsigned (ew (scs_E2 regs3 B1) 19) = SENDCTL_S)
  by (rewrite (EE2 19%nat 19%bv eq_refl), V19; apply unsigned_lit_small; lia).
set (old := TW.u_at B1 (TW.OFF_g_s + 18192) 8).
assert (R32b : 0 <= old < 2 ^ 64) by exact (TWL.u_at_range B1 _ 8).
assert (U32b : bv_unsigned (ew (scs_E2 regs3 B1) 32) = old).
{ unfold scs_E2. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs3 _ 0).
  apply unsigned_lit_small. exact R32b. }
assert (D10 : sv_denot (scs_E2 regs3 B1) (SOff 10 0) = w64 r)
  by (cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10_3).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg _ ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + SCS_C2)) mem3 (YK11.seg_rom segs)) mdx) Q) end.
pose proof HJ3 as HJ.
paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
{ scs_awr_rs. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19b in Ha.
  apply scs_inG. unfold TW.SZ_g_s. lia. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms2a end.
rename HF into HF2a, HFr into HFr2a, HG into HG2a.
psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
- (* r <> 0: the world is io_send's *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (scs_E2 regs3 B1) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  assert (Hr0 : r <> 0) by (intros Hr; rewrite Hr in Hc; vm_compute in Hc; discriminate Hc).
  destruct HBW as [(Hr & _) | (_ & EBw')]; [exfalso; exact (Hr0 Hr)|].
  paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan SENDCTL_REL.
  { scs_awr_rs. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19b in Ha.
    apply scs_inG. unfold TW.SZ_g_s. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms4 end.
  assert (VT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SENDCTL_S + 18192 <= a < SENDCTL_S + 18200) ->
    aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn.
    rewrite (YC4b.kept_of_frame _ _ (w_H W3) (ms_mem ms2a) (ms_mem ms4) (fun x => SENDCTL_S + 18192 <= x < SENDCTL_S + 18200)
      HFr ltac:(intros b wlo whi x Hwi Hx; cbv beta; scs_win Hwi Hx U19b) a Ha Hn).
    exact (YC4b.kept_of_frame _ _ (w_H W3) mem3 (ms_mem ms2a) (fun x => SENDCTL_S + 18192 <= x < SENDCTL_S + 18200)
      HFr2a ltac:(intros b wlo whi x Hwi Hx; cbv beta; scs_win Hwi Hx U19b) a Ha Hn). }
  assert (PT3 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG2a Ha))).
  (* tx_frames is unchanged *)
  scs_region HS 0%nat HRtx.
  pose proof (can_field_of_region (segs := segs) _ _ 19 SENDCTL_S _ 18192 18200 18192 18200 18192 8%N
    (SOff 32 0) old HRtx U19b ltac:(cbn [In]; auto)
    ltac:(cbn [sv_denot]; rewrite U32b, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VT.
  pose proof (tw_read_val segs (mrestrict (w_H W3) mem3) TMAP_B B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18192 8 TMAP_B_ok HTW3
    TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as VM3.
  assert (VALL : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. destruct (Z_lt_le_dec a (SENDCTL_S + 18192)) as [Hl|Hl]; [apply VT3; lia|].
    destruct (Z_lt_le_dec a (SENDCTL_S + 18200)) as [Hh|Hh]; [|apply VT3; lia].
    replace a with (SENDCTL_S + 18192 + (a - (SENDCTL_S + 18192))) by lia.
    apply (scs_view_of_vals (w_H W3) (w_H W3) mem3 (ms_mem ms4) (SENDCTL_S + 18192) 8 old VM3 VT).
    change (Z.of_nat 8) with 8. lia. }
  assert (TW4 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms4)) Bw').
  { rewrite EBw'. apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact HTW3|].
    intros x (o & b & n & Hino & Hx). pose proof (tw_row TMAP_B o b n TMAP_B_ok Hino) as (_ & _ & _ & Hb0 & Hb64).
    apply VALL. lia. }
  assert (GF4 : TW.g_fail_next Bw' <= 1).
  { rewrite EBw', (TIF.io_send_m_fail_next _ _ _ _ _ HIO (tw_len _ _ _ HTW0)). lia. }
  scs_reg HS (2%bv : bv 5) (YK11.getr regs3 2) Y2
    ltac:(cbn [sv_denot]; rewrite (EE2 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (3%bv : bv 5) (YK11.getr regs3 3) Y3
    ltac:(cbn [sv_denot]; rewrite (EE2 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (4%bv : bv 5) (YK11.getr regs3 4) Y4
    ltac:(cbn [sv_denot]; rewrite (EE2 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (8%bv : bv 5) (YK11.getr regs3 8) Y8
    ltac:(cbn [sv_denot]; rewrite (EE2 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (9%bv : bv 5) (YK11.getr regs3 9) Y9
    ltac:(cbn [sv_denot]; rewrite (EE2 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (18%bv : bv 5) (YK11.getr regs3 18) Y18
    ltac:(cbn [sv_denot]; rewrite (EE2 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (24%bv : bv 5) (YK11.getr regs3 24) Y24
    ltac:(cbn [sv_denot]; rewrite (EE2 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (25%bv : bv 5) (YK11.getr regs3 25) Y25
    ltac:(cbn [sv_denot]; rewrite (EE2 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (27%bv : bv 5) (YK11.getr regs3 27) Y27
    ltac:(cbn [sv_denot]; rewrite (EE2 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (21%bv : bv 5) (w64 r) Y21
    ltac:(cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10_3).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SENDCTL_REL)) mm rom) mdx) Q) end.
  apply (REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
    pos sp1 F ly3 S3 W3 (ms_mem ms4) _ e (ms_regs ms4) HFIX).
  + exact (CLOSE (ms_mem ms4) _ Bw' HJ VT3 PT3 TW4 GF4).
  + exact (REGS (ms_regs ms4) Y2 Y3 Y4 Y8 Y9 Y18 Y24 Y25 Y27 Y21).
- (* r = 0: the store of tx_frames + 1 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (scs_E2 regs3 B1) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  destruct (TIF.io_send_m_ret _ _ _ _ _ HIO) as [Hr0 | Hr0];
    [| exfalso; rewrite Hr0 in Hc; vm_compute in Hc; discriminate Hc].
  destruct HBW as [(_ & EBw') | (Hr & _)]; [| exfalso; exact (Hr Hr0)].
  paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan SENDCTL_REL.
  { scs_awr_rs. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19b in Ha.
    apply scs_inG. unfold TW.SZ_g_s. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms4 end.
  assert (VT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SENDCTL_S + 18192 <= a < SENDCTL_S + 18200) ->
    aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn.
    rewrite (YC4b.kept_of_frame _ _ (w_H W3) (ms_mem ms2a) (ms_mem ms4) (fun x => SENDCTL_S + 18192 <= x < SENDCTL_S + 18200)
      HFr ltac:(intros b wlo whi x Hwi Hx; cbv beta; scs_win Hwi Hx U19b) a Ha Hn).
    exact (YC4b.kept_of_frame _ _ (w_H W3) mem3 (ms_mem ms2a) (fun x => SENDCTL_S + 18192 <= x < SENDCTL_S + 18200)
      HFr2a ltac:(intros b wlo whi x Hwi Hx; cbv beta; scs_win Hwi Hx U19b) a Ha Hn). }
  assert (PT3 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG2a Ha))).
  (* tx_frames holds old + 1 *)
  scs_region HS 0%nat HRtx.
  pose proof (can_field_of_region (segs := segs) _ _ 19 SENDCTL_S _ 18192 18200 18192 18200 18192 8%N
    (SOff 32 1) (TS0.u64 (old + 1)) HRtx U19b ltac:(cbn [In]; auto)
    ltac:(cbn [sv_denot]; rewrite U32b; unfold TS0.u64; apply scs_z2bv_mod)
    ltac:(unfold TS0.u64; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)
    ltac:(cbn; lia)) as VT.
  assert (TW4 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms4)) Bw').
  { rewrite EBw', scs_tx_get. exact (scs_tw_tx (w_H W3) mem3 (ms_mem ms4) B1 _ HTW3 VT VT3). }
  assert (GF4 : TW.g_fail_next Bw' <= 1).
  { rewrite EBw', (scs_gf_tx _ _ (tw_len _ _ _ HTW3)), (TIF.io_send_m_fail_next _ _ _ _ _ HIO (tw_len _ _ _ HTW0)).
    lia. }
  scs_reg HS (2%bv : bv 5) (YK11.getr regs3 2) Y2
    ltac:(cbn [sv_denot]; rewrite (EE2 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (3%bv : bv 5) (YK11.getr regs3 3) Y3
    ltac:(cbn [sv_denot]; rewrite (EE2 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (4%bv : bv 5) (YK11.getr regs3 4) Y4
    ltac:(cbn [sv_denot]; rewrite (EE2 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (8%bv : bv 5) (YK11.getr regs3 8) Y8
    ltac:(cbn [sv_denot]; rewrite (EE2 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (9%bv : bv 5) (YK11.getr regs3 9) Y9
    ltac:(cbn [sv_denot]; rewrite (EE2 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (18%bv : bv 5) (YK11.getr regs3 18) Y18
    ltac:(cbn [sv_denot]; rewrite (EE2 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (24%bv : bv 5) (YK11.getr regs3 24) Y24
    ltac:(cbn [sv_denot]; rewrite (EE2 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (25%bv : bv 5) (YK11.getr regs3 25) Y25
    ltac:(cbn [sv_denot]; rewrite (EE2 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (27%bv : bv 5) (YK11.getr regs3 27) Y27
    ltac:(cbn [sv_denot]; rewrite (EE2 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  scs_reg HS (21%bv : bv 5) (w64 r) Y21 ltac:(rewrite Hr0; reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SENDCTL_REL)) mm rom) mdx) Q) end.
  apply (REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
    pos sp1 F ly3 S3 W3 (ms_mem ms4) _ e (ms_regs ms4) HFIX).
  + exact (CLOSE (ms_mem ms4) _ Bw' HJ VT3 PT3 TW4 GF4).
  + exact (REGS (ms_regs ms4) Y2 Y3 Y4 Y8 Y9 Y18 Y24 Y25 Y27 Y21).
Qed.

End send.

Print Assumptions sendctl_send.
