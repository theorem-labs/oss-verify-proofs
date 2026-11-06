(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1878 of its 1989 lines of code are new or changed and 815 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_tail.v, with its module paths and module names changed; 621 of its 750 lines of code are new or changed and 1860 lines of the source are left out. *)
(* io_send_seg_e2a: the E2 arm of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry 0x82d60 =
   TImgA.v ti_io_send timg_A; the frozen statement is lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt),
   0x8312c .. 0x8315c = transport_text + IOS_AT 0x3cc .. + 0x3fc.

   The code (io_send_cg.v header lines 115-119), with sp = the walk's sp (the entry sp less IOSEND_FRAME = 160):
     0x8312c            `jal` check_state_wake (0x84370), return address 0x83130; the call takes no argument;
     0x83130 - 0x83134  a0 = sp + 8 (the struct spec_frame f); `jal` check_latest_control (0x8420c), return
                        address 0x83138;
     0x83138 - 0x83148  a1 = GOT.e2 (the 4-byte load at 0x5e53a4 = GOT + 196, sign-extended), a2 = f.send (the
                        4-byte load at sp + 40, sign-extended), a1 + 1 stored back at GOT.e2 (`sw a1, 620(a0)`
                        with a0 the %hi of object 53);
     0x8314c - 0x83154  a0 = the %hi of object 54 (g_last_counter + 12), a1 = s3 & 1, the 4-byte store of a2 at
                        g_last_counter (`sw a2, -12(a0)`);
     0x83158 - 0x8315c  a1 = 0 goes to 0x83338 (= transport_text + IOS_FLY), else `j` 0x83384 (= + IOS_EPI).

   ios_e2_arm is SELF-CONTAINED: its premises are the callee contracts and record facts (io_send_seg_e2.v
   ios_e2_laws), the entry facts of the walk (io_send_seg_cut.v ios_fix), the state at the arm's entry
   (io_send_seg_e2.v ios_e2_at at the world io_send_segs.v ios_B0 Bw) and the model's dispatch
   (io_send_segs.v ios_arm); it concludes, in continuation form, the two exits of the arm. Both continuations are
   io_send_seg_e2.v ios_e2_seg_stmt's, word for word.

   How:
   - the two LEAF calls (ie2a_calls): io_send_seg_tail.v ios_leaf_call with ie2a_csw_leaf, an instance of the
     leaf form modelled on that file's ios_ckd_leaf / ios_cld_leaf (check_state_wake takes no argument and its one
     footprint row beyond its frame is M.foreign, check_state_wake_c.v CHECK_STATE_WAKE_FOREIGN); then
     io_send_seg_ack.v iak_call_clc, the call of check_latest_control from the same struct at sp + 8 the ACK and
     E3 arms make. Each leaf keeps the world and every byte outside its own ESTACK window, so the cut survives it
     (io_send_seg_e2.v ios_e2_keep over [sp - ESTACK, sp)).
   - the two stores (ie2a_tail): one paj_run_tok over io_send_seg_e2.v ios_e2_state with the GOT.e2 and
     g_last_counter write windows, to the stop at IOS_AT 0x3f8; the world after them is two
     io_send_seg_world.v ios_tw_step (the GOT row at A_GOT_e2, 4 bytes of int_inc (GOT_e2 Bx); the
     g_last_counter row, 4 bytes of f.send), both bytes of iosend_wr (ios_wr_got_e2 / ios_wr_lastc), and the
     running kept fact is io_send_seg_csf.v ics_kept_step.
   - the split on `s3 & 1` (ie2a_br_and1): s3 is the unsigned byte of g_fail_next the entry read, 0 or 1 by
     ios_fix, so the machine's test is the model's `truth (g_fail_next Bw)`; bit clear is the frame in flight
     (io_send_segs.v ios_arm_e2's second case), bit set the epilogue (its first case). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA DgnTransportCgRun DgnTransportLeafb CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_state_wake_c check_latest_control_c check_state_wake_cg check_latest_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
io_send_cg io_send_segs io_send_seg_cut io_send_seg_world io_send_seg_frm io_send_seg_src io_send_seg_csf.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
io_send_seg_tail io_send_seg_ack io_send_seg_e2.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame ExecF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_c.
Module LLCc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_c.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* Values and registers                                                *)
(* ------------------------------------------------------------------ *)

(* A 32-bit value through the sign extension the stores write back: the byte a store writes is the byte of the
   value itself, since le_byte reads only the low 32 bits. *)
Lemma ie2a_swrap_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
change (2 ^ 32) with 4294967296. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma ie2a_le_byte_swrap : forall v j, YO0f.le_byte (bv_swrap 32 v) 4 j = YO0f.le_byte v 4 j.
Proof.
intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite ie2a_swrap_mod. reflexivity.
Qed.

(* GOT.e2 and the two stores of this stretch, as the world holds them. *)
Lemma ie2a_got_e2 : forall Bx, TW.GOT_e2 Bx = bv_swrap 32 (TW.u_at Bx TW.A_GOT_e2 4).
Proof. reflexivity. Qed.
Lemma ie2a_set_e2 : forall Bx v, TW.set_GOT_e2 Bx v = TW.upd Bx TW.A_GOT_e2 (TW.put 4 v).
Proof. reflexivity. Qed.
Lemma ie2a_set_lastc : forall Bx v,
  TW.set_g_last_counter Bx v = TW.upd Bx TW.OFF_g_last_counter (TW.put 4 v).
Proof. reflexivity. Qed.

(* The branch of 0x83158 on bit 0 of s3: s3 is the byte of g_fail_next the entry read, 0 or 1. *)
Lemma ie2a_br_and1 : forall (E : env) n u, ew E n = Z_to_bv 64 u -> 0 <= u <= 1 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = (u =? 0).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
assert (E01 : u = 0 \/ u = 1) by lia.
destruct E01 as [E1 | E1]; subst u; vm_compute; reflexivity.
Qed.

(* The register indices the calls' lemmas name as Z_to_bv 5 n. *)
Lemma ie2a_i1 : Z_to_bv 5 1 = 1%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i2 : Z_to_bv 5 2 = 2%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i3 : Z_to_bv 5 3 = 3%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i4 : Z_to_bv 5 4 = 4%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i10 : Z_to_bv 5 10 = 10%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* Every register io_send_seg_e2.v ios_e2_kept names is callee-saved, so a call keeps it. *)
Lemma ie2a_kept_of_pres : forall rg rg2 : bvmap 5 word, aregs_preserved rg rg2 ->
  forall r, In r ios_e2_kept -> YK11.getr rg2 r = YK11.getr rg r.
Proof.
intros rg rg2 HP r Hr. apply (iak_ap rg rg2 r HP). unfold ios_e2_kept in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
        [unfold acallee_saved;
         lazymatch goal with |- context [bv_unsigned ?x] =>
           let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
         lia |]).
destruct Hr.
Qed.

(* The bytes of G this stretch stores: GOT.e2 and g_last_counter. *)
Definition ie2a_wr (a : Z) : Prop :=
  (TA_GOT + 196 <= a < TA_GOT + 196 + 4) \/ (TA_g_last_counter <= a < TA_g_last_counter + 4).

Lemma ie2a_wr_inG : forall a, ie2a_wr a -> inG TG.G_HARNESS a.
Proof.
intros a [Ha | Ha].
- apply (ios_inG_row _ _ _ a TMAP_A_GOT). unfold TW.SZ_GOT. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_g_last_counter). unfold TW.SZ_g_last_counter. lia.
Qed.

Lemma ie2a_wr_iosend : forall n a, ie2a_wr a -> iosend_wr n a.
Proof.
intros n a [Ha | Ha]; [apply ios_wr_got_e2 | apply ios_wr_lastc]; lia.
Qed.

(* The frame never holds a byte of ie2a_wr: it is outside G, or inside g_s, which holds neither word. *)
Lemma ie2a_frame_off : forall p n a, iosend_frame_at p n -> p <= a < p + n -> ~ ie2a_wr a.
Proof.
intros p n a HFAT Ha HW.
assert (EG : TA_GOT = 6181600) by reflexivity.
assert (EL : TA_g_last_counter = 6156608) by reflexivity.
assert (ES : TA_g_s = 6158784) by reflexivity.
assert (SS : TW.SZ_g_s = 18264) by reflexivity.
destruct HFAT as [HnG | (Hlo & Hhi)].
- exact (HnG a Ha (ie2a_wr_inG a HW)).
- destruct HW as [HW | HW]; lia.
Qed.

(* The write right of a run whose state has no writable window (io_send_seg_tail.v ios_awr_nil) and the model
   term after a run, named and opaque (io_send_seg_ack.v iak_md): each of those files keeps its Ltac inside its
   Section, which forgets it at End, so this file carries its own. *)
Ltac ie2a_awr_nil :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

Ltac ie2a_md := lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
  let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv end.

(* The two regions this stretch writes, read back from a state of the run: GOT.e2 (index 3 of
   io_send_seg_e2.v ios_e2_regions) and g_last_counter (index 4). *)
Ltac ie2a_stored HS Re Rl :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ss) ios_e2_rstk) in
    pose proof (st_ok_pi_region_nth Ex ss (restrict Hh m) 3 r3 HS ltac:(vm_compute; reflexivity)) as Re;
    let r4 := eval vm_compute in (nth 4 (ss_mem ss) ios_e2_rstk) in
    pose proof (st_ok_pi_region_nth Ex ss (restrict Hh m) 4 r4 HS ltac:(vm_compute; reflexivity)) as Rl
  end;
  cbn [ms_mem restrict] in Re, Rl.

Section e2a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* ------------------------------------------------------------------ *)
(* check_state_wake through the leaf form                              *)
(* ------------------------------------------------------------------ *)

(* The footprint premises of check_state_wake at a call state whose sp is above G: its own 16-byte frame and the
   4 bytes of M.foreign it loads (check_state_wake_c.v:48-53). Form: io_send_seg_tail.v ios_ckd_leaf. *)
Lemma ie2a_csw_leaf : forall (W : world segs) regsT memT mdc ly2 S2 B5,
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') ->
  tw_at TMAP_A (aview segs (w_H W) memT) B5 -> TC.check_state_wake_m B5 = Some (B5, tt) ->
  TG.G_HARNESS_HI + ESTACK <= spZ regsT -> spZ regsT <= 2 ^ 47 ->
  LB.decode_leafb_ecall_pre B ly2 S2 W regsT memT mdc ->
  SRr segs W (@LCK.cfg_at fx (transport_sigma TS_check_state_wake) regsT memT mdc)
    (LB.decode_leafb_post B ly2 S2 W regsT memT mdc None [] (fun _ => B5 = B5)).
Proof.
intros W regsT memT mdc ly2 S2 B5 HL Htw Hm Hlo Hhi HPRE.
pose proof (HL fx ly2 S2 W regsT memT mdc (spZ regsT - CSW.CHECK_STATE_WAKE_FRAME) B5 B5 HPRE) as HC.
cbv zeta in HC.
change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT) in HC.
change CSW.CHECK_STATE_WAKE with (transport_sigma TS_check_state_wake) in HC.
unfold LB.decode_leafb_ecall_pre, LCK.ecall_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & Hpres & _).
change (LCK.spZ regsT) with (spZ regsT) in Hpres.
assert (EST : LCK.ESTACK = 4096) by reflexivity. rewrite EST in Hpres.
assert (FR : CSW.CHECK_STATE_WAKE_FRAME = 16) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity.
unfold CSW.CHECK_STATE_WAKE_FOREIGN, TW.A_M_foreign, TW.OFF_M in HC.
assert (GLO : TG.G_HARNESS_LO = 0x5df080) by reflexivity.
assert (SM : TW.SZ_M = 1648) by reflexivity.
apply HC.
- exact (ios_csw W memT B5 Htw).
- exact Hm.
- apply (LB.decode_leafb_stk W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- lia.
- unfold AKA.off_stk. left. change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT). lia.
- apply (LB.decode_leafb_rng_vis W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_M. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Carrying the cut across the two stores                              *)
(* ------------------------------------------------------------------ *)

(* io_send_seg_e2.v ios_e2_keep for a stretch that writes bytes of G instead of bytes below sp: the harness
   globals' two words are not read by any other fact of the cut (the saved words and the struct lie above
   sp - IOSEND_FRAME, the shadow band above kLowMemEnd, the frame outside G or inside g_s), so every fact but the
   world relation survives; the world after the stores comes in as a premise. *)
Lemma ie2a_keep_g : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) mem4 md4 (regs4 : bvmap 5 word) Bx By,
  AR_laws segs B ->
  ios_e2_fix B STK sp0 regs p frame -> 60 <= Z.of_nat (length frame) ->
  iosend_frame_at p (Z.of_nat (length frame)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
     aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W3 mem4 md4 ->
  ios_regs regs regs4 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  tw_at TMAP_A (aview segs (w_H W3) mem4) By ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem4 md4 regs4 By.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
  ly3 S3 W3 mem3 md3 regs3 mem4 md4 regs4 Bx By LAWS FIX H60 HFAT KV AT CUR RG R24 HTW4.
destruct AT as (CUR3 & SAVED & RG3 & R243 & SFR & SRCS & GARR & SRCF & HTW).
destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47 & Hra & Hra4 & Hgp & Htp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EF : IOSEND_FRAME = 160) by reflexivity.
assert (EO : IOS_F_OFF = 8) by reflexivity.
assert (ES : SF_SIZE = 80) by reflexivity.
assert (EIS : IOSEND_STK = 8496) by reflexivity.
assert (EG : TA_GOT = 6181600) by reflexivity.
assert (EL : TA_g_last_counter = 6156608) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof CUR3 as (HJ3 & _).
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof (proj1 HJi3) as HAR3.
(* where the frame lies: a heap block or a fake frame below alloc_ceiling, G, or the machine stack *)
pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 p (Z.of_nat (length frame)) HAR3 SRCF
              ltac:(lia)) as HPL.
assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                aview segs (w_H W3) mem4 s = aview segs (w_H W3) mem3 s).
{ intros s Hs. apply KV; [lia|]. intros [HW | HW]; lia. }
split; [exact CUR|].
split.
{ (* the nine saved words, far above G *)
  apply (ios_saved_kept W3 W3 mem3 mem4 regs SAVED).
  intros a Ha. apply KV; [lia|]. intros [HW | HW]; lia. }
split; [exact RG|]. split; [exact R24|].
split.
{ (* the struct spec_frame at sp + 8 *)
  apply (ios_sframe_kept W3 W3 mem3 mem4 _ p (TC.rf frame)); [exact SFR|].
  intros a Ha. apply KV; [lia|]. intros [HW | HW]; lia. }
split.
{ exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4
          (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE SRCS
          (fun a Ha => KV a ltac:(lia) ltac:(intros [HW | HW]; lia)) KSH). }
split.
{ (* the frame's bytes *)
  apply (ios_garr8_kept (w_H W3) (w_H W3) mem3 mem4 p (map DSpec.bz frame) GARR).
  intros a Ha. rewrite length_map in Ha.
  apply KV; [destruct HPL as [Pl|Pl]; lia | exact (ie2a_frame_off p (Z.of_nat (length frame)) a HFAT Ha)]. }
split.
{ exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4 p (Z.of_nat (length frame)) SRCF
          (fun a Ha => KV a ltac:(destruct HPL as [Pl|Pl]; lia)
                         (ie2a_frame_off p (Z.of_nat (length frame)) a HFAT Ha)) KSH). }
exact HTW4.
Qed.

(* ------------------------------------------------------------------ *)
(* The two leaf calls (0x8312c .. 0x83134)                             *)
(* ------------------------------------------------------------------ *)

(* From the E2 arm's head to the return of check_latest_control: `jal` check_state_wake, a0 = sp + 8,
   `jal` check_latest_control. Neither callee writes a byte of G or of io_send's frame, so the cut and its world
   reach 0x83138 unchanged. *)
Lemma ie2a_calls : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail cmd : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
  transport_cells B -> AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') ->
  @AR rc segs B lyc Sc W memc mdc ->
  ios_e2_fix B STK sp0 regs p frame -> 60 <= Z.of_nat (length frame) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  YK11.getr regs3 21 = w64 cmd ->
  TC.check_state_wake_m Bx = Some (Bx, tt) ->
  TC.check_latest_control_m Bx frame = Some (Bx, tt) ->
  (forall mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem5 md5 regs5 Bx ->
     YK11.getr regs5 21 = w64 cmd ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3d8) regs5 mem5 md5) Q) ->
  SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3cc) regs3 mem3 md3) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail cmd
  ly3 S3 W3 mem3 md3 regs3 Bx Q HCELLS LAWS HGX LCSW LCLC HARc FIX H60 AT R21 HMW HMC HK.
pose proof AT as AT0.
pose proof FIX as FIX0.
destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47r & Hra & Hra4 & Hgp & Htp).
destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity.
assert (EO : IOS_F_OFF = 8) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* the entry sp of the walk, from the journal inside ios_cur *)
pose proof HJ as (HSTKj & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & HSTK0 & Hceil0 & Hslo1 & Hshi1 & H47 & _).
clear HJ0 memS0.
set (sp := spZ regs - IOSEND_FRAME) in *.
assert (Esp : sp = spZ regs - IOSEND_FRAME) by reflexivity.
assert (Hsp16' : sp mod 16 = 0).
{ rewrite Esp, FF. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hsp16. }
assert (Hsp3 : spZ regs3 = sp)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
change IOS_F_OFF with 8 in SFR, SRCS.
(* ---- run 1 (0x8312c): `jal` check_state_wake ---- *)
set (E0 := ios_E0 regs3).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ios_E0; apply Eimg_env).
assert (EWR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E0, ios_E0; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (ios_e0_entry W3 regs3 mem3 (IOS_AT 0x3cc)) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs IOS_Bx [] E0 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
              TG.G_HARNESS HGX 0 []) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_AT 0x3cc)) mem3
    (YK11.seg_rom segs)) md3) Qx) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ie2a_awr_nil. }
ie2a_md. rename ms into ms1.
assert (KC1 : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. exfalso. vm_compute in Hin. exact Hin. }
assert (GC1 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (HPC1 : aregs_preserved regs3 (ms_regs ms1)).
{ apply (aregs_preserved_of_st_ok segs (w_H W3) E0 _ ms1 regs3 [] HS).
  - exact (ios_e0_agree regs3).
  - vm_compute. reflexivity. }
pose proof (ie2a_kept_of_pres regs3 (ms_regs ms1) HPC1) as KR1.
pmkst HS.
ics_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_AT 0x3d0)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (Q2 : YK11.getr (ms_regs ms1) 2 = w64 sp)
  by (rewrite (KR1 2%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)); exact R2).
assert (Q3 : YK11.getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (rewrite (KR1 3%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), R3; exact Hgp).
assert (Q4 : YK11.getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (rewrite (KR1 4%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), R4; exact Htp).
assert (Hspc1 : spZ (ms_regs ms1) = sp)
  by (unfold spZ at 1; rewrite Q2; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_check_state_wake)) mm rom) mdx) Qx)
  end.
apply (ios_leaf_call B W3 (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 mdv (k + 0)
  (sp - sp0) (transport_sigma TS_check_state_wake) (fun _ => Bx = Bx) Q LAWS HJ).
- rewrite Hspc1. lia.
- rewrite Esp, FF. replace (spZ regs - 160 - sp0) with (spZ regs - sp0 + (-10) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity.
- lia.
- lia.
- rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transport));
    [unfold IOS_AT, AF_io_send; lia | reflexivity].
- exact Q3.
- exact Q4.
- intros HPRE.
  apply (ie2a_csw_leaf W3 (ms_regs ms1) (ms_mem ms1) mdv ly3 S3 Bx LCSW); [| exact HMW | lia | lia | exact HPRE].
  apply (tw_kept TMAP_A _ _ Bx HTW). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KC1. lia.
- intros regs4 mem4 md4 HJ4 HP4 HK4 HG4 _.
  rewrite Q1.
  assert (KR2 : forall r, In r ios_e2_kept -> YK11.getr regs4 r = YK11.getr regs3 r)
    by (intros r Hr; rewrite (ie2a_kept_of_pres _ _ HP4 r Hr); exact (KR1 r Hr)).
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
    aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite (HK4 a Ha ltac:(rewrite Hspc1; exact Hn)). exact (KC1 a Ha). }
  assert (GV2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a)
    by (intros a Ha; exact (HG4 a (GC1 a Ha))).
  (* ---- run 2 (0x83130): a0 = sp + 8; `jal` check_latest_control ---- *)
  set (E1 := ios_E0 regs4).
  assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, ios_E0; apply Eimg_env).
  pose proof (ios_e0_entry W3 regs4 mem4 (IOS_AT 0x3d0)) as HS1. fold E1 in HS1.
  assert (SHOK1 : sh_ok segs IOS_Bx [] E1 (mrestrict (w_H W3) mem4)) by constructor.
  clear HS SHOK.
  rename HJ4 into HJ1.
  paj_run_tok RUN HS1 HJ1 SHOK1 YC4b.Bspan.
  { ie2a_awr_nil. }
  ie2a_md. rename ms into ms2.
  assert (KC3 : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem4 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. exfalso. vm_compute in Hin. exact Hin. }
  assert (GC3 : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (HPC2 : aregs_preserved regs4 (ms_regs ms2)).
  { apply (aregs_preserved_of_st_ok segs (w_H W3) E1 _ ms2 regs4 [] HS1).
    - exact (ios_e0_agree regs4).
    - vm_compute. reflexivity. }
  pose proof (ie2a_kept_of_pres regs4 (ms_regs ms2) HPC2) as KR3.
  pmkst HS1.
  ics_reg HS1 (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_AT 0x3d8)) P1 ltac:(apply codeptr_val; exact HEI1).
  ics_reg HS1 (10%bv : bv 5) (Z_to_bv 64 (sp + 8)) P10
    ltac:(cbn [sv_denot];
          rewrite (ew_Eimg_Ereg_nat regs4 (@nil word) 2%nat 2%bv eq_refl),
                  (KR2 2%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), R2;
          rewrite unsigned_lit_small by lia; reflexivity).
  assert (P2 : YK11.getr (ms_regs ms2) 2 = w64 sp).
  { rewrite (KR3 2%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (KR2 2%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)). exact R2. }
  assert (P3 : YK11.getr (ms_regs ms2) 3 = w64 (as_gp B)).
  { rewrite (KR3 3%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (KR2 3%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), R3. exact Hgp. }
  assert (P4 : YK11.getr (ms_regs ms2) 4 = w64 (as_tp B)).
  { rewrite (KR3 4%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (KR2 4%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), R4. exact Htp. }
  assert (Hspc2 : spZ (ms_regs ms2) = sp)
    by (unfold spZ at 1; rewrite P2; apply unsigned_lit_small; lia).
  (* the struct and the world at the call state *)
  assert (HSF2 : trans_sframe_at W3 (ms_mem ms2) (sp + 8) p (TC.rf frame)).
  { apply (ios_sframe_kept W3 W3 mem3 (ms_mem ms2) (sp + 8) p (TC.rf frame));
      [exact SFR|].
    intros a Ha. rewrite (KC3 a ltac:(lia)). apply KV2; lia. }
  assert (HTW2 : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms2)) Bx).
  { apply (tw_kept TMAP_A _ _ Bx HTW). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    rewrite (KC3 x ltac:(lia)). apply KV2; lia. }
  assert (HWIN : iak_call_win STK sp0 sp) by (split; [exact Hsp16' | split; lia]).
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 LLCc.CHECK_LATEST_CONTROL) mm rom) mdx) Qx) end.
  eapply SRr_bind.
  { refine (iak_call_clc B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms2) _ (k + 0)
      (ms_regs ms2) sp p frame Bx HCELLS LAWS LCLC HJ1 _ _ _ _ _ HWIN HSF2 HTW2 HMC).
    - rewrite ie2a_i2. exact P2.
    - rewrite ie2a_i10. exact P10.
    - rewrite ie2a_i1, P1. apply (ret_ok_codeptr_v (PI := PI_transport));
        [unfold IOS_AT, AF_io_send; lia | reflexivity].
    - rewrite ie2a_i3. exact P3.
    - rewrite ie2a_i4. exact P4. }
  intros W4 c4 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & _ & HK5 & HG5 & _).
  rewrite ie2a_i1, P1.
  (* ---- the cut at 0x83138 ---- *)
  assert (KR4 : forall r, In r ios_e2_kept -> YK11.getr regs5 r = YK11.getr regs3 r).
  { intros r Hr. rewrite (ie2a_kept_of_pres _ _ HP5 r Hr), (KR3 r Hr). exact (KR2 r Hr). }
  assert (KV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
    aview segs (w_H W3) mem5 a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn.
    rewrite (HK5 a Ha ltac:(rewrite Hspc2; exact Hn) ltac:(intros X; unfold LCK.in_wr in X; inversion X)).
    rewrite (KC3 a Ha). apply KV2; [exact Ha | exact Hn]. }
  assert (GV4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem5 a)
    by (intros a Ha; exact (HG5 a (GC3 a (GV2 a Ha)))).
  assert (CUR5 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 mem5 md5).
  { unfold ios_cur. split; [exact HJ5|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 mem3 mem5
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame)))
      (fun a => sp - ESTACK <= a < sp)
      LAWS HGX HARc HKEPT ltac:(intros a Ha Hn; exact (KV4 a Ha Hn)) GV4
      ltac:(intros a Ha; cbv beta in Ha; left; lia) ltac:(lia) ltac:(lia)). }
  destruct (ios_e2_regs_step regs regs3 regs5 p frame fail cmd RG R21 R24 KR4) as (RG5 & R215 & R245).
  apply (HK mem5 md5 regs5); [| exact R215].
  apply (ios_e2_keep B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
           ly3 S3 W3 mem3 md3 regs3 W3 mem5 md5 regs5 Bx (sp - ESTACK) sp
           LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(intros a Ha Hn; exact (KV4 a Ha Hn)) AT0 CUR5 RG5 R245).
Qed.

(* ------------------------------------------------------------------ *)
(* The two stores and the branch (0x83138 .. 0x8315c)                  *)
(* ------------------------------------------------------------------ *)

(* From the return of check_latest_control: GOT.e2 + 1 and g_last_counter = f.send, then the test of bit 0 of s3.
   Both stores are bytes of G in iosend_wr, so the running kept fact survives (ics_kept_step) and the world moves
   by two ios_tw_step. *)
Lemma ie2a_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail e2 : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> @AR rc segs B lyc Sc W memc mdc ->
  ios_e2_fix B STK sp0 regs p frame -> 60 <= Z.of_nat (length frame) ->
  iosend_frame_at p (Z.of_nat (length frame)) ->
  0 <= fail <= 1 ->
  TC.int_inc (TW.GOT_e2 Bx) = Some e2 ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  (forall mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem5 md5 regs5
       (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (DSpec.sf_send (TC.rf frame))) ->
     (forall r, In r ios_e2_kept -> YK11.getr regs5 r = YK11.getr regs3 r) ->
     fail = 0 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) regs5 mem5 md5) Q) ->
  (forall mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem5 md5 regs5
       (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (DSpec.sf_send (TC.rf frame))) ->
     (forall r, In r ios_e2_kept -> YK11.getr regs5 r = YK11.getr regs3 r) ->
     fail <> 0 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_EPI) regs5 mem5 md5) Q) ->
  SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3d8) regs3 mem3 md3) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail e2
  ly3 S3 W3 mem3 md3 regs3 Bx Q LAWS HGX HARc FIX H60 HFAT Hfail Hinc AT HFLY HEPI.
pose proof AT as AT0.
pose proof FIX as FIX0.
destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47r & Hra & Hra4 & Hgp & Htp).
destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* s5 travels beside the cut; this stretch neither reads nor writes it, so its value is named only here *)
assert (R21x : YK11.getr regs3 21 = w64 (bv_unsigned (YK11.getr regs3 21)))
  by (unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct (ios_e2_cut_vals B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
            ly3 S3 W3 mem3 md3 regs3 Bx AT0) as (V38 & V40 & V108 & Vnow & Ve2 & Z1 & Z2 & Z3 & Z4 & Z5).
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EG : TA_GOT = 6181600) by reflexivity.
assert (EL : TA_g_last_counter = 6156608) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* the run's state: the five regions, with the GOT.e2 and g_last_counter write windows *)
pose proof (ios_e2_state false true true (IOS_AT 0x3d8) (spZ regs - IOSEND_FRAME)
              (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr Bx) (ios_e2_now Bx) (ios_e2_e2v Bx)
              W3 regs3 mem3 R2 ltac:(lia) ltac:(lia) Z1 Z2 Z3 Z4 Z5 V38 V40 V108 Vnow Ve2) as HS0.
set (E0 := ios_e2_E regs3 (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr Bx) (ios_e2_now Bx)
             (ios_e2_e2v Bx)) in HS0.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ios_e2_E; apply Eimg_env).
assert (SHOK : sh_ok segs ios_e2_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (X33 : ew E0 33 = Z_to_bv 64 (ios_e2_snd frame))
  by (unfold E0, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (X36 : ew E0 36 = Z_to_bv 64 (ios_e2_e2v Bx))
  by (unfold E0, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 4)).
assert (X19 : ew E0 19 = Z_to_bv 64 fail)
  by (unfold E0, ios_e2_E; rewrite (ew_Eimg_Ereg_nat regs3 _ 19%nat 19%bv eq_refl); exact R19).
assert (U269 : bv_unsigned (ew E0 269%nat) = TA_GOT + 196)
  by (unfold E0, ios_e2_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U454 : bv_unsigned (ew E0 454%nat) = TA_g_last_counter + 12)
  by (unfold E0, ios_e2_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
(* the two bases the stores address, as facts of the state: without them the static check of the run
   (YP0j.v cells_safe_b) cannot place a write window against the runtime cells' span *)
assert (FA269 : afact_ok E0 269%nat (mkAF (TA_GOT + 196) (TA_GOT + 196) 2)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U269.
  split; [lia|]. split; [vm_compute; reflexivity | lia]. }
assert (FA454 : afact_ok E0 454%nat (mkAF (TA_g_last_counter + 12) (TA_g_last_counter + 12) 2)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U454.
  split; [lia|]. split; [vm_compute; reflexivity | lia]. }
pose proof (st_ok_pi_add_fact E0 _ _ 269%nat _ HS0 FA269) as HS1.
pose proof (st_ok_pi_add_fact E0 _ _ 454%nat _ HS1 FA454) as HS.
clear HS0 HS1.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
              TG.G_HARNESS HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
              TG.G_HARNESS HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_AT 0x3d8)) mem3
    (YK11.seg_rom segs)) md3) Qx) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite U269 in Ha; apply ie2a_wr_inG; left; lia
            | rewrite U454 in Ha; apply ie2a_wr_inG; right; lia ] |]).
  apply awr_ok_x_nil. }
ie2a_md. rename ms into ms1.
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
  aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ ie2a_wr HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. ics_win Hin Hx ltac:(rewrite ?U269, ?U454 in Hx; first [left; lia | right; lia]). }
assert (GW : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (Ee2 : e2 = bv_swrap 32 (ios_e2_e2v Bx) + 1).
{ unfold ios_e2_e2v. rewrite <- ie2a_got_e2. exact (iak_int_inc _ _ Hinc). }
(* the branch of 0x83158 on bit 0 of s3 *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* s3 & 1 = 0: the frame in flight at 0x83338 *)
  rewrite (ie2a_br_and1 E0 19 fail X19 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_FLY.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (apply awr_ok_x_cons_g;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        first [ lia
              | rewrite U269 in Ha; apply ie2a_wr_inG; left; lia
              | rewrite U454 in Ha; apply ie2a_wr_inG; right; lia ] |]).
    apply awr_ok_x_nil. }
  ie2a_md. rename ms into ms2.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
    aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ ie2a_wr HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    ics_win Hin Hx ltac:(rewrite ?U269, ?U454 in Hx; first [left; lia | right; lia]). }
  assert (GF : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (KWF : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
    aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem3 a)
    by (intros a Ha Hn; rewrite (KF a Ha Hn); exact (KW a Ha Hn)).
  ie2a_stored HS RGe RGl.
  pose proof (iak_region_rd4 E0 _ _ 269%nat _ _ _ _ _ _ e2 _ RGe U269
                ltac:(rewrite Ee2; exact (iak_inc_den E0 36 (ios_e2_e2v Bx) X36 Z5))) as VE.
  pose proof (iak_region_rd4 E0 _ _ 454%nat _ _ _ _ _ _ (bv_swrap 32 (ios_e2_snd frame)) _ RGl U454
                (iak_sext_den E0 33 (ios_e2_snd frame) X33 Z2)) as VL.
  assert (VEb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms2) (TA_GOT + 196 + Z.of_nat j) = Some (YO0f.le_byte e2 4 j))
    by (intros j Hj; rewrite <- (VE j Hj); f_equal; lia).
  assert (VLb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms2) (TA_g_last_counter + 0 + Z.of_nat j) =
    Some (YO0f.le_byte (ios_e2_snd frame) 4 j))
    by (intros j Hj; rewrite <- (ie2a_le_byte_swrap (ios_e2_snd frame) j), <- (VL j Hj); f_equal; lia).
  assert (HTW2 : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms2))
                   (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ios_e2_snd frame))).
  { rewrite ie2a_set_lastc, ie2a_set_e2.
    eapply (ios_tw_end (aview segs (w_H W3) (ms_mem ms2)) (aview segs (w_H W3) mem3)).
    - eapply (ios_tw_step _ _ _ _ TW.OFF_g_last_counter TA_g_last_counter TW.SZ_g_last_counter 0
                TW.OFF_g_last_counter 4%nat (ios_e2_snd frame));
        [| exact TMAP_A_g_last_counter | reflexivity | lia | unfold TW.SZ_g_last_counter; lia | exact VLb].
      eapply (ios_tw_step _ _ _ _ TW.OFF_GOT TA_GOT TW.SZ_GOT 196 TW.A_GOT_e2 4%nat e2);
        [| exact TMAP_A_GOT | reflexivity | lia | unfold TW.SZ_GOT; lia | exact VEb].
      apply ios_tw_start. exact HTW.
    - intros x Hx HP. ios_unP HP. pose proof (TMAP_A_hull x Hx) as Hh.
      unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KWF; [lia | intros [HWx | HWx]; lia]. }
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS (ios_e2_agree regs3 _ _ _ _ _)
                ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms2) mdv0).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 mem3 (ms_mem ms2)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) ie2a_wr
      LAWS HGX HARc HKEPT ltac:(intros a Ha Hn; exact (KWF a Ha Hn))
      ltac:(intros a Ha; exact (GF a (GW a Ha)))
      ltac:(intros a Ha; right; split;
            [exact (ie2a_wr_inG a Ha) | exact (ie2a_wr_iosend (Z.of_nat (length frame)) a Ha)])
      ltac:(lia) ltac:(lia)). }
  destruct (ios_e2_regs_step regs regs3 (ms_regs ms2) p frame fail _ RG R21x R24 KR2)
    as (RGb & _ & R24b).
  assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms2) mdv0 (ms_regs ms2)
                  (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ios_e2_snd frame))).
  { apply (ie2a_keep_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 (ms_mem ms2) mdv0 (ms_regs ms2) Bx _
             LAWS FIX0 H60 HFAT ltac:(intros a Ha Hn; exact (KWF a Ha Hn)) AT0 CUR2 RGb R24b HTW2). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) rg mm mdx) Q) end.
  exact (HFLY (ms_mem ms2) mdv0 (ms_regs ms2) AT2 KR2 Hc).
- (* s3 & 1 <> 0: the epilogue at 0x83384 *)
  rewrite (ie2a_br_and1 E0 19 fail X19 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_EPI.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (apply awr_ok_x_cons_g;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        first [ lia
              | rewrite U269 in Ha; apply ie2a_wr_inG; left; lia
              | rewrite U454 in Ha; apply ie2a_wr_inG; right; lia ] |]).
    apply awr_ok_x_nil. }
  ie2a_md. rename ms into ms2.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
    aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ ie2a_wr HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    ics_win Hin Hx ltac:(rewrite ?U269, ?U454 in Hx; first [left; lia | right; lia]). }
  assert (GF : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (KWF : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
    aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem3 a)
    by (intros a Ha Hn; rewrite (KF a Ha Hn); exact (KW a Ha Hn)).
  ie2a_stored HS RGe RGl.
  pose proof (iak_region_rd4 E0 _ _ 269%nat _ _ _ _ _ _ e2 _ RGe U269
                ltac:(rewrite Ee2; exact (iak_inc_den E0 36 (ios_e2_e2v Bx) X36 Z5))) as VE.
  pose proof (iak_region_rd4 E0 _ _ 454%nat _ _ _ _ _ _ (bv_swrap 32 (ios_e2_snd frame)) _ RGl U454
                (iak_sext_den E0 33 (ios_e2_snd frame) X33 Z2)) as VL.
  assert (VEb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms2) (TA_GOT + 196 + Z.of_nat j) = Some (YO0f.le_byte e2 4 j))
    by (intros j Hj; rewrite <- (VE j Hj); f_equal; lia).
  assert (VLb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms2) (TA_g_last_counter + 0 + Z.of_nat j) =
    Some (YO0f.le_byte (ios_e2_snd frame) 4 j))
    by (intros j Hj; rewrite <- (ie2a_le_byte_swrap (ios_e2_snd frame) j), <- (VL j Hj); f_equal; lia).
  assert (HTW2 : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms2))
                   (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ios_e2_snd frame))).
  { rewrite ie2a_set_lastc, ie2a_set_e2.
    eapply (ios_tw_end (aview segs (w_H W3) (ms_mem ms2)) (aview segs (w_H W3) mem3)).
    - eapply (ios_tw_step _ _ _ _ TW.OFF_g_last_counter TA_g_last_counter TW.SZ_g_last_counter 0
                TW.OFF_g_last_counter 4%nat (ios_e2_snd frame));
        [| exact TMAP_A_g_last_counter | reflexivity | lia | unfold TW.SZ_g_last_counter; lia | exact VLb].
      eapply (ios_tw_step _ _ _ _ TW.OFF_GOT TA_GOT TW.SZ_GOT 196 TW.A_GOT_e2 4%nat e2);
        [| exact TMAP_A_GOT | reflexivity | lia | unfold TW.SZ_GOT; lia | exact VEb].
      apply ios_tw_start. exact HTW.
    - intros x Hx HP. ios_unP HP. pose proof (TMAP_A_hull x Hx) as Hh.
      unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KWF; [lia | intros [HWx | HWx]; lia]. }
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS (ios_e2_agree regs3 _ _ _ _ _)
                ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms2) mdv0).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 mem3 (ms_mem ms2)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) ie2a_wr
      LAWS HGX HARc HKEPT ltac:(intros a Ha Hn; exact (KWF a Ha Hn))
      ltac:(intros a Ha; exact (GF a (GW a Ha)))
      ltac:(intros a Ha; right; split;
            [exact (ie2a_wr_inG a Ha) | exact (ie2a_wr_iosend (Z.of_nat (length frame)) a Ha)])
      ltac:(lia) ltac:(lia)). }
  destruct (ios_e2_regs_step regs regs3 (ms_regs ms2) p frame fail _ RG R21x R24 KR2)
    as (RGb & _ & R24b).
  assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms2) mdv0 (ms_regs ms2)
                  (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ios_e2_snd frame))).
  { apply (ie2a_keep_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 (ms_mem ms2) mdv0 (ms_regs ms2) Bx _
             LAWS FIX0 H60 HFAT ltac:(intros a Ha Hn; exact (KWF a Ha Hn)) AT0 CUR2 RGb R24b HTW2). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_EPI) rg mm mdx) Q) end.
  exact (HEPI (ms_mem ms2) mdv0 (ms_regs ms2) AT2 KR2 Hc).
Qed.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

(* The E2 arm, 0x8312c .. 0x8315c: from the dispatch's E2 exit (io_send_seg_e2.v ios_e2_at at the world
   io_send_segs.v ios_B0 Bw, with s5 = f.cmd = 0xe2 and f.retry = 0) to the frame in flight (IOS_FLY) when bit 0
   of the entry g_fail_next is clear, and to the epilogue (IOS_EPI) when it is set. Both continuations are
   io_send_seg_e2.v ios_e2_seg_stmt's. *)
Lemma ios_e2_arm : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame cmd
    Bw Bw' ly3 S3 (W2 : world segs) mem4 md4 regs4 (Q : world segs -> config -> Prop),
  ios_e2_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
    ly3 S3 W2 mem4 md4 regs4 (ios_B0 Bw) ->
  YK11.getr regs4 21 = w64 cmd -> cmd = DSpec.sf_cmd (TC.rf frame) -> cmd = TC.SPEC_CMD_E2 ->
  ios_e2_rty frame = 0 ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  ios_arm Bw frame = Some (Bw', tt) ->
  (forall ly5 S5 mem5 md5 regs5 B5,
     cmd = TC.SPEC_CMD_E2 -> TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
     TC.truth (TW.g_fail_next Bw) = false -> Bw' = ios_fly frame B5 ->
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
       ly5 S5 W2 mem5 md5 regs5 B5 ->
     YK11.getr regs5 21 = w64 cmd ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) regs5 mem5 md5) Q) ->
  (forall ly5 S5 (W5 : world segs) mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
       ly5 S5 W5 mem5 md5 regs5 Bw' ->
     SRr segs W5 (@cfg_at fx segs (transport_text + IOS_EPI) regs5 mem5 md5) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_AT 0x3cc) regs4 mem4 md4) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame cmd Bw Bw'
  ly3 S3 W2 mem4 md4 regs4 Q HLAWS HFIX AT R21 Ecmd EE2 Erty HCSF HARM HFLY HEPI.
destruct HLAWS as (HCELLS & LAWS & MTL & HGX & HGE & LCIR & LCSW & LCLC).
destruct (iak_geo B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFIX)
  as (HARc & Hce & Hlo & Hhi & H47 & Hsp0al & Hal).
pose proof (ios_len60 _ _ _ HCSF) as H60.
pose proof HFIX as HFIX0.
destruct HFIX as (HJc & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hslo & Hshi & Hp0 & HG8c & HSRCc & HOFFc
  & HFATc & Hfailb & HROM & Htwc & Hfly & Hcmd & Hev).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8496) by reflexivity.
(* the model: the two leaf calls, the counter and the world each arm leaves *)
assert (Efc : DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2) by (rewrite <- Ecmd; exact EE2).
assert (Hretry : TC.truth (DSpec.sf_retry (TC.rf frame)) = false).
{ unfold TC.truth. unfold ios_e2_rty in Erty. rewrite Erty. reflexivity. }
destruct (ios_arm_e2 Bw frame Bw' HARM Efc Hretry) as (HMW & HMC & e2 & Hinc & Hcase).
cbv zeta in Hcase.
(* the fixed facts this stretch reads *)
assert (FIX : ios_e2_fix B STK sp0 regs p frame).
{ unfold ios_e2_fix.
  split; [exact Hp0|]. split; [lia|]. split; [exact HOFFc|]. split; [exact Hsp16|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp | exact Htp]. }
assert (Hfail0 : 0 <= TW.g_fail_next Bw <= 1).
{ pose proof (TWL.u_at_range Bw TW.OFF_g_fail_next 1) as Hr.
  change (TW.u_at Bw TW.OFF_g_fail_next 1) with (TW.g_fail_next Bw) in Hr. lia. }
(* 0x8312c .. 0x83134: the two leaf calls *)
apply (ie2a_calls STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame
         (TW.g_fail_next Bw) cmd ly3 S3 W2 mem4 md4 regs4 (ios_B0 Bw) Q
         HCELLS LAWS HGX LCSW LCLC HARc FIX H60 AT R21 HMW HMC).
intros mem5 md5 regs5 AT5 R215.
(* 0x83138 .. 0x8315c: the two stores and the branch *)
apply (ie2a_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame
         (TW.g_fail_next Bw) e2 ly3 S3 W2 mem5 md5 regs5 (ios_B0 Bw) Q
         LAWS HGX HARc FIX H60 HFATc Hfail0 Hinc AT5).
- (* bit 0 clear: the frame in flight, at the world ios_arm_e2's second case gives *)
  intros mem6 md6 regs6 AT6 KR6 Hz.
  assert (Htruth : TC.truth (TW.g_fail_next Bw) = false)
    by (unfold TC.truth; rewrite Hz; reflexivity).
  destruct Hcase as [(Ht & _) | (_ & EBw')]; [rewrite Htruth in Ht; discriminate Ht|].
  apply (HFLY ly3 S3 mem6 md6 regs6
           (TW.set_g_last_counter (TW.set_GOT_e2 (ios_B0 Bw) e2) (DSpec.sf_send (TC.rf frame)))
           EE2 Hretry Htruth EBw' AT6).
  rewrite (KR6 21%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)). exact R215.
- (* bit 0 set: the epilogue, at the world ios_arm_e2's first case gives *)
  intros mem6 md6 regs6 AT6 KR6 Hz.
  assert (Htruth : TC.truth (TW.g_fail_next Bw) = true)
    by (unfold TC.truth; apply negb_true_iff, Z.eqb_neq; exact Hz).
  destruct Hcase as [(_ & EBw') | (Hf & _)]; [|rewrite Htruth in Hf; discriminate Hf].
  rewrite <- EBw' in AT6.
  exact (HEPI ly3 S3 W2 mem6 md6 regs6 AT6).
Qed.

End e2a.
