(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 844 of its 917 lines of code are new or changed and 1066 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4sub: the segment lc_op4sub_stmt (OP4SUB) of the image-A walk of
   libdiginet/fuzz_transport's LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), +0x1164 .. +0x1198:
   the tagged arm of op 4 with want decided, its three calls, up to the cut CMDW at +0x119c.

   lc_op4sub_ok : lc_op4sub_stmt. The code (an offset +X is the address 0x81264 + X):
     +0x1164 auipc a0 / +0x1168 addi a0: a0 = &g_s; +0x116c mv a1, s7 (c = F + 32);
     +0x1170 jal diginet_session_submit (return +0x1174): a G-form callee composed in the walk's own G journal
            (its statement diginet_session_submit_cg.v transport_diginet_session_submit_cg is the record field
            lp_submit); c lies in the class-2 side-stack frame (decode_in_fake), its shadow bytes 4 .. 7 are 0 while
            op 4 runs (lf_shm true _), so trans_src_ok holds of [c, c + 32);
     +0x1174 .. +0x1180: a1 = c, s7 = rc, a0 = c, a1 = rc; +0x1184 ld a2, 144(s1) (the queue length before, as the
            `lw` at +0x4a8 left it); +0x1188 jal check_refusal_submit (return +0x118c): a leaf, through
            DgnTransportCg.v transport_leaf_at (record field lp_crs), DgnTransportLeafb.v decode_leafb_journal and
            TransportGCg.v gx_call_leaf;
     +0x118c bnez s4, +0x119c: s4 is the sys flag (lc_sys); when it is 1 the jump goes to the cut;
     +0x1190 mv a0, s7 (rc), +0x1194 mv a1, s6 (want), +0x1198 jal check_latest_submit (return +0x119c): a leaf
            (lp_cls), as above.
   The model: the operation's Some (LoopOk.op_ok at lc_opok's facts), read through LLVMFuzzerTestOneInput_st.v
   lc_op4_eq and lc_submit_tag_eq, gives the three Some answers the cut CMDW names (o4s_model).
   Every run between the calls writes no memory (no region is written); the calls keep what lc_core_kept asks (the
   bytes from alloc_ceiling up outside the callee's window below sp1, the blocks, the frame and its shadow). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YE00 YE01 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase PaTable PaSym PaStep PaRun
  PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit DgnTransportLeafb DgnTransportCgRun LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  LeafCgKit AsanKA check_refusal_submit_cg check_latest_submit_cg check_refusal_submit_c check_latest_submit_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TImg TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module LCRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_refusal_submit_cg.
Module LCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_submit_cg.
Module LCRSc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_refusal_submit_c.
Module LCLSc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_submit_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                         *)
(* ------------------------------------------------------------------ *)

Lemma o4s_pair_inv : forall (X Y : Type) (a a' : X) (b b' : Y), Some (a, b) = Some (a', b') -> a' = a /\ b' = b.
Proof. intros X Y a a' b b' H. inversion H. split; reflexivity. Qed.

(* diginet_session_submit_m answers 0, -1, -5 or -10 (lib/Prog/T/LLVMFuzzerTestOneInput_op4t3.v o4t3_submit_rc). *)
Ltac o4s_dest_if H := lazymatch type of H with (if ?b then _ else _) = _ => destruct b end.
Ltac o4s_rc_small := lazymatch goal with |- -10 <= ?x <= 0 =>
  let v := eval vm_compute in x in change x with v; lia end.
Lemma o4s_submit_rc : forall B c B' r, TS0.diginet_session_submit_m B c = Some (B', r) -> -10 <= r <= 0.
Proof.
  intros B c B' r H. unfold TS0.diginet_session_submit_m in H. cbv zeta in H.
  o4s_dest_if H.
  { apply o4s_pair_inv in H. destruct H as [_ ->]. o4s_rc_small. }
  o4s_dest_if H.
  { apply o4s_pair_inv in H. destruct H as [_ ->]. o4s_rc_small. }
  destruct (if TS0.coalescable_m (TS0.cmd_key_of c) =? 0 then Some None
            else TS0.submit_find_m B (TS0.cmd_key_of c) 0 (Z.to_nat (TW.S_queued B)))
    as [[i|]|]; [| |discriminate H].
  - apply o4s_pair_inv in H. destruct H as [_ ->]. o4s_rc_small.
  - destruct (TW.S_queued B =? TS0.DIGINET_QUEUE_MAX).
    { apply o4s_pair_inv in H. destruct H as [_ ->]. o4s_rc_small. }
    destruct (TW.S_queue_N <=? TW.S_queued B); [discriminate H|].
    apply o4s_pair_inv in H. destruct H as [_ ->]. o4s_rc_small.
Qed.

(* The operation's Some, through op_submit's tagged mode: the three calls of this segment answer Some. *)
Lemma o4s_model : forall (D B0 B1 : list byte) (c0 : TOP.fuzz_in) (k : nat) (A : nat -> Z) Bf cf kf at_,
  TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 A D c0 k = Some (Bf, (cf, kf)) ->
  lc_opc D c0 = 4 -> TC.op_begin_m B0 = Some (B1, tt) -> TW.g_raw B1 = 0 ->
  lc_at (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))) (sv_key (lc_sub_kd D (lc_oc D c0))) = Some at_ ->
  exists B3 r B4 B5,
    TS0.diginet_session_submit_m (tg_B2 (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))))
      (TOP.cmd_struct (tg_cbytes (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))))
         (tg_len (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))))
         (sv_display (lc_sub_kd D (lc_oc D c0))) (sv_key (lc_sub_kd D (lc_oc D c0)))) = Some (B3, r) /\
    TC.check_refusal_submit_m B3
      (TOP.cmd_struct (tg_cbytes (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))))
         (tg_len (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))))
         (sv_display (lc_sub_kd D (lc_oc D c0))) (sv_key (lc_sub_kd D (lc_oc D c0))))
      r (TW.S_queued B0) = Some (B4, tt) /\
    (if lc_sys (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))) then B5 = B4
     else TC.check_latest_submit_m B4 r
            (lc_want (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0)))) at_) = Some (B5, tt)).
Proof.
  intros D B0 B1 c0 k A Bf cf kf at_ H Ho HOB HR Hat.
  rewrite (lc_op4_eq timg_A B0 A D c0 k Ho) in H.
  rewrite (lc_submit_tag_eq B0 B1 D (lc_oc D c0) HOB HR) in H.
  cbv zeta in H.
  set (kd := lc_sub_kd D (lc_oc D c0)) in *.
  set (tv := lc_tag_vals D B1 (sv_c kd)) in *.
  set (cs := TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd)) in *.
  destruct (TC.CMDS_MAX <=? tg_serial tv); cbv beta iota in H; [discriminate H|].
  rewrite Hat in H. cbv beta iota zeta in H.
  destruct (TS0.diginet_session_submit_m (tg_B2 tv) cs) as [[B3 r]|] eqn:E3; cbv beta iota in H; [|discriminate H].
  destruct (TC.check_refusal_submit_m B3 cs r (TW.S_queued B0)) as [[B4 u4]|] eqn:E4; cbv beta iota in H;
    [|discriminate H].
  destruct u4.
  destruct (lc_sys tv) eqn:Es; cbv beta iota in H.
  - exists B3, r, B4, B4. split; [reflexivity|]. split; [exact E4 | reflexivity].
  - destruct (TC.check_latest_submit_m B4 r (lc_want tv at_)) as [[B5 u5]|] eqn:E5; cbv beta iota in H;
      [|discriminate H].
    destruct u5. exists B3, r, B4, B5. split; [reflexivity|]. split; [exact E4 | first [reflexivity | exact E5]].
Qed.

(* want is one of SPEC_OK, SPEC_E_SPACE, SPEC_E_REFUSED: a small signed value. *)
Lemma o4s_want_small : forall tv at_, -2 ^ 31 <= lc_want tv at_ < 2 ^ 31.
Proof.
  intros tv at_. unfold lc_want.
  destruct (lc_sys tv); [|destruct ((at_ <? 0) && (TW.g_nq (tg_B2 tv) =? TC.QUEUE_MAX))];
    lazymatch goal with |- _ <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Qed.

(* c's 32 bytes: 24 command bytes (the tag, two serial bytes, the n bytes taken from D, 21 - n zeros), len, display,
   two zeros, the key (TOps.v cmd_struct); the take hands out n <= len - 3 <= 21 bytes inside D (QueueFacts.v
   fuzz_take_ok), from the cursor of op 4 (fuzz_in_ok through the five u8 reads). *)
Lemma o4s_cs_len : forall D c B1, QF.fuzz_in_ok D c ->
  length (TOP.cmd_struct (tg_cbytes (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c)))))
    (tg_len (lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c)))))
    (sv_display (lc_sub_kd D (lc_oc D c))) (sv_key (lc_sub_kd D (lc_oc D c)))) = 32%nat.
Proof.
  intros D c B1 Hc. unfold lc_oc.
  destruct (QF.fuzz_u8_ok D c Hc) as (c1 & v1 & E1 & H1 & _). rewrite E1. cbn [fst].
  unfold lc_sub_kd.
  destruct (QF.fuzz_u8_ok D c1 H1) as (c2 & v2 & E2 & H2 & _). rewrite E2. cbv beta iota zeta.
  destruct (QF.fuzz_u8_ok D c2 H2) as (c3 & v3 & E3 & H3 & _). rewrite E3. cbv beta iota zeta.
  destruct (QF.fuzz_u8_ok D c3 H3) as (c4 & v4 & E4 & H4 & _). rewrite E4. cbv beta iota zeta.
  cbn [sv_c sv_key sv_display].
  unfold lc_tag_vals.
  destruct (QF.fuzz_u8_ok D c4 H4) as (c5 & v5 & E5 & H5 & Hv5). rewrite E5. cbv beta iota zeta.
  assert (Hw : 0 <= v5 mod 22 + 3 - 3) by (pose proof (Z.mod_pos_bound v5 22 ltac:(lia)); lia).
  destruct (QF.fuzz_take_ok D c5 (v5 mod 22 + 3 - 3) H5 Hw) as (c6 & off & n & E6 & _ & Hn & Hoff & Hon & _).
  rewrite E6. cbv beta iota zeta. cbn [tg_cbytes tg_len].
  pose proof (Z.mod_pos_bound v5 22 ltac:(lia)) as Hm.
  unfold TOP.cmd_struct. rewrite !length_app, TWL.length_put. cbn [length]. rewrite repeat_length.
  unfold TW.sub. rewrite length_firstn, length_skipn. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The section                                                       *)
(* ------------------------------------------------------------------ *)

Section op4sub. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma o4s_base : BASE = transport_text.
Proof. vm_compute. reflexivity. Qed.

Definition o4s_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).

Lemma o4s_ew_reg : forall regs extra n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (o4s_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn Hr. unfold o4s_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.

Lemma o4s_env_img : forall regs extra, img_env VAL A_LIM (o4s_E regs extra).
Proof. intros regs extra. unfold o4s_E. apply Eimg_env. Qed.

(* A symbolic state with no region and pinned registers holds of any machine state at its pc. *)
Lemma o4s_entry0 : forall (fx : YK11.FPState) (W : world segs) regs extra mem (pc : Z),
  st_ok_pi segs VAL (o4s_E regs extra) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros fx W regs extra mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The value of register r of the machine state of a symbolic state HS (close_send's cs_reg). *)
Ltac o4s_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* An atom register SOff n 0 of the entry registers regs0. *)
Ltac o4s_atom regs0 Q :=
  cbn [sv_denot]; erewrite o4s_ew_reg; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Q | lia | reflexivity].
Ltac o4s_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons; [intros ? ?; cbn [YP09.r_wlo YP09.r_whi] in *; lia|]);
  apply awr_ok_x_nil.
(* A run from a state whose regions it does not write writes no byte. *)
Ltac o4s_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; lia|]); destruct Hin
  | ].

(* ------------------------------------------------------------------ *)
(* 3. c = F + 32 in the class-2 frame, its shadow 0 while op 4 runs     *)
(* ------------------------------------------------------------------ *)

Lemma o4s_div64 : forall q t, (64 * q + t) / 8 = 8 * q + t / 8.
Proof. intros q t. replace (64 * q + t) with (t + (8 * q) * 8) by ring. rewrite Z.div_add by lia. ring. Qed.

Lemma o4s_sh_div : forall q t, 0 <= t < 64 -> (SHADOW_OFF + (64 * q + t) / 8) / 8 * 8 = SHADOW_OFF + 8 * q.
Proof.
  intros q t Ht. rewrite o4s_div64. unfold SHADOW_OFF.
  replace (2147450880 + (8 * q + t / 8)) with (t / 8 + (268431360 + q) * 8) by ring.
  rewrite Z.div_add by lia.
  rewrite (Z.div_small (t / 8) 8) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  ring.
Qed.

Lemma o4s_c_ok : forall cx ly S (W : world segs) mem md (bin : bool) (cs : list byte),
  AR_laws segs B -> AR segs B ly S W mem md -> In (LF_CID, l_fpos cx) (frames S) ->
  frame_addr ly LF_CID (l_fpos cx) = lc_F cx -> lc_F cx mod 64 = 0 ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W) mem a) ->
  lc_fsh cx (aview segs (w_H W) mem) true bin ->
  decode_in_fake ly S (lc_F cx + 32) 32 /\ decode_rd_ok W mem (lc_F cx + 32) 32.
Proof.
  intros cx ly S W mem md bin cs LAWS HAR Hin HFa HFal HFp HFS.
  destruct (frames_bounds segs B LAWS ly S W mem md LF_CID (l_fpos cx) HAR Hin) as (Hb1 & Hb2 & Happ).
  rewrite HFa in Hb1, Hb2, Happ. change (fs_frame_bytes LF_CID) with 256 in Hb2, Happ.
  pose proof (@ASAN_CEIL_range rc) as (CE1 & CE2).
  unfold ASAN_CEIL in CE1. unfold ASAN_CEIL in CE2.
  set (F := lc_F cx) in *.
  apply Z.mod_divide in HFal as [q Hq]; [|lia].
  assert (EF : F = 64 * q) by lia.
  assert (ESH : lc_SH cx = SHADOW_OFF + 8 * q).
  { unfold lc_SH. fold F. rewrite EF. replace (64 * q) with ((8 * q) * 8) by ring. rewrite Z.div_mul by lia. ring. }
  split.
  { exists LF_CID, (l_fpos cx). split; [exact Hin|]. rewrite HFa. change (fs_frame_bytes LF_CID) with 256. lia. }
  split; [|split; [|split; [|split]]].
  - intros a Ha. apply (aview_some_of_apresent segs). apply HFp. unfold LF_FBYTES. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr.
    replace x with (64 * q + (x - 64 * q)) by ring. rewrite o4s_div64.
    assert (Hi : 4 <= (x - 64 * q) / 8 < 8)
      by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
    replace (SHADOW_OFF + (8 * q + (x - 64 * q) / 8)) with (lc_SH cx + (x - 64 * q) / 8) by (rewrite ESH; ring).
    rewrite (HFS ((x - 64 * q) / 8) ltac:(lia)).
    assert (Ei : (x - 64 * q) / 8 = 4 \/ (x - 64 * q) / 8 = 5 \/ (x - 64 * q) / 8 = 6 \/ (x - 64 * q) / 8 = 7) by lia.
    destruct Ei as [-> | [-> | [-> | ->]]]; reflexivity.
  - intros s Hs. unfold shadow_addr in Hs.
    replace (F + 32) with (64 * q + 32) in Hs by lia.
    replace (F + 32 + 32 - 1) with (64 * q + 63) in Hs by lia.
    rewrite !o4s_sh_div in Hs by lia.
    replace s with (lc_SH cx + (s - lc_SH cx)) by ring.
    rewrite (HFS (s - lc_SH cx) ltac:(lia)). discriminate.
  - unfold amem_range. unfold in_app in Happ.
    destruct Happ as [Ha1 [Ha2 | [Ha2 Ha3]]];
      [left | right]; unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
      [lia | split; lia].
  - lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. What holds at every point of the segment                          *)
(* ------------------------------------------------------------------ *)

(* The loop's common facts (c in scope), c's 32 bytes, the op-4 spill slots sl of the machine frame, and the values rv
   of callee-saved registers the cut CMDW names (none of them s7, which this segment writes). *)
Definition o4s_inv (cx : lcx) (op : lop) (cs : list byte) (sl : list (Z * Z)) (rv : list (Z * word))
    (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (e : Z) : Prop :=
  lc_lcore B MT cx op true false (lo_k op) ly S W regs mem md e /\
  garr8 segs (mrestrict (w_H W) mem) (lc_F cx + 32) (TW.zs cs) /\
  lc_spills cx sl (aview segs (w_H W) mem) /\
  Forall (fun x : Z * word => YK11.getr regs (Z_to_bv 5 (fst x)) = snd x) rv.

(* lc_core reads only sp, s0, s1, gp and tp of the registers. *)
Lemma o4s_core_regs : forall cx ly S (W : world segs) regsA regsB mem md e,
  lc_core B cx ly S W regsA mem md e ->
  (forall r, acallee_saved r -> r <> 23 -> YK11.getr regsB (Z_to_bv 5 r) = YK11.getr regsA (Z_to_bv 5 r)) ->
  lc_core B cx ly S W regsB mem md e.
Proof.
  intros cx ly S W regsA regsB mem md e HC HR.
  destruct HC as (HJ & Hfr & HlyF & HP & R2 & R8 & R9 & R3 & R4 & Hrest).
  refine (conj HJ (conj Hfr (conj HlyF (conj HP (conj _ (conj _ (conj _ (conj _ (conj _ Hrest))))))))).
  - exact (eq_trans (HR 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) R2).
  - exact (eq_trans (HR 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) R8).
  - exact (eq_trans (HR 9 ltac:(unfold acallee_saved; lia) ltac:(lia)) R9).
  - exact (eq_trans (HR 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) R3).
  - exact (eq_trans (HR 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) R4).
Qed.

(* The invariant carried over a step or a call (LLVMFuzzerTestOneInput_st.v lc_core_kept, with the callee-saved
   registers but s7 kept, no meter charge and no event). *)
Lemma o4s_inv_kept : forall cx op cs sl rv ly' S' (W' : world segs) regs' mem' md' e (X : Z)
    ly2 S2 (W2 : world segs) regs2 mem2 md2,
  AR_laws segs B -> ameter_laws MT -> @lc_base rc B MT XL RLO RHI cx ->
  o4s_inv cx op cs sl rv ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e ->
  frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  (forall r, acallee_saved r -> r <> 23 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  mo_le MT S' S2 0 ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W') mem' (b + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  length cs = 32%nat ->
  (forall o, In o sl -> 0 <= fst o /\ fst o + 8 <= 192) ->
  (forall x, In x rv -> acallee_saved (fst x) /\ fst x <> 23) ->
  o4s_inv cx op cs sl rv ly2 S2 W2 regs2 mem2 md2 e.
Proof.
  intros cx op cs sl rv ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 LAWS MTL HB HI HJ2 HFR2 HP2 HR HMO HX
    KA KB KF HLC Hsl Hrv.
  destruct HI as (HLC0 & HGA & HSL & HRV).
  destruct HLC0 as (HC & HFR & HSP & HFSH & HOPOK & He & HMET & R21).
  pose proof (o4s_core_regs cx ly' S' W' regs' regs2 mem' md' e HC HR) as HC'.
  assert (HPR : aregs_preserved regs2 regs2) by (intros r _; reflexivity).
  pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs2 mem' md' e X ly2 S2 W2 regs2 mem2 md2 e LAWS HB HC' HJ2
    HFR2 HP2 HPR HX KA KB KF) as HC2.
  destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as [_ _ Hstk Hsp1c _ _ _ _ _].
  pose proof (@YM05.alloc_ceiling_val rc) as [CE1 CE2].
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & _ & HFceil & _).
  destruct Hstk as (_ & _ & Hs3 & Hs4). unfold LF_FRAME in Hsp1.
  assert (KS : forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 ->
    aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
  { intros a Ha. apply KA; [split; [lia | change (2 ^ 64) with 18446744073709551616; lia] | lia]. }
  split; [|split; [|split]].
  - refine (conj HC2 (conj _ (conj _ (conj _ (conj HOPOK (conj He (conj _ _))))))).
    + destruct HFR as (F18 & F26). split.
      * exact (eq_trans (HR 18 ltac:(unfold acallee_saved; lia) ltac:(lia)) F18).
      * exact (eq_trans (HR 26 ltac:(unfold acallee_saved; lia) ltac:(lia)) F26).
    + apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W') mem') (aview segs (w_H W2) mem2));
        [|exact KS|exact HSP].
      intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as HV.
      rewrite Forall_forall in HV. pose proof (HV o Ho) as (_ & _ & Ho8 & Ho192). lia.
    + apply (lc_fsh_kept cx (aview segs (w_H W') mem') (aview segs (w_H W2) mem2)); [|exact HFSH].
      intros a Ha. apply KF. right. exact Ha.
    + destruct HMET as (HM1 & HM2). split.
      * replace (Z.of_nat (lo_k op) * lf_rcost MT) with (Z.of_nat (lo_k op) * lf_rcost MT + 0) by ring.
        exact (mo_le_trans MT MTL _ _ _ _ _ HM1 HMO).
      * apply (mo_ok_step MT MTL S' S2 0 _); [rewrite Z.add_0_l; exact HM2 | exact HMO].
    + exact (eq_trans (HR 21 ltac:(unfold acallee_saved; lia) ltac:(lia)) R21).
  - apply (lc_garr8_kept (w_H W') (w_H W2) mem' mem2 (lc_F cx + 32) (TW.zs cs)); [|exact HGA].
    intros j Hj. unfold TW.zs in Hj. rewrite length_map, HLC in Hj. apply KF. left. unfold LF_FBYTES. lia.
  - apply (lc_spills_kept cx sl (aview segs (w_H W') mem') (aview segs (w_H W2) mem2)); [exact Hsl | exact KS | exact HSL].
  - rewrite Forall_forall in HRV |- *. intros x Hx. rewrite <- (HRV x Hx).
    destruct (Hrv x Hx) as (Hcs & Hn23). exact (HR (fst x) Hcs Hn23).
Qed.

(* The slot 144(s1) the `ld a2, 144(s1)` at +0x1184 reads, as atom 32 (s1 is atom 9). *)
Definition o4s_rg144 : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))].

(* The op-4 slots of the machine frame the cut CMDW names, and the callee-saved registers it names (with s4). *)
Definition o4s_sl (op : lop) (tv : ltg) : list (Z * Z) :=
  [(56, TOP.fi_n (tg_c4 tv)); (64, TA_g_cmd); (72, tg_serial tv);
   (144, bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.S_queued (lo_B op)))))].
Definition o4s_rv (cx : lcx) (tv : ltg) (at_ : Z) : list (Z * word) :=
  [(22, w64 (lc_want tv at_)); (19, w64 (at_ mod 2 ^ 32)); (24, w64 (l_p cx + TOP.fi_off (tg_c4 tv)));
   (25, w64 (tg_n tv)); (27, w64 (TA_g_cmd + 40 * tg_serial tv)); (20, w64 (if lc_sys tv then 1 else 0))].
Lemma o4s_sl_ok : forall op tv o, In o (o4s_sl op tv) -> 0 <= fst o /\ fst o + 8 <= 192.
Proof.
  intros op tv o Ho. unfold o4s_sl in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho.
Qed.
Lemma o4s_rv_ok : forall cx tv at_ x, In x (o4s_rv cx tv at_) -> acallee_saved (fst x) /\ fst x <> 23.
Proof.
  intros cx tv at_ x Hx. unfold o4s_rv in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [cbn [fst]; unfold acallee_saved; lia|]). destruct Hx.
Qed.

(* The cut CMDW from the invariant and the model's three answers. *)
Lemma o4s_cmdw : forall cx op B1 at_ B3 r B4 B5 ly S (W : world segs) regs mem md e,
  lc_opc (l_pl cx) (lo_c op) = 4 ->
  TC.op_begin_m (lo_B op) = Some (B1, tt) -> TW.g_raw B1 = 0 ->
  0 <= tg_serial (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) < TC.CMDS_MAX ->
  lc_at (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))))
    (sv_key (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))) = Some at_ ->
  let kd := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) in
  let tv := lc_tag_vals (l_pl cx) B1 (sv_c kd) in
  let cs := TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd) in
  TS0.diginet_session_submit_m (tg_B2 tv) cs = Some (B3, r) ->
  TC.check_refusal_submit_m B3 cs r (TW.S_queued (lo_B op)) = Some (B4, tt) ->
  (if lc_sys tv then B5 = B4 else TC.check_latest_submit_m B4 r (lc_want tv at_) = Some (B5, tt)) ->
  o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly S W regs mem md e ->
  lc_tw W mem B5 ->
  lc_st_cmdw B MT cx op W (lc_cfg cx LO_CMDW regs mem md).
Proof.
  intros cx op B1 at_ B3 r B4 B5 ly S W regs mem md e Hopc HOB Hraw Hser Hat kd tv cs M3 M4 M5 HI HTW.
  destruct HI as (HLC & HGA & HSL & HRV).
  unfold lc_spills, o4s_sl in HSL. unfold o4s_rv in HRV.
  inversion HSL as [|o1 l1 S56 HSL1]; subst. inversion HSL1 as [|o2 l2 S64 HSL2]; subst.
  inversion HSL2 as [|o3 l3 S72 _]; subst.
  inversion HRV as [|x1 k1 V22 HRV1]; subst. inversion HRV1 as [|x2 k2 V19 HRV2]; subst.
  inversion HRV2 as [|x3 k3 V24 HRV3]; subst. inversion HRV3 as [|x4 k4 V25 HRV4]; subst.
  inversion HRV4 as [|x5 k5 V27 _]; subst.
  cbn [fst snd] in S56, S64, S72, V22, V19, V24, V25, V27.
  unfold lc_st_cmdw. exists ly, S, regs, mem, md, e, B1, at_, B3, r, B4, B5. cbv zeta.
  fold kd tv cs.
  refine (conj eq_refl (conj Hopc (conj HLC (conj HOB (conj Hraw (conj Hser (conj Hat (conj M3 (conj M4 (conj M5
    (conj HTW (conj HGA (conj S56 (conj S64 (conj S72 (conj V22 (conj V19 (conj V24 (conj V25 V27))))))))))))))))))).
Qed.

(* A leaf called from the walk's G journal, through the unit's leaf bridge (DgnTransportLeafb.v
   decode_leafb_journal) and TransportGCg.v gx_call_leaf: the world and the journal kept, the callee-saved registers
   kept, every byte outside the leaf's stack window kept, presence kept, and the leaf's X. *)
Lemma o4s_leaf : forall (fx : YK11.FPState) (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md
    own lyc Sc mdc k (o PC : Z) (X : (word -> option byte) -> Prop),
  AR_laws segs B ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  (@decode_leafb_ecall_pre rc B lyc Sc W regsT memT mdc ->
     SRr segs W (@LCK.cfg_at fx PC regsT memT mdc) (@decode_leafb_post fx rc B lyc Sc W regsT memT mdc None [] X)) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 PC) memT (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
      c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
      @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2
        md2 k /\
      aregs_preserved regsT regs2 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
         aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
      (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\ X mem2).
Proof.
  intros fx W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o PC X LAWS HJ Hsp Hal Hneg Hbud Hra Hgp Htp HLEAF.
  apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k _
    (YK11.getr regsT 1)
    (fun regs2 mem2 md2 => aregs_preserved regsT regs2 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
         aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
      (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\ X mem2) HJ).
  intros memS HJi.
  eapply SRr_mono.
  { apply (@decode_leafb_journal fx rc tfib_sink_head B LAWS W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc k
      o PC None [] X HJi Hsp Hal Hneg Hbud Hra Hgp Htp).
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - exact HLEAF. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Ec & HJ2 & HP & _ & Heff & Hgr & HX).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
  split; [exact HP|].
  split; [intros a Ha Hn; exact (Heff a Ha Hn ltac:(intros Hw; unfold LCK.in_wr in Hw; inversion Hw))|].
  split; [exact Hgr | exact HX].
Qed.

(* The registers a symbolic state keeps from the entry registers regs0 (an atom SOff r 0 for register r). *)
Ltac o4s_kreg HS regs0 :=
  lazymatch goal with |- YK11.getr (ms_regs ?msx) ?rr = YK11.getr regs0 ?rr =>
  lazymatch type of HS with
  | st_ok ?sg ?Ex ?ssx (restrict ?Hh msx) =>
      refine (eq_trans (st_ok_restrict_reg sg Hh Ex ssx msx rr HS) _);
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in change (sv_denot Ex e = YK11.getr regs0 rr);
      cbn [sv_denot]; erewrite o4s_ew_reg; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | reflexivity]
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx rr HS) _);
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in change (sv_denot Ex e = YK11.getr regs0 rr);
      cbn [sv_denot]; erewrite o4s_ew_reg; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | reflexivity]
  end end.
Ltac o4s_keep HS regs0 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hn := fresh "Hn" in
  intros r Hr Hn; unfold acallee_saved in Hr;
  assert (Er : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Er as [-> | Er]; [o4s_kreg HS regs0|]); subst r; o4s_kreg HS regs0.

(* What diginet_session_submit may store lies in g_s, image bytes (diginet_session_submit_segs.v ssw_wr_gs). *)
Lemma o4s_wr_gs : forall a, ssubmit_wr a -> TA_g_s <= a < TA_g_s + TW.SZ_g_s.
Proof.
  intros a [H | [H | [H | (j & Hj & H)]]]; unfold twa_fld in H;
    unfold TW.A_S_queued, TW.A_S_stats_coalesced, TW.A_S_stats_refused, TW.A_S_queue_bytes, TW.S_queue_ESZ,
      TW.S_queue_N, TW.OFF_g_s, TW.SZ_g_s, TA_g_s in *; lia.
Qed.
Lemma o4s_wr_img : forall a, ssubmit_wr a -> in_img segs a.
Proof.
  intros a H. apply trans_g_img. pose proof (o4s_wr_gs a H) as Ha.
  unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [cbn; tauto | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.
(* Every byte is read modulo 2 ^ 64. *)
Lemma o4s_kept_all : forall (W : world segs) (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  forall a, aview segs (w_H W) m' a = aview segs (w_H W) m a.
Proof.
  intros W m m' H a. rewrite (aview_wrap64 segs (w_H W) m' a), (aview_wrap64 segs (w_H W) m a).
  apply H. apply Z.mod_pos_bound. lia.
Qed.

(* The harness globals' payloads lie in loaded segments: no world hides them, and the world relation at a world's
   view is the relation at the raw memory (check_inflight_settle_cgW.v cis_hull_vis, cis_tw_csw, cis_rng_hull). *)
Lemma o4s_hull_vis : forall (W : world segs) x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. apply (decode_vis_seg W).
  apply (decode_covers_img TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) x); [vm_compute; reflexivity | lia].
Qed.
Lemma o4s_tw_csw : forall (W : world segs) mem Bw,
  tw_at TMAP_A (aview segs (w_H W) mem) Bw -> tw_at TMAP_A (csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  unfold csw_view. rewrite (decode_aview_mrd W mem x (o4s_hull_vis W x (TMAP_A_hull x Hx))). reflexivity.
Qed.
Lemma o4s_rng_hull : forall (W : world segs) lo len, TG.G_HARNESS_LO <= lo -> lo + len <= TG.G_HARNESS_HI ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W lo len H1 H2. apply (decode_rng W); [unfold TG.G_HARNESS_LO in *; lia | unfold TG.G_HARNESS_HI in *; lia |].
  intros b Hb. apply o4s_hull_vis. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The walk                                                          *)
(* ------------------------------------------------------------------ *)

Lemma lc_op4sub_ok : lc_op4sub_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4sub_stmt. intros HP cx op W1 c1 HB HWANT.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS. pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
destruct HWANT as (ly1 & S1 & regs1 & mem1 & md1 & e1 & B1 & at_ & HW). cbv zeta in HW.
destruct HW as (Ec1 & HTC & Hat & R22 & R19 & R20).
unfold lc_tag_common in HTC. cbv zeta in HTC.
destruct HTC as (Hopc & HLC & HOB & Hraw & Hser & HTW & HGA & Q144 & Q56 & Q64 & Q72 & R24 & R25 & R27 & R23).
pose proof HLC as (HCORE & HFR & HSPL & HFSH & HOPOK & He1 & HMET & R21).
set (kd := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) in *.
set (tv := lc_tag_vals (l_pl cx) B1 (sv_c kd)) in *.
set (cs := TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd)) in *.
(* the model *)
pose proof HOPOK as (HAG & Hops & Hcok & Hcn & Hk).
destruct (LOK.op_ok LP.links_holds timg_A (lo_ops op) (lo_B op) (fun _ => 4096) (l_pl cx) (lo_c op) (lo_k op)
  HAG Hops Hcok Hcn ltac:(lia) ltac:(lia)) as (Bf & cf & kf & Eop & _ & _).
destruct (o4s_model (l_pl cx) (lo_B op) B1 (lo_c op) (lo_k op) (fun _ => 4096) Bf cf kf at_ Eop Hopc HOB Hraw Hat)
  as (B3 & r & B4 & B5 & M3 & M4 & M5).
fold kd tv cs in M3, M4, M5.
pose proof (o4s_submit_rc _ _ _ _ M3) as Hr.
(* the geometry *)
destruct (lc_geom B MT XL RLO RHI cx ly1 S1 W1 regs1 mem1 md1 e1 HB HCORE)
  as [HAR1 Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HCORE as (HJ1 & Hfrs1 & HlyF1 & HPERM1 & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
(* the invariant at WANT *)
assert (Hcs : length cs = 32%nat) by exact (o4s_cs_len (l_pl cx) (lo_c op) B1 Hcok).
assert (INV0 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly1 S1 W1 regs1 mem1 md1 e1).
{ split; [exact HLC|]. split; [exact HGA|]. split.
  - unfold lc_spills, o4s_sl.
    apply Forall_cons; [exact Q56|]. apply Forall_cons; [exact Q64|]. apply Forall_cons; [exact Q72|].
    apply Forall_cons; [exact Q144|]. apply Forall_nil.
  - unfold o4s_rv.
    apply Forall_cons; [exact R22|]. apply Forall_cons; [exact R19|]. apply Forall_cons; [exact R24|].
    apply Forall_cons; [exact R25|]. apply Forall_cons; [exact R27|]. apply Forall_cons; [exact R20|].
    apply Forall_nil. }
pose proof (@YM05.alloc_ceiling_val rc) as [CE1 CE2].
destruct Hstk as (Hs1 & Hs2 & Hs3 & Hs4). unfold LF_FRAME in Hsp1.
assert (ESS : SSUBMIT_STK = 4448) by (vm_compute; reflexivity).
assert (ELS : LLVMF_STK = 32768) by (vm_compute; reflexivity).
(* ---- +0x1164 .. +0x1170: a0 = &g_s, a1 = c, the call of diginet_session_submit ---- *)
subst c1. unfold lc_cfg.
set (fx := l_fx cx) in *.
replace (w64 (transport_text + LO_WANT)) with (Z_to_bv 64 (BASE + LO_WANT)) by (rewrite o4s_base; reflexivity).
pose proof (o4s_entry0 fx W1 regs1 [] mem1 LO_WANT) as HS.
assert (HEI : img_env VAL A_LIM (o4s_E regs1 [])) by apply o4s_env_img.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs1 []) (mrestrict (w_H W1) mem1)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ1 SHOK (0, 0).
{ o4s_awr. }
o4s_kept HFr KR1 W1 mem1 ms.
pose proof (o4s_kept_all W1 mem1 (ms_mem ms) KR1) as KR1a. clear HF HFr HG KR1.
assert (HK1 : forall r0, acallee_saved r0 -> r0 <> 23 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r0) = YK11.getr regs1 (Z_to_bv 5 r0)) by o4s_keep HS regs1.
assert (INV1 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly1 S1 W1 (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md1) mat md1) e1).
{ apply (o4s_inv_kept cx op cs _ _ ly1 S1 W1 regs1 mem1 md1 e1 0 ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ LAWS MTL HB
    INV0 HJ1 eq_refl (Permutation_refl _) HK1 (mo_le_refl MT MTL S1)).
  - rewrite ELS. lia.
  - intros a _ _. exact (KR1a a).
  - intros b m i _ _. exact (KR1a (b + i)).
  - intros a _. exact (KR1a a).
  - exact Hcs.
  - apply o4s_sl_ok.
  - apply o4s_rv_ok. }
(* the registers at the call *)
o4s_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 4468)) Q1 ltac:(apply codeptr_val; exact HEI).
o4s_reg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) Q2 ltac:(o4s_atom regs1 Rsp).
o4s_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3 ltac:(o4s_atom regs1 Rgp).
o4s_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4 ltac:(o4s_atom regs1 Rtp).
o4s_reg HS (11%bv : bv 5) (w64 (lc_F cx + 32)) Q11 ltac:(o4s_atom regs1 R23).
o4s_reg HS (23%bv : bv 5) (w64 (lc_F cx + 32)) Q23 ltac:(o4s_atom regs1 R23).
o4s_reg HS (10%bv : bv 5) (w64 SSUBMIT_S) Q10
  ltac:(cbn [sv_denot]; rewrite (img_env_atomP (o4s_E regs1 []) 250%nat HEI) by (unfold A_TEXT; split; [lia | vm_compute; lia]);
        vm_compute; reflexivity).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx)
  by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
(* what the call reads at the call memory *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARc.
pose proof INV1 as (HLC1 & HGA1 & HSL1 & HRV1).
pose proof HLC1 as (HC1 & HFR1 & HSP1 & HFSH1 & _).
pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpresc & _).
destruct (o4s_c_ok cx ly1 S1 W1 (ms_mem ms) _ false cs LAWS HARc HFin HFaddr HFal HFpresc HFSH1) as (HINF & HRD).
assert (H16 : lc_sp1 cx mod 16 = 0).
{ apply Z.mod_divide in Hsp1al as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 2) * 16) by ring.
  apply Z_mod_mult. }
assert (HF4 : (lc_F cx + 32) mod 4 = 0).
{ apply Z.mod_divide in HFal as [q Hq]; [|lia]. rewrite Hq. replace (q * 64 + 32) with ((q * 16 + 8) * 4) by ring.
  apply Z_mod_mult. }
(* +0x1170: the call of diginet_session_submit *)
eapply SRr_bind.
{ refine (lp_submit B MT XL RLO RHI HP fx LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly1 S1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) e1 (ms_regs ms)
    (lc_F cx + 32) r cs (tg_B2 tv) B3 HJ1 _ _ Q3 Q4 Q10 Q11 _ _ _ _ M3 Hcs _ HF4 _ HGA1 _ _ _ _).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, o4s_base. unfold transport_text. rewrite unsigned_lit_small by lia. lia.
  - rewrite QSP. exact H16.
  - rewrite QSP, ESS, ELS. lia.
  - rewrite QSP. lia.
  - apply (tw_kept TMAP_A (aview segs (w_H W1) mem1)); [exact HTW | intros x _; exact (KR1a x)].
  - lia.
  - right. split; [left; exact HINF | exact HRD].
  - unfold decode_off_win, SSUBMIT_CMD_LEN. left. rewrite QSP, ESS. unfold LF_FBYTES in HFceil. lia.
  - intros x Hx. split; intros HX.
    + apply (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) x HARc HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold SSUBMIT_CMD_LEN in Hx; lia | exact (trans_g_img x HX)].
    + apply (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) x HARc HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold SSUBMIT_CMD_LEN in Hx; lia | exact (trans_ro_img x HX)].
  - rewrite Hfrs1. vm_compute. reflexivity.
  - pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
    destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
    assert (He1' : 0 <= e1 <= 2 * Z.of_nat (lo_k op)) by exact He1.
    assert (EEL : EV_LIB = 2048) by reflexivity. assert (EOM : TC.OPS_MAX = 1024) by reflexivity.
    unfold SSUBMIT_EV. lia. }
cbv beta. intros W2 c2 _ HPOST.
unfold transport_ssubmit_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Ec2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 & (HA0 & HTW2)).
assert (Ee2 : e2 = 0) by (unfold SSUBMIT_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Ec2. subst c2.
(* the invariant after the call *)
pose proof HK2 as (K21 & K22 & K23 & K24 & _).
assert (INV2 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly2 S2 W2 regs2 mem2 md2 e1).
{ apply (o4s_inv_kept cx op cs _ _ ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ e1 SSUBMIT_STK ly2 S2 W2 regs2 mem2 md2 LAWS
    MTL HB INV1 HJ2 Hfr2 Hperm2 (fun r0 Hr0 _ => HP2 r0 Hr0) Hmo2).
  - rewrite ESS, ELS. lia.
  - intros a Ha Hna. apply K21; [exact Ha | rewrite QSP; exact Hna].
  - intros b m i Hb Hi. apply (K22 b m i Hb Hi). intros Hw.
    exact (blk_img segs B LAWS ly1 S1 W1 _ _ b m (b + i) HARc Hb ltac:(lia) (o4s_wr_img _ Hw)).
  - intros a Ha. apply (K24 LF_CID (l_fpos cx) a HFin).
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
        change (fs_frame_bytes LF_CID) with 256; unfold lc_SH, LF_FBYTES, shadow_addr in *; lia.
    + intros Hw. destruct Ha as [Ha | Ha].
      * exact (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) a HARc HFin
          ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold LF_FBYTES in Ha; lia) (o4s_wr_img _ Hw)).
      * pose proof (o4s_wr_gs a Hw) as Hg. unfold lc_SH, SHADOW_OFF in Ha. unfold TA_g_s, TW.SZ_g_s in Hg.
        pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). lia.
  - exact Hcs.
  - apply o4s_sl_ok.
  - apply o4s_rv_ok. }
(* ---- +0x1174 .. +0x1188: a1 = c, s7 = rc, a0 = c, a1 = rc, a2 = 144(s1), the call of check_refusal_submit ---- *)
pose proof INV2 as (HLC2 & HGA2 & HSL2 & HRV2).
pose proof HLC2 as (HC2 & HFR2 & _).
pose proof HC2 as (_ & _ & _ & _ & R2_2 & R8_2 & R9_2 & R3_2 & R4_2 & _).
assert (R23_2 : YK11.getr regs2 (Z_to_bv 5 23) = w64 (lc_F cx + 32))
  by exact (eq_trans (HP2 23 ltac:(unfold acallee_saved; lia)) Q23).
set (v144 := bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.S_queued (lo_B op))))) in *.
assert (HV144 : 0 <= v144 < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (bv_swrap 32 (TW.S_queued (lo_B op))))) as H;
  change (bv_modulus 64) with (2 ^ 64) in H; exact H).
assert (S144 : rdword (aview segs (w_H W2) mem2) (lc_sp1 cx + 144) = Some v144).
{ unfold lc_spills in HSL2. rewrite Forall_forall in HSL2. exact (HSL2 (144, v144) ltac:(unfold o4s_sl; cbn; tauto)). }
assert (U9 : bv_unsigned (ew (o4s_E regs2 [w64 v144]) 9) = lc_sp1 cx).
{ rewrite (o4s_ew_reg regs2 _ 9 9%bv ltac:(lia) eq_refl). change (YK11.getr regs2 9%bv) with (YK11.getr regs2 9).
  rewrite R9_2. unfold w64. apply unsigned_lit_small. lia. }
assert (X32 : ew (o4s_E regs2 [w64 v144]) 32 = w64 v144).
{ unfold o4s_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 0). }
assert (HS2 : st_ok_pi segs VAL (o4s_E regs2 [w64 v144]) (mkSS 4468 sr_atoms [o4s_rg144] None (mkFacts [] [] []))
  (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + 4468)) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold o4s_rg144, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ (lc_sp1 cx) 144 8 (SOff 32 0) v144).
    + cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + apply val_mem_of_rdword. exact S144.
  - exact (conj I I).
  - exact (conj I (conj I I)). }
assert (HEI2 : img_env VAL A_LIM (o4s_E regs2 [w64 v144])) by apply o4s_env_img.
assert (SHOK2 : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs2 [w64 v144]) (mrestrict (w_H W2) mem2)) by constructor.
paj_run_tok RUN HS2 HJ2 SHOK2 (0, 0).
{ o4s_awr. }
(* the state at check_refusal_submit's entry *)
o4s_kept HFr KR2 W2 mem2 ms0.
pose proof (o4s_kept_all W2 mem2 (ms_mem ms0) KR2) as KR2a. clear HF HFr HG KR2.
assert (HK3 : forall r0, acallee_saved r0 -> r0 <> 23 ->
  YK11.getr (ms_regs ms0) (Z_to_bv 5 r0) = YK11.getr regs2 (Z_to_bv 5 r0)) by o4s_keep HS2 regs2.
assert (INV3 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly2 S2 W2 (ms_regs ms0) (ms_mem ms0)
  (with_vm_backing (m_vm_lazy md2) mat0 md2) e1).
{ apply (o4s_inv_kept cx op cs _ _ ly2 S2 W2 regs2 mem2 md2 e1 0 ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ LAWS MTL HB
    INV2 HJ2 eq_refl (Permutation_refl _) HK3 (mo_le_refl MT MTL S2)).
  - rewrite ELS. lia.
  - intros a _ _. exact (KR2a a).
  - intros b m i _ _. exact (KR2a (b + i)).
  - intros a _. exact (KR2a a).
  - exact Hcs.
  - apply o4s_sl_ok.
  - apply o4s_rv_ok. }
(* the registers at the call *)
o4s_reg HS2 (1%bv : bv 5) (Z_to_bv 64 (BASE + 4492)) P1 ltac:(apply codeptr_val; exact HEI2).
o4s_reg HS2 (Z_to_bv 5 2) (w64 (lc_sp1 cx)) P2 ltac:(o4s_atom regs2 R2_2).
o4s_reg HS2 (3%bv : bv 5) (w64 (as_gp B)) P3 ltac:(o4s_atom regs2 R3_2).
o4s_reg HS2 (4%bv : bv 5) (w64 (as_tp B)) P4 ltac:(o4s_atom regs2 R4_2).
o4s_reg HS2 (Z_to_bv 5 10) (w64 (lc_F cx + 32)) P10 ltac:(o4s_atom regs2 R23_2).
o4s_reg HS2 (Z_to_bv 5 11) (w64 r) P11 ltac:(o4s_atom regs2 HA0).
o4s_reg HS2 (Z_to_bv 5 23) (w64 r) P23 ltac:(o4s_atom regs2 HA0).
o4s_reg HS2 (Z_to_bv 5 12) (w64 v144) P12 ltac:(cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (PSP : spZ (ms_regs ms0) = lc_sp1 cx).
{ transitivity (bv_unsigned (w64 (lc_sp1 cx))); [unfold spZ; f_equal; exact P2 | unfold w64; apply unsigned_lit_small; lia]. }
(* the facts the leaf reads at the call memory *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARc3.
destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (memS & HJd & _ & _).
pose proof HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _). clear HJd memS.
pose proof INV3 as (HLC3 & HGA3 & HSL3 & HRV3).
pose proof HLC3 as (HC3 & HFR3 & HSP3 & HFSH3 & _).
pose proof HC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpres3 & _).
destruct (lc_geom B MT XL RLO RHI cx ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ e1 HB HC3)
  as [_ _ _ _ HFaddr2 HFin2 _ _ _].
destruct (o4s_c_ok cx ly2 S2 W2 (ms_mem ms0) _ false cs LAWS HARc3 HFin2 HFaddr2 HFal HFpres3 HFSH3) as (HINF3 & HRD3).
destruct (frames_bounds segs B LAWS ly2 S2 W2 (ms_mem ms0) _ LF_CID (l_fpos cx) HARc3 HFin2) as (_ & _ & Happ2).
rewrite HFaddr2 in Happ2. change (fs_frame_bytes LF_CID) with 256 in Happ2.
(* +0x1188: the call of check_refusal_submit *)
pmkst HS2.
assert (EPC1 : pa_sigma TS_check_refusal_submit = LCRSc.CHECK_REFUSAL_SUBMIT) by reflexivity.
rewrite EPC1.
eapply SRr_bind.
{ apply (o4s_leaf fx W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx)
    (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 _ e1 (lc_sp1 cx - lc_sp0 cx) LCRSc.CHECK_REFUSAL_SUBMIT (fun _ => B4 = B3)
    LAWS HJ2).
  - rewrite PSP. ring.
  - rewrite Zminus_mod, H16, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. rewrite ELS. lia.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact P3.
  - exact P4.
  - intros HPRE.
    pose proof (lp_crs B MT XL RLO RHI HP fx) as LF.
    unfold transport_leaf_at, LCRS.transport_check_refusal_submit_cg in LF.
    specialize (LF ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ (lc_sp1 cx - ESTACK) B3 B4 (lc_F cx + 32) cs r
      (TW.S_queued (lo_B op)) HPRE).
    cbv zeta in LF.
    destruct HRD3 as (_ & HRA3 & _ & _).
    apply LF; clear LF.
    + exact P10.
    + exact P11.
    + rewrite P12. unfold w64, v144. apply Z_to_bv_bv_unsigned.
    + lia.
    + pose proof (TWL.u_at_range (lo_B op) TW.A_S_queued 4) as HQ. exact HQ.
    + lia.
    + exact HF4.
    + apply (decode_leafb_bytes_garr8 W2 (ms_mem ms0) (lc_F cx + 32) cs); [exact HGA3 | lia |].
      rewrite Hcs. change (Z.of_nat 32) with 32. change (2 ^ 64) with 18446744073709551616.
      unfold LF_FBYTES in HFceil. lia.
    + exact Hcs.
    + apply (o4s_tw_csw W2). apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW2 | intros x _; exact (KR2a x)].
    + exact M4.
    + rewrite P2, unsigned_lit by lia. apply (decode_leafb_stk W2 (ms_mem ms0)); [unfold ESTACK; lia | lia |].
      intros a Ha. apply Hpres3. unfold ESTACK in Ha. rewrite ELS. lia.
    + rewrite P2, unsigned_lit by lia. unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, ESTACK. lia.
    + unfold AKA.off_stk. rewrite P2, unsigned_lit by lia.
      unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    + exact (decode_leafb_asan_cells B (lp_cells B MT XL RLO RHI HP) ly2 S2 W2 (ms_mem ms0) _ HARc3).
    + rewrite P2, unsigned_lit by lia. apply (@decode_leafb_app_stack rc). unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME. lia.
    + rewrite P2, unsigned_lit by lia. apply (@decode_leafb_app_stack rc). lia.
    + unfold AKA.off_stk. rewrite P2, unsigned_lit by lia.
      unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, AsanCells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite P2, unsigned_lit by lia. unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, AsanCells.CELL_K. lia.
    + unfold AKA.off_stk. rewrite P2, unsigned_lit by lia. unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, LF_FBYTES in *. lia.
    + apply (decode_leafb_addressable W2 (ms_mem ms0) (lc_F cx + 32) 32 HRA3); [lia | lia | |].
      * pose proof (@decode_leafb_app_of_in_app rc (lc_F cx) 256 255 Happ2 ltac:(lia)) as HA.
        unfold AsanCells.app_mem in HA. unfold AsanCells.APPMEM_END.
        unfold AsanCells.LOWMEM_END, AsanCells.HIGHMEM_BEG, AsanCells.APPMEM_END in HA. lia.
      * intros i Hi. replace (lc_F cx + 32 + i) with (lc_F cx + (32 + i)) by ring.
        apply (@decode_leafb_app_of_in_app rc (lc_F cx) 256 (32 + i) Happ2). lia.
    + rewrite P2, unsigned_lit by lia. unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME.
      apply (decode_leafb_rng_vis W2 (ms_mem ms0)); [lia | change (2 ^ 64) with 18446744073709551616; lia |].
      intros a Ha. apply Hpres3. rewrite ELS. lia.
    + exact (proj1 (decode_leafb_rng_cells W2)).
    + exact (proj2 (decode_leafb_rng_cells W2)).
    + intros i Hi.
      pose proof (decode_leafb_rng_shadow W2 (ms_mem ms0) (lc_F cx + 32) 32 HRA3 ltac:(lia) ltac:(lia)
        ltac:(change (2 ^ 64) with 18446744073709551616; unfold LF_FBYTES in HFceil; lia)) as HRS.
      apply (ExecF.rng_sub _ _ _ _ _ HRS); unfold AsanCells.shadow_addr.
      * pose proof (Z.div_le_mono (lc_F cx + 32) (lc_F cx + 32 + i) 8 ltac:(lia) ltac:(lia)). lia.
      * pose proof (Z.div_le_mono (lc_F cx + 32 + i) (lc_F cx + 32 + 32 - 1) 8 ltac:(lia) ltac:(lia)). lia.
    + apply (decode_leafb_rng_vis W2 (ms_mem ms0) (lc_F cx + 32) 32);
        [lia | change (2 ^ 64) with 18446744073709551616; unfold LF_FBYTES in HFceil; lia |].
      intros a Ha. apply HFpres3. unfold LF_FBYTES. lia.
    + rewrite LCRSc.check_refusal_submit_queued_at. apply o4s_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & Ec3 & HJ3 & HP3 & KE3 & Hgr3 & HX3).
change (YK11.getr (ms_regs ms0) 1) with (YK11.getr (ms_regs ms0) 1%bv) in Ec3. rewrite P1 in Ec3. subst c3.
(* the invariant after the call *)
assert (HF8 : lc_F cx / 8 <= lc_F cx) by (apply Z.div_le_upper_bound; lia).
assert (INV4 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly2 S2 W2 regs3 mem3 md3 e1).
{ apply (o4s_inv_kept cx op cs _ _ ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ e1 ESTACK ly2 S2 W2 regs3 mem3 md3 LAWS MTL HB
    INV3 HJ3 eq_refl (Permutation_refl _) (fun r0 Hr0 _ => HP3 r0 Hr0) (mo_le_refl MT MTL S2)).
  - unfold ESTACK. rewrite ELS. lia.
  - intros a Ha Hna. apply KE3; [lia | rewrite PSP; exact Hna].
  - intros b m i Hb Hi.
    destruct (al_blocks segs B LAWS ly2 S2 W2 (ms_mem ms0) _ b m HARc3 Hb) as (_ & H4096 & Hc & _).
    apply KE3; [change (2 ^ 64) with 18446744073709551616; lia | rewrite PSP; unfold ESTACK; lia].
  - intros a Ha. unfold lc_SH, LF_FBYTES, SHADOW_OFF in Ha. unfold LF_FBYTES in HFceil.
    apply KE3; [change (2 ^ 64) with 18446744073709551616; lia | rewrite PSP; unfold ESTACK; lia].
  - exact Hcs.
  - apply o4s_sl_ok.
  - apply o4s_rv_ok. }
(* the world relation after the leaf: its bytes lie below the leaf's window, and check_refusal_submit keeps B3 *)
assert (HTW3 : lc_tw W2 mem3 B4).
{ rewrite HX3. unfold lc_tw. apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW2|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite (KE3 x ltac:(lia) ltac:(rewrite PSP; unfold ESTACK; lia)). exact (KR2a x). }
pose proof INV4 as (HLC4 & HGA4 & HSL4 & HRV4).
pose proof HLC4 as (HC4 & _).
pose proof HC4 as (HJ4 & _ & _ & _ & R2_4 & R8_4 & R9_4 & R3_4 & R4_4 & _).
assert (R20_4 : YK11.getr regs3 (Z_to_bv 5 20) = w64 (if lc_sys tv then 1 else 0)).
{ rewrite Forall_forall in HRV4. exact (HRV4 (20, w64 (if lc_sys tv then 1 else 0)) ltac:(unfold o4s_rv; cbn; tauto)). }
assert (R22_4 : YK11.getr regs3 (Z_to_bv 5 22) = w64 (lc_want tv at_)).
{ rewrite Forall_forall in HRV4. exact (HRV4 (22, w64 (lc_want tv at_)) ltac:(unfold o4s_rv; cbn; tauto)). }
assert (R23_4 : YK11.getr regs3 (Z_to_bv 5 23) = w64 r) by exact (eq_trans (HP3 23 ltac:(unfold acallee_saved; lia)) P23).
(* ---- +0x118c bnez s4, +0x119c: the sys flag decides ---- *)
pose proof (o4s_entry0 fx W2 regs3 [] mem3 0x118c) as HS3.
assert (HEI3 : img_env VAL A_LIM (o4s_E regs3 [])) by apply o4s_env_img.
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs3 []) (mrestrict (w_H W2) mem3)) by constructor.
replace (YK11.getr (ms_regs ms0) 1%bv) with (Z_to_bv 64 (BASE + 0x118c)) by (rewrite P1; reflexivity).
destruct (lc_sys tv) eqn:Esys.
- (* sys: the jump to the cut, B5 = B4 *)
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) 1 HS3 R20_4 eq_refl) as HS3p. clear HS3.
  paj_run_to_tok RUNTO HS3p HJ3 SHOK3 (0, 0) LO_CMDW.
  { o4s_awr. }
  o4s_kept HFr KR3 W2 mem3 ms1.
  pose proof (o4s_kept_all W2 mem3 (ms_mem ms1) KR3) as KR3a. clear HF HFr HG KR3.
  assert (HK5 : forall r0, acallee_saved r0 -> r0 <> 23 ->
    YK11.getr (ms_regs ms1) (Z_to_bv 5 r0) = YK11.getr regs3 (Z_to_bv 5 r0)).
  { intros r0 Hr0 Hn0. destruct (Z.eq_dec r0 20) as [-> | Hne].
    - o4s_reg HS3p (Z_to_bv 5 20) (w64 1) Q20 ltac:(reflexivity). rewrite Q20, R20_4. reflexivity.
    - unfold acallee_saved in Hr0.
      assert (Er : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 19 \/ r0 = 21 \/ r0 = 22 \/
                   r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
      repeat (destruct Er as [-> | Er]; [o4s_kreg HS3p regs3|]); subst r0; o4s_kreg HS3p regs3. }
  lazymatch type of HJ3 with context [with_vm_backing (m_vm_lazy md3) ?mt md3] =>
    set (md5 := with_vm_backing (m_vm_lazy md3) mt md3) in * end.
  assert (INV5 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) md5 e1).
  { apply (o4s_inv_kept cx op cs _ _ ly2 S2 W2 regs3 mem3 md3 e1 0 ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ LAWS MTL HB
      INV4 HJ3 eq_refl (Permutation_refl _) HK5 (mo_le_refl MT MTL S2)).
    - rewrite ELS. lia.
    - intros a _ _. exact (KR3a a).
    - intros b m i _ _. exact (KR3a (b + i)).
    - intros a _. exact (KR3a a).
    - exact Hcs.
    - apply o4s_sl_ok.
    - apply o4s_rv_ok. }
  pmkst HS3p.
  apply SRr_ret.
  replace (Z_to_bv 64 (BASE + 4508)) with (w64 (transport_text + LO_CMDW)) by (rewrite o4s_base; reflexivity).
  lazymatch goal with |- lc_st_cmdw _ _ _ _ _ (mkCfg (YK11.mkst ?rg _ ?mm _) ?mdx) =>
    change (lc_st_cmdw B MT cx op W2 (lc_cfg cx LO_CMDW rg mm mdx)) end.
  refine (o4s_cmdw cx op B1 at_ B3 r B4 B5 ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ e1 Hopc HOB Hraw Hser Hat M3 M4 _
    INV5 _).
  + change (if lc_sys tv then B5 = B4 else TC.check_latest_submit_m B4 r (lc_want tv at_) = Some (B5, tt)).
    rewrite Esys. exact M5.
  + cbv iota in M5. rewrite M5. unfold lc_tw.
    apply (tw_kept TMAP_A (aview segs (w_H W2) mem3)); [exact HTW3 | intros x _; exact (KR3a x)].
- (* not sys: +0x1190 a0 = rc, +0x1194 a1 = want, +0x1198 the call of check_latest_submit (return +0x119c) *)
  cbv iota in M5.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) 0 HS3 R20_4 eq_refl) as HS3p. clear HS3.
  paj_run_tok RUN HS3p HJ3 SHOK3 (0, 0).
  { o4s_awr. }
  o4s_kept HFr KR3 W2 mem3 ms1.
  pose proof (o4s_kept_all W2 mem3 (ms_mem ms1) KR3) as KR3a. clear HF HFr HG KR3.
  assert (HK5 : forall r0, acallee_saved r0 -> r0 <> 23 ->
    YK11.getr (ms_regs ms1) (Z_to_bv 5 r0) = YK11.getr regs3 (Z_to_bv 5 r0)).
  { intros r0 Hr0 Hn0. destruct (Z.eq_dec r0 20) as [-> | Hne].
    - o4s_reg HS3p (Z_to_bv 5 20) (w64 0) Q20 ltac:(reflexivity). rewrite Q20, R20_4. reflexivity.
    - unfold acallee_saved in Hr0.
      assert (Er : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 19 \/ r0 = 21 \/ r0 = 22 \/
                   r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
      repeat (destruct Er as [-> | Er]; [o4s_kreg HS3p regs3|]); subst r0; o4s_kreg HS3p regs3. }
  lazymatch type of HJ3 with context [with_vm_backing (m_vm_lazy md3) ?mt md3] =>
    set (md5 := with_vm_backing (m_vm_lazy md3) mt md3) in * end.
  assert (INV5 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) md5 e1).
  { apply (o4s_inv_kept cx op cs _ _ ly2 S2 W2 regs3 mem3 md3 e1 0 ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ LAWS MTL HB
      INV4 HJ3 eq_refl (Permutation_refl _) HK5 (mo_le_refl MT MTL S2)).
    - rewrite ELS. lia.
    - intros a _ _. exact (KR3a a).
    - intros b m i _ _. exact (KR3a (b + i)).
    - intros a _. exact (KR3a a).
    - exact Hcs.
    - apply o4s_sl_ok.
    - apply o4s_rv_ok. }
  (* the registers at the call *)
  o4s_reg HS3p (1%bv : bv 5) (Z_to_bv 64 (BASE + 4508)) T1 ltac:(apply codeptr_val; exact HEI3).
  o4s_reg HS3p (Z_to_bv 5 2) (w64 (lc_sp1 cx)) T2 ltac:(o4s_atom regs3 R2_4).
  o4s_reg HS3p (3%bv : bv 5) (w64 (as_gp B)) T3 ltac:(o4s_atom regs3 R3_4).
  o4s_reg HS3p (4%bv : bv 5) (w64 (as_tp B)) T4 ltac:(o4s_atom regs3 R4_4).
  o4s_reg HS3p (Z_to_bv 5 10) (w64 r) T10 ltac:(o4s_atom regs3 R23_4).
  o4s_reg HS3p (Z_to_bv 5 11) (w64 (lc_want tv at_)) T11 ltac:(o4s_atom regs3 R22_4).
  assert (TSP : spZ (ms_regs ms1) = lc_sp1 cx).
  { transitivity (bv_unsigned (w64 (lc_sp1 cx))); [unfold spZ; f_equal; exact T2 | unfold w64; apply unsigned_lit_small; lia]. }
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARc5.
  destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (memS & HJd & _ & _).
  pose proof HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _). clear HJd memS.
  pmkst HS3p.
  assert (EPC2 : pa_sigma TS_check_latest_submit = LCLSc.CHECK_LATEST_SUBMIT) by reflexivity.
  rewrite EPC2.
  eapply SRr_bind.
  { apply (o4s_leaf fx W2 (ms_regs ms1) (ms_mem ms1) LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx)
      (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 _ e1 (lc_sp1 cx - lc_sp0 cx) LCLSc.CHECK_LATEST_SUBMIT (fun _ => B5 = B4)
      LAWS HJ3).
    - rewrite TSP. ring.
    - rewrite Zminus_mod, H16, Hsp0al. reflexivity.
    - lia.
    - unfold ESTACK. rewrite ELS. lia.
    - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - exact T3.
    - exact T4.
    - intros HPRE.
      pose proof (lp_cls B MT XL RLO RHI HP fx) as LF.
      unfold transport_leaf_at, LCLS.transport_check_latest_submit_cg in LF.
      specialize (LF ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ (lc_sp1 cx - ESTACK) B4 B5 r (lc_want tv at_) HPRE).
      cbv zeta in LF.
      apply LF; clear LF.
      + exact T10.
      + exact T11.
      + lia.
      + exact (o4s_want_small tv at_).
      + apply (o4s_tw_csw W2). apply (tw_kept TMAP_A (aview segs (w_H W2) mem3)); [exact HTW3 | intros x _; exact (KR3a x)].
      + exact M5.
      + rewrite T2, unsigned_lit by lia. apply (decode_leafb_stk W2 (ms_mem ms1)); [unfold ESTACK; lia | lia |].
        intros a Ha. apply Hpres5. unfold ESTACK in Ha. rewrite ELS. lia.
      + rewrite T2, unsigned_lit by lia. unfold LCLSc.CHECK_LATEST_SUBMIT_FRAME, ESTACK. lia.
      + unfold AKA.off_stk. rewrite T2, unsigned_lit by lia.
        unfold LCLSc.CHECK_LATEST_SUBMIT_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
      + rewrite T2, unsigned_lit by lia. unfold LCLSc.CHECK_LATEST_SUBMIT_FRAME.
        apply (decode_leafb_rng_vis W2 (ms_mem ms1)); [lia | change (2 ^ 64) with 18446744073709551616; lia |].
        intros a Ha. apply Hpres5. rewrite ELS. lia. }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & Ec4 & HJ6 & HP4 & KE4 & Hgr4 & HX4).
  change (YK11.getr (ms_regs ms1) 1) with (YK11.getr (ms_regs ms1) 1%bv) in Ec4. rewrite T1 in Ec4. subst c4.
  assert (INV6 : o4s_inv cx op cs (o4s_sl op tv) (o4s_rv cx tv at_) ly2 S2 W2 regs4 mem4 md4 e1).
  { apply (o4s_inv_kept cx op cs _ _ ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ e1 ESTACK ly2 S2 W2 regs4 mem4 md4 LAWS MTL
      HB INV5 HJ6 eq_refl (Permutation_refl _) (fun r0 Hr0 _ => HP4 r0 Hr0) (mo_le_refl MT MTL S2)).
    - unfold ESTACK. rewrite ELS. lia.
    - intros a Ha Hna. apply KE4; [lia | rewrite TSP; exact Hna].
    - intros b m i Hb Hi.
      destruct (al_blocks segs B LAWS ly2 S2 W2 (ms_mem ms1) _ b m HARc5 Hb) as (_ & H4096 & Hc & _).
      apply KE4; [change (2 ^ 64) with 18446744073709551616; lia | rewrite TSP; unfold ESTACK; lia].
    - intros a Ha. unfold lc_SH, LF_FBYTES, SHADOW_OFF in Ha. unfold LF_FBYTES in HFceil.
      apply KE4; [change (2 ^ 64) with 18446744073709551616; lia | rewrite TSP; unfold ESTACK; lia].
    - exact Hcs.
    - apply o4s_sl_ok.
    - apply o4s_rv_ok. }
  apply SRr_ret.
  replace (Z_to_bv 64 (BASE + 4508)) with (w64 (transport_text + LO_CMDW)) by (rewrite o4s_base; reflexivity).
  lazymatch goal with |- lc_st_cmdw _ _ _ _ _ (mkCfg (YK11.mkst ?rg _ ?mm _) ?mdx) =>
    change (lc_st_cmdw B MT cx op W2 (lc_cfg cx LO_CMDW rg mm mdx)) end.
  refine (o4s_cmdw cx op B1 at_ B3 r B4 B5 ly2 S2 W2 regs4 mem4 md4 e1 Hopc HOB Hraw Hser Hat M3 M4 _ INV6 _).
  + change (if lc_sys tv then B5 = B4 else TC.check_latest_submit_m B4 r (lc_want tv at_) = Some (B5, tt)).
    rewrite Esys. exact M5.
  + rewrite HX4. unfold lc_tw. apply (tw_kept TMAP_A (aview segs (w_H W2) mem3)); [exact HTW3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    rewrite (KE4 x ltac:(lia) ltac:(rewrite TSP; unfold ESTACK; lia)). exact (KR3a x).
Qed.

End op4sub.
