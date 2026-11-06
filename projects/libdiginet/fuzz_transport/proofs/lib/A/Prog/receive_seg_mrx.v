(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1969 of its 2149 lines of code are new or changed and 959 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_head.v, with its module paths and module names changed; 546 of its 625 lines of code are new or changed and 2070 lines of the source are left out. *)
(* receive_seg_mrx: Lemma recv_mrx : recv_mrx_stmt (lib/A/Prog/receive_seg_cut.v), the mrx piece of the image-A ASan walk
   of receive (fuzz_transport.asan 0x837d0 = transport_sigma TS_receive, AF_receive = 0x256c of
   lib/A/Prog/DgnTransportList.v): from the mrx cut (+0x248 = 0x83a18, by_poll = 0) to the set cut (+0x274 = 0x83a44).
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) at k + 1 events; the runs
   are lib/A/Prog/TransportGRunA.v paj_run_x, the two callees are G-form callees in the same journal:
     run A   +0x248 .. +0x250  `mv a0, s0` (a), `mv a1, s2` (n), `jal m_rx` (no region: nothing is read or written);
     m_rx    m_rx_cg.v transport_m_rx_cg at transport_sigma TS_m_rx, return address +0x254 = 0x83a24: the frame
             TFrame a bytes at MRX_STK (garr8 of the copy: the cut's recv_blk; trans_src_ok: the frame's block
             (a, max (n, 1)), decode_in_block; decode_off_win: the block lies below alloc_ceiling, the window above),
             a + n < 2 ^ 64, mrx_apart (every byte of mrx_wr lies in G's hull, an image range: mx_mrx_hull,
             mx_hull_img; a block byte is not an image byte: YCbq.v blk_img), trans_rom_view_rd (the cut's
             acall_kept_g keeps the TRANS_RO_RD bytes: mx_rom), tw_at at recv_w2 Bw bytes (the cut's) and the model's
             m_rx_m (receive_cg.v recv_model at a <> 0, by_poll = 0). Its post: a0 = ticked, tw_at at Bx; its
             acall_kept_g at the call state folds into the walk's with TransportGCg.v dk_kept_trans_nf_g
             (NF := False; mrx_wr is a row of recv_wr bytes).
     run B   +0x254 .. +0x270  the 8-byte load of g_now (A_OBJ 27, a constant address: the region mx_now, whose chunk
             is TW.g_now Bx by TWorldG.v tw_read_val), `mv s1, a0` (ticked), a0 = &g_s (A_OBJ 9), `mv a1, s0`,
             `mv a2, s2`, `jal diginet_session_rx` (the region is read only).
     rx      diginet_session_rx_cg.v transport_diginet_session_rx_cg at transport_sigma TS_diginet_session_rx, return
             address +0x274 = 0x83a44 = RECV_SET: buf = a, b = bytes, now = g_now Bx, TF = Some (TFrame a bytes): the
             frame's bytes kept across m_rx (its block clause: the block lies outside mrx_wr), the placement as for
             m_rx at the state after it (its Permutation of the blocks), srx_buf_off_g and trans_tf_off_g (a block byte
             is not a byte of G), srx_apart (every byte of srx_wr lies in G's hull: mx_srx_hull), tw_at at Bx and
             g_fail_next Bx <= 1 (TModel/TIoRecv.v m_rx_gk keeps g_fail_next; mx_gf_w2: recv_w2 keeps it), the run
             invariants at Bx (recv_inv_stmt's third clause), the guarded (3) from recv_fix's recv_dn_each (poll_dn_in
             puts the OW.dn body range in [a, a + n): a sub-range of the frame's block), the five counts (TICK_CID =
             POLL_CID: the + 1 premise), st_nev. Its post folds likewise (srx_wr bytes is a row of recv_wr bytes).
   At its return the walk is at the set cut with B3 = By: tw_at and g_fail_next from rx's X, TRunInv.run_inv By from
   recv_inv_stmt's fourth clause, settle_m By ticked = Some (Bw', tt) from recv_model, 0 <= ticked <= 1
   (TModel/TRxFacts.v m_rx_m_01), the saved words kept (they lie in [sp - 64, sp), above both callees' windows),
   s0 = a and s1 = ticked (both callee-saved across rx). *)
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
DgnTransportCg TransportGCg TransportGRwA TransportGRunA TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require
  TWorld TCb TImg TSess0 TSess TOps TWorldLemmas TIoRecv TRxFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require receive.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoRecv.
Module TRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRxFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module RCV := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.receive.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The callees' written ranges lie in G's hull, an image range        *)
(* ------------------------------------------------------------------ *)

(* A field of a world row whose bytes lie in [G_HARNESS_LO, G_HARNESS_HI) (decided on closed offsets). *)
Lemma mx_twa_hull : forall o b A w x, twa_fld o b A w x ->
  (TG.G_HARNESS_LO <=? b + (A - o)) && (b + (A - o) + w <=? TG.G_HARNESS_HI) = true ->
  TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI.
Proof.
intros o b A w x H E. unfold twa_fld in H. apply andb_prop in E as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(* G's hull lies in one loaded segment of the image (decided by vm_compute). *)
Lemma mx_hull_img : forall x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI -> in_img tfibsegs x.
Proof.
intros x Hx. apply (decode_seg_covers_img [(TG.G_HARNESS_LO, TG.G_HARNESS_HI - TG.G_HARNESS_LO)] x).
- vm_compute. reflexivity.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* Split a written-range hypothesis into its rows. *)
Ltac mx_dest :=
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H|H]
  | H : exists _, _ |- _ => let i := fresh "i" in destruct H as [i H]
  | H : _ /\ _ |- _ => let H1 := fresh "Hc" in let H2 := fresh "Hd" in destruct H as [H1 H2]
  end.
(* t holds no local variable (vm_compute of an open arithmetic term unfolds every branch of its stuck matches). *)
Ltac mx_has_var t := match t with context [?v] => is_var v end.
Ltac mx_closed t := tryif (idtac; mx_has_var t) then fail else idtac.
(* One row: a notice store (TransportGNotice.v notice_wr_G), a field at closed offsets, or an entry of an array
   indexed below its bound. *)
Ltac mx_leaf :=
  match goal with
  | H : notice_wr _ _ _ |- _ => exact (inG_G_HARNESS_hull _ (notice_wr_G _ _ _ H))
  | H : twa_fld ?o ?b ?A ?w _ |- _ =>
      first [ mx_closed constr:((o, b, A, w)); apply (mx_twa_hull _ _ _ _ _ H); vm_compute; reflexivity
            | unfold twa_fld, TA_OW, TA_GOT, TA_g_s, TA_g_cmd, TA_M, TW.A_OW_t_state, TW.A_GOT_t_state,
                TC.A_OW_dn_body, TW.A_Cmd_st, TW.A_S_queue_bytes, TW.OFF_OW, TW.OFF_GOT, TW.OFF_g_s, TW.OFF_g_cmd,
                TW.OFF_M, TW.OW_t_ESZ, TW.GOT_t_ESZ, TW.S_queue_ESZ, TC.TRANS_MAX, TW.OW_dn_N, TW.S_queue_N,
                TC.CMDS_MAX, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *; lia ]
  end.

(* m_rx's stores (m_rx_cg.v mrx_wr) lie in G's hull. *)
Lemma mx_mrx_hull : forall x, mrx_wr x -> TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI.
Proof. intros x H. unfold mrx_wr in H. mx_dest; mx_leaf. Qed.

(* diginet_session_rx's stores (diginet_session_rx_cg.v srx_wr, every callee row at any world) lie in G's hull. *)
Lemma mx_srx_hull : forall b x, srx_wr b x -> TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI.
Proof.
intros b x H.
unfold srx_wr, onann_wr, onack_wr, ondata_wr, tick_wr, wake_wr, maybeon_wr, slost_wr, senddata_wr, iosend_wr in H.
mx_dest; mx_leaf.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Model facts                                                       *)
(* ------------------------------------------------------------------ *)

Ltac mx_len := first [ assumption
  | apply RCV.r_len_upd; [ mx_len | lia | rewrite ?repeat_length, ?TWL.length_put; lia ] ].

(* op_begin's stores and the store at g_rx_send leave g_fail_next (lib/Prog/T/receive.v r_gf_b1, r_gf_upd). *)
Lemma mx_gf_w2 : forall Bw bytes, length Bw = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (recv_w2 Bw bytes) = TW.g_fail_next Bw.
Proof.
intros Bw bytes HL.
pose proof (TIR.len_w Bw HL) as LB. unfold TW.W_LEN in LB.
assert (L1 : Z.of_nat (length (recv_w1 Bw)) = 65616).
{ change (recv_w1 Bw) with (RCV.rb_b1 Bw).
  unfold RCV.rb_b1, TW.set_M_fail, TW.set_OW_desk_off, TW.A_M_fail, TW.A_OW_desk_off, TW.OFF_M, TW.OFF_OW,
    TW.OFF_GOT, TW.SZ_OW, TW.SZ_GOT.
  cbv zeta. change (0xff20 + 232) with 65544. change (0x0 + 88) with 88.
  change 0xff20 with 65312. change 0xfe3c with 65084.
  change (Z.to_nat 304) with 304%nat. change (Z.to_nat 224) with 224%nat.
  mx_len. }
unfold recv_w2, TW.set_g_rx_send.
rewrite RCV.r_gf_upd;
  [| exact L1 | unfold TW.OFF_g_rx_send; lia | rewrite TWL.length_put; unfold TW.OFF_g_rx_send; lia
   | left; unfold TW.OFF_g_rx_send; lia].
change (recv_w1 Bw) with (RCV.rb_b1 Bw). exact (RCV.r_gf_b1 Bw HL).
Qed.

Lemma mx_req : forall n, 0 <= n -> req_size (Z.max 1 n) = Z.max 1 n.
Proof. intros n Hn. unfold req_size. destruct (Z.max 1 n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The two symbolic states and the run tactics                        *)
(* ------------------------------------------------------------------ *)

(* The value of register q in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac mx_reg HS q v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mx_reg: no match for" T; fail
  end.

(* The write rights of a run whose regions have no writable byte. *)
Ltac mx_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* Such a run wrote nothing: every byte's view is the one it started from. *)
Ltac mx_kept HFr :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr);
  [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; exfalso;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |]);
    destruct Hin
  | exact Ha
  | let Hf := fresh "Hf" in intros Hf; destruct Hf ].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation: the 32 registers, the shadow base (atom 32), and for run B the 8 bytes of g_now (atom 33). *)
Definition mx_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).
Definition mx_F : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition MX_Bx : sv := SOff 32 0.
(* run A: no region. *)
Definition ss_mx0 (pc : Z) : sstate := mkSS pc sr_atoms [] None mx_F.
(* run B: g_now (object 27), read only. *)
Definition mx_now : YP09.region := YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 33 0))].
Definition ss_mx1 (pc : Z) : sstate := mkSS pc sr_atoms [mx_now] None mx_F.

Lemma mx_ew32 : forall regs extra, ew (mx_E regs (w64 SHADOW_OFF :: extra)) 32%nat = Z_to_bv 64 SHADOW_OFF.
Proof.
intros regs extra. unfold mx_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs (w64 SHADOW_OFF :: extra) 0%nat).
Qed.

Lemma mx_agree : forall regs extra, env_agree 32 (Ereg regs extra) (mx_E regs extra).
Proof. intros regs extra. split; [intros m Hm; unfold mx_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma mx_entry0 : forall (W2 : world segs) (regs : bvmap 5 word) mem k,
  st_ok_pi segs VAL (mx_E regs [w64 SHADOW_OFF]) (ss_mx0 k)
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom segs))).
Proof.
intros W2 regs mem k. rewrite restrict_mkst_fx. unfold ss_mx0.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- unfold mx_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite mx_ew32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma mx_entry1 : forall (W2 : world segs) (regs : bvmap 5 word) mem k Bx,
  tw_at TMAP_A (aview segs (w_H W2) mem) Bx ->
  st_ok_pi segs VAL (mx_E regs [w64 SHADOW_OFF; w64 (TW.g_now Bx)]) (ss_mx1 k)
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom segs))).
Proof.
intros W2 regs mem k Bx Htw.
set (E := mx_E regs [w64 SHADOW_OFF; w64 (TW.g_now Bx)]).
assert (V27 : VAL (A_OBJ 27) = TA_g_now) by (vm_compute; reflexivity).
assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; unfold E, mx_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E33 : ew E 33%nat = w64 (TW.g_now Bx)).
{ unfold E, mx_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs [w64 SHADOW_OFF; w64 (TW.g_now Bx)] 1%nat). }
assert (U27 : base_val E (Some (A_OBJ 27)) = TA_g_now).
{ cbn [base_val]. rewrite (EOB 27%nat ltac:(lia)), V27. apply unsigned_lit_small. unfold TA_g_now. lia. }
pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as R34. change (8 * Z.of_nat 8) with 64 in R34.
rewrite restrict_mkst_fx. unfold ss_mx1.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold mx_now, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite U27. split; [unfold TA_g_now; lia|]. split; [unfold TA_g_now; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 33 0) (TW.g_now Bx)).
  + cbn [sv_denot]. rewrite E33. unfold w64. rewrite (unsigned_lit_small (TW.g_now Bx)) by exact R34.
    rewrite Z.add_0_r. reflexivity.
  + exact R34.
  + lia.
  + exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok Htw TMAP_A_g_now
      ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold mx_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  unfold E. rewrite mx_ew32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* What a call keeps, moved to a later memory whose view is the same at every address and whose present bytes grow. *)
Lemma mx_kept_view : forall G lyc Sc (W : world segs) memc (W2 : world segs) mem2 mem3 slo shi (E : Z -> Prop),
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) mem3 x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mem3 x) ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
intros G lyc Sc W memc W2 mem2 mem3 slo shi E (K1 & K2 & K3 & K4 & K5 & K6) HV HP.
assert (HV' : forall x, aview segs (w_H W2) mem3 x = aview segs (w_H W2) mem2 x).
{ intros x. rewrite (aview_wrap64 segs _ mem3 x), (aview_wrap64 segs _ mem2 x).
  apply HV. apply Z.mod_pos_bound. lia. }
split; [|split; [|split; [|split; [|split]]]].
- intros x Hx Hw. rewrite HV'. exact (K1 x Hx Hw).
- intros b m i Hb Hi Hn. rewrite HV'. exact (K2 b m i Hb Hi Hn).
- intros x Hi HnG Hno He. rewrite HV'. exact (K3 x Hi HnG Hno He).
- intros cid pos x Hin Hr Hn. rewrite HV'. exact (K4 cid pos x Hin Hr Hn).
- intros x Hx Hw Hp. exact (HP x (K5 x Hx Hw Hp)).
- intros x Hx. exact (HP x (K6 x Hx)).
Qed.

(* The read-only bytes the callees read stay the image's: acall_kept_g keeps every TRANS_RO_RD byte. *)
Lemma mx_rom : forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W2 mem2.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E HRU HRE (_ & _ & K3 & _) Hrom a Ha.
rewrite <- (Hrom a Ha).
destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
unfold TG.G_HARNESS_LO in Gh. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma recv_mrx : @recv_mrx_stmt fx rc B MT.
Proof.
unfold recv_mrx_stmt, recv_mrx_at.
intros INV SET LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw'
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HRES HBLK HTW Hbp HREGS.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof CALLS as (_ & _ & _ & _ & MRXC & RXC & _ & _).
pose proof HFIX as (HJ0 & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hsp16 & Hwlo & Hwhi & _ & _ & Hn64 & _ & _ &
  Htw0 & Hgf & _ & Hrom & Hrinv & Hdn & C1 & C2 & C3 & C4 & C5 & Hnev & _).
pose proof HCUR as (HJ2 & Hfr2 & Hperm2 & Hmo2 & HK2 & Hsaved & Ha4096).
pose proof HRES as (Haddr & Hm).
pose proof HREGS as ((R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R18).
unfold recv_blk in HBLK.
pose proof (Nat2Z.is_nonneg (length bytes)) as Hn0.
(* ---- the model: m_rx_m, diginet_session_rx_m, settle_m at the malloc's address, by_poll = 0 ---- *)
rewrite recv_model in Hm.
assert (Ea0 : (a =? 0) = false) by (apply Z.eqb_neq; lia).
rewrite Ea0, Hbp in Hm. change (negb (0 =? 0)) with false in Hm. cbv beta iota in Hm.
lazymatch type of Hm with context [TC.m_rx_m ?I ?F ?X ?N] =>
  destruct (TC.m_rx_m I F X N) as [[Bx ticked]|] eqn:Emrx; cbv beta iota in Hm; [|discriminate Hm] end.
lazymatch type of Hm with context [TSS.diginet_session_rx_m ?I ?F ?X ?b ?nw] =>
  destruct (TSS.diginet_session_rx_m I F X b nw) as [[By rr]|] eqn:Erx; cbv beta iota in Hm; [|discriminate Hm] end.
lazymatch type of Hm with context [TC.settle_m ?X ?t] =>
  destruct (TC.settle_m X t) as [[B4 u]|] eqn:Eset; cbv beta iota in Hm; [|discriminate Hm] end.
destruct u. pose proof (recv_some_inv_u B4 Bw' Hm) as EB4. subst B4.
pose proof (TRX.m_rx_m_01 _ _ _ _ _ _ Emrx) as T01.
pose proof (tw_len _ _ _ Htw0) as HLBw.
pose proof (tw_len _ _ _ HTW) as HLw2.
destruct (TIR.m_rx_gk (recv_w2 Bw bytes) HLw2 _ _ _ _ _ _ (TIR.gkeep_refl _) Emrx) as [LBx GBx].
assert (HLBx : length Bx = Z.to_nat TW.W_LEN) by (rewrite LBx; exact HLw2).
assert (Hgfx : TW.g_fail_next Bx <= 1) by (rewrite GBx, (mx_gf_w2 Bw bytes HLBw); exact Hgf).
destruct INV as (_ & _ & INV3 & INV4 & _).
pose proof (INV3 Bw bytes _ _ Bx ticked HLBw Hrinv Emrx) as RIx.
pose proof (INV4 _ Bx bytes (TW.g_now Bx) By rr HLBx RIx Erx) as RIy.
pose proof RIx as (I1 & I2 & I4 & I5a & I5b & I4b & I2b).
pose proof (Hdn a Haddr) as Hdn1. rewrite Hbp in Hdn1. change (0 =? 0) with true in Hdn1. cbv beta iota in Hdn1.
pose proof (Hdn1 Bx ticked Emrx) as HDN. clear Hdn1.
(* ---- the stack and the layout ---- *)
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hlyc as (_ & _ & _ & _ & _ & ELFc & _).
clear HJi0 memS0.
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (_ & Hly2 & _). pose proof Hly2 as (_ & _ & _ & _ & _ & ELF2 & _).
clear HJi2 memS2.
assert (ERS : RECV_STK = 16448) by reflexivity.
assert (EMS : MRX_STK = 8352) by reflexivity.
assert (ESS : SRX_STK = 9168) by reflexivity.
assert (HspR : alloc_ceiling + 16448 <= spZ regs) by lia.
assert (HspH : spZ regs <= 2 ^ 47) by lia.
(* ---- the frame's block (a, max (n, 1)): below alloc_ceiling, not an image byte ---- *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hinb2 : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) (in_eq _ _)).
pose proof (mx_req (Z.of_nat (length bytes)) Hn0) as ERQ.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 a _ HAR2 Hinb2) as (_ & _ & Hceila & _).
rewrite ERQ in Hceila.
assert (Hac0 : 4096 < alloc_ceiling) by lia.
assert (NIMG : forall x, a <= x < a + Z.max 1 (Z.of_nat (length bytes)) -> ~ in_img segs x).
{ intros x Hx. apply (blk_img segs B LAWS ly2 S2 W2 mem2 md2 a _ x HAR2 Hinb2). rewrite ERQ. exact Hx. }
assert (NG : forall x, a <= x < a + Z.of_nat (length bytes) -> ~ inG TG.G_HARNESS x)
  by (intros x Hx HG; exact (NIMG x ltac:(lia) (trans_g_img x HG))).
assert (NMRX : forall x, a <= x < a + Z.of_nat (length bytes) -> ~ mrx_wr x)
  by (intros x Hx Hw; exact (NIMG x ltac:(lia) (mx_hull_img x (mx_mrx_hull x Hw)))).
assert (NSRX : forall x, a <= x < a + Z.of_nat (length bytes) -> ~ srx_wr bytes x)
  by (intros x Hx Hw; exact (NIMG x ltac:(lia) (mx_hull_img x (mx_srx_hull bytes x Hw)))).
(* ---- run A, +0x248 .. +0x250: a0 = s0, a1 = s2, `jal m_rx` ---- *)
pose proof (mx_entry0 W2 regs2 mem2 RECV_MRX) as HS.
assert (HEI : img_env VAL A_LIM (mx_E regs2 [w64 SHADOW_OFF])) by (unfold mx_E; apply Eimg_env).
assert (SHOK : sh_ok segs MX_Bx [] (mx_E regs2 [w64 SHADOW_OFF]) (mrestrict (w_H W2) mem2))
  by (unfold sh_ok; apply Forall_nil).
assert (EEA : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (mx_E regs2 [w64 SHADOW_OFF]) m = YK11.getr regs2 q)
  by (intros m q Hq; unfold mx_E; apply ew_Eimg_Ereg_nat; exact Hq).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
{ mx_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msA) x = aview segs (w_H W2) mem2 x)
  by (mx_kept HFr).
assert (GA1 : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem msA) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
clear HF HFr HG.
pmkst HS.
mx_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 10176)) Q1 ltac:(apply codeptr_val; exact HEI).
mx_reg HS (Z_to_bv 5 10) (w64 a) Q10
  ltac:(cbn [sv_denot]; rewrite (EEA 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
mx_reg HS (Z_to_bv 5 11) (w64 (Z.of_nat (length bytes))) Q11
  ltac:(cbn [sv_denot]; rewrite (EEA 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok segs (w_H W2) (mx_E regs2 [w64 SHADOW_OFF]) _ msA regs2 [w64 SHADOW_OFF] HS);
      [apply mx_agree | vm_compute; reflexivity]).
assert (T2 : YK11.getr (ms_regs msA) 2 = w64 (spZ regs - RECV_FRAME))
  by exact (eq_trans (HP0 2 ltac:(hnf; lia)) R2).
assert (T3 : YK11.getr (ms_regs msA) 3 = w64 (as_gp B))
  by exact (eq_trans (eq_trans (HP0 3 ltac:(hnf; lia)) R3) Hgp).
assert (T4 : YK11.getr (ms_regs msA) 4 = w64 (as_tp B))
  by exact (eq_trans (eq_trans (HP0 4 ltac:(hnf; lia)) R4) Htp).
assert (USPA : spZ (ms_regs msA) = spZ regs - 64).
{ change (spZ (ms_regs msA)) with (bv_unsigned (YK11.getr (ms_regs msA) 2)). rewrite T2.
  unfold w64, RECV_FRAME. apply unsigned_lit_small. lia. }
assert (EBR1 : BASE + 10176 = 0x83a24) by (vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_m_rx) rg mm mdx) Q) end.
(* m_rx's premises *)
assert (PRO : YK0s.ret_ok (YK11.getr (ms_regs msA) 1)).
{ rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity]. }
assert (PRA : 4096 <= raZ (ms_regs msA)).
{ unfold raZ. rewrite Q1, EBR1. rewrite unsigned_lit_small by lia. lia. }
assert (PS16 : spZ (ms_regs msA) mod 16 = 0).
{ rewrite USPA. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
assert (PWLO : sp0 - STK <= spZ (ms_regs msA) - MRX_STK) by (rewrite USPA, EMS; rewrite ERS in Hwlo; lia).
assert (PWHI : spZ (ms_regs msA) <= sp0) by (rewrite USPA; lia).
assert (PTF : trans_tframe_at B ly2 S2 W2 (ms_mem msA) (ms_regs msA) MRX_STK (Some (TI.TFrame a bytes))).
{ unfold trans_tframe_at. cbn [TI.tf_addr TI.tf_bytes].
  split; [lia|]. split.
  - change (map DSpec.bz bytes) with (TW.zs bytes).
    apply (garr8_frame segs _ _ _ _ HBLK). intros x Hx. unfold TW.zs in Hx. rewrite length_map in Hx.
    apply mbyte_of_aview. apply KA1. lia.
  - split.
    + unfold trans_src_ok, decode_in_block. left. exists a, (Z.max 1 (Z.of_nat (length bytes))).
      split; [exact Hinb2 | lia].
    + unfold decode_off_win. left. rewrite USPA, EMS. lia. }
assert (PFN : TI.tf_addr (TI.TFrame a bytes) + Z.of_nat (length bytes) < 2 ^ 64) by (cbn [TI.tf_addr]; lia).
assert (PAP : mrx_apart (TI.TFrame a bytes)).
{ intros x Hw Hx. cbn [TI.tf_addr TI.tf_bytes] in Hx. exact (NMRX x Hx Hw). }
assert (KA2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msA) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)) by exact (mx_kept_view _ _ _ _ _ _ _ _ _ _ _ HK2 KA1 GA1).
assert (PROM : trans_rom_view_rd W2 (ms_mem msA)) by exact (mx_rom _ _ _ _ _ _ _ _ _ HRU HRE KA2 Hrom).
assert (PTW : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msA)) (recv_w2 Bw bytes)).
{ apply (tw_kept TMAP_A (aview segs (w_H W2) mem2) _ _ HTW). intros x Hx.
  pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA1. lia. }
assert (PEV : st_nev S + (k + 1) + MRX_EV <= EV_MAX) by (unfold MRX_EV; unfold RECV_EV in Hnev; lia).
(* +0x250: m_rx, in the same G journal *)
eapply SRr_bind.
{ exact (MRXC fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem msA) _ (k + 1) (ms_regs msA)
    (TI.TFrame a bytes) (Z.of_nat (length bytes)) ticked (recv_w2 Bw bytes) Bx
    HJ2 PRO PRA T3 T4 Q10 Q11 PS16 PWLO PWHI PTF PFN PAP PROM PTW Emrx PEV). }
intros W3 c3 _ HQ.
unfold transport_mrx_post, transport_cg_post in HQ. cbv beta in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e3 & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX10 & HXtw).
assert (He30 : e3 = 0) by (unfold MRX_EV in He3; lia). subst e3.
rewrite Z.add_0_r in HJ3. rewrite Q1 in Hc3. subst c3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (K3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem msA) W3 mem3
    (spZ regs - RECV_STK) (spZ regs) (spZ (ms_regs msA) - MRX_STK) (spZ (ms_regs msA)) (recv_wr bytes) mrx_wr
    (fun _ => False)).
  - lia.
  - lia.
  - intros c q. unfold frame_addr. rewrite ELF2, ELFc. reflexivity.
  - intros f Hf. rewrite Hfr2. exact Hf.
  - intros bm Hbm. exact (Permutation_in _ (Permutation_sym Hperm2) (in_cons _ _ _ Hbm)).
  - intros _ _ _ _ _ [].
  - intros _ _ _ _ _ [].
  - exact KA2.
  - exact HK3.
  - rewrite USPA, EMS. lia.
  - rewrite USPA. lia.
  - intros x Hx. left. unfold recv_wr. do 8 right. left. exact Hx. }
(* the registers m_rx keeps *)
assert (X2 : YK11.getr regs3 (Z_to_bv 5 2) = w64 (spZ regs - RECV_FRAME))
  by exact (eq_trans (HP3 2 ltac:(hnf; lia)) T2).
assert (X3 : YK11.getr regs3 (Z_to_bv 5 3) = w64 (as_gp B)) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) T3).
assert (X4 : YK11.getr regs3 (Z_to_bv 5 4) = w64 (as_tp B)) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) T4).
assert (X8 : YK11.getr regs3 (Z_to_bv 5 8) = w64 a)
  by exact (eq_trans (HP3 8 ltac:(hnf; lia)) (eq_trans (HP0 8 ltac:(hnf; lia)) R8)).
assert (X18 : YK11.getr regs3 (Z_to_bv 5 18) = w64 (Z.of_nat (length bytes)))
  by exact (eq_trans (HP3 18 ltac:(hnf; lia)) (eq_trans (HP0 18 ltac:(hnf; lia)) R18)).
(* ---- run B, +0x254 .. +0x270: a3 = g_now, s1 = a0, a0 = &g_s, a1 = s0, a2 = s2, `jal diginet_session_rx` ---- *)
pose proof (mx_entry1 W3 regs3 mem3 10176 Bx HXtw) as HS3.
assert (HEIB : img_env VAL A_LIM (mx_E regs3 [w64 SHADOW_OFF; w64 (TW.g_now Bx)])) by (unfold mx_E; apply Eimg_env).
assert (SHOK3 : sh_ok segs MX_Bx [] (mx_E regs3 [w64 SHADOW_OFF; w64 (TW.g_now Bx)]) (mrestrict (w_H W3) mem3))
  by (unfold sh_ok; apply Forall_nil).
assert (EEB : forall m (q : bv 5), Z.of_nat m = bv_unsigned q ->
  ew (mx_E regs3 [w64 SHADOW_OFF; w64 (TW.g_now Bx)]) m = YK11.getr regs3 q)
  by (intros m q Hq; unfold mx_E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (EB33 : ew (mx_E regs3 [w64 SHADOW_OFF; w64 (TW.g_now Bx)]) 33%nat = w64 (TW.g_now Bx)).
{ unfold mx_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs3 [w64 SHADOW_OFF; w64 (TW.g_now Bx)] 1%nat). }
assert (EB250 : ew (mx_E regs3 [w64 SHADOW_OFF; w64 (TW.g_now Bx)]) 250%nat = Z_to_bv 64 TA_g_s).
{ unfold mx_E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). f_equal; vm_compute; reflexivity. }
paj_run_tok RUN HS3 HJ3 SHOK3 YC4b.Bspan.
{ mx_awr. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into msB end.
assert (KB1 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msB) x = aview segs (w_H W3) mem3 x)
  by (mx_kept HFr).
assert (GB1 : forall x, apresent (w_H W3) mem3 x -> apresent (w_H W3) (ms_mem msB) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
clear HF HFr HG.
pmkst HS3.
pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as Rnow. change (8 * Z.of_nat 8) with 64 in Rnow.
mx_reg HS3 (1%bv : bv 5) (Z_to_bv 64 (BASE + 10208)) RB1 ltac:(apply codeptr_val; exact HEIB).
mx_reg HS3 (Z_to_bv 5 10) (w64 SRX_S) RB10
  ltac:(cbn [sv_denot]; rewrite EB250, Z.add_0_r; rewrite unsigned_lit_small by (unfold TA_g_s; lia); reflexivity).
mx_reg HS3 (Z_to_bv 5 11) (w64 a) RB11
  ltac:(cbn [sv_denot]; rewrite (EEB 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X8).
mx_reg HS3 (Z_to_bv 5 12) (w64 (Z.of_nat (length bytes))) RB12
  ltac:(cbn [sv_denot]; rewrite (EEB 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X18).
mx_reg HS3 (Z_to_bv 5 13) (w64 (TW.g_now Bx)) RB13
  ltac:(cbn [sv_denot]; rewrite EB33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 9) (w64 ticked) RB9
  ltac:(cbn [sv_denot]; rewrite (EEB 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HX10).
mx_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) RB2
  ltac:(cbn [sv_denot]; rewrite (EEB 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) RB3
  ltac:(cbn [sv_denot]; rewrite (EEB 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) RB4
  ltac:(cbn [sv_denot]; rewrite (EEB 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) RB8
  ltac:(cbn [sv_denot]; rewrite (EEB 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 22) (YK11.getr regs3 (Z_to_bv 5 22)) RB22
  ltac:(cbn [sv_denot]; rewrite (EEB 22%nat (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 23) (YK11.getr regs3 (Z_to_bv 5 23)) RB23
  ltac:(cbn [sv_denot]; rewrite (EEB 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 24) (YK11.getr regs3 (Z_to_bv 5 24)) RB24
  ltac:(cbn [sv_denot]; rewrite (EEB 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 25) (YK11.getr regs3 (Z_to_bv 5 25)) RB25
  ltac:(cbn [sv_denot]; rewrite (EEB 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 26) (YK11.getr regs3 (Z_to_bv 5 26)) RB26
  ltac:(cbn [sv_denot]; rewrite (EEB 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mx_reg HS3 (Z_to_bv 5 27) (YK11.getr regs3 (Z_to_bv 5 27)) RB27
  ltac:(cbn [sv_denot]; rewrite (EEB 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (USPB : spZ (ms_regs msB) = spZ regs - 64).
{ change (spZ (ms_regs msB)) with (bv_unsigned (YK11.getr (ms_regs msB) (Z_to_bv 5 2))). rewrite (eq_trans RB2 X2).
  unfold w64, RECV_FRAME. apply unsigned_lit_small. lia. }
assert (EBR2 : BASE + 10208 = 0x83a44) by (vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_diginet_session_rx) rg mm mdx) Q) end.
(* diginet_session_rx's premises *)
pose proof (Permutation_in _ (Permutation_sym Hperm3) Hinb2) as Hinb3.
assert (KBLK : forall x, a <= x < a + Z.of_nat (length bytes) ->
  aview segs (w_H W3) (ms_mem msB) x = aview segs (w_H W2) mem2 x).
{ intros x Hx. rewrite KB1 by lia.
  pose proof HK3 as (_ & L2 & _).
  pose proof (L2 a (Z.max 1 (Z.of_nat (length bytes))) (x - a) Hinb2 ltac:(rewrite ERQ; lia)
    ltac:(replace (a + (x - a)) with x by lia; exact (NMRX x Hx))) as E2.
  replace (a + (x - a)) with x in E2 by lia.
  refine (eq_trans E2 _). apply KA1. lia. }
assert (GARR : garr8 segs (mrestrict (w_H W3) (ms_mem msB)) a (TW.zs bytes)).
{ apply (garr8_frame segs _ _ _ _ HBLK). intros x Hx. unfold TW.zs in Hx. rewrite length_map in Hx.
  apply mbyte_of_aview. exact (KBLK x Hx). }
assert (SRC : trans_src_ok B ly3 S3 W3 (ms_mem msB) a (Z.of_nat (length bytes))).
{ unfold trans_src_ok, decode_in_block. left. exists a, (Z.max 1 (Z.of_nat (length bytes))).
  split; [exact Hinb3 | lia]. }
assert (OFFW : decode_off_win (ms_regs msB) SRX_STK a (Z.of_nat (length bytes)))
  by (unfold decode_off_win; left; rewrite USPB, ESS; lia).
assert (QRO : YK0s.ret_ok (YK11.getr (ms_regs msB) 1)).
{ rewrite RB1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity]. }
assert (QRA : 4096 <= raZ (ms_regs msB)).
{ unfold raZ. rewrite RB1, EBR2. rewrite unsigned_lit_small by lia. lia. }
assert (QS16 : spZ (ms_regs msB) mod 16 = 0).
{ rewrite USPB. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
assert (QWLO : sp0 - STK <= spZ (ms_regs msB) - SRX_STK) by (rewrite USPB, ESS; rewrite ERS in Hwlo; lia).
assert (QWHI : spZ (ms_regs msB) <= sp0) by (rewrite USPB; lia).
assert (QNOW : 0 <= TW.g_now Bx < 2 ^ 64) by exact Rnow.
assert (QTW : tw_at TMAP_A (aview segs (w_H W3) (ms_mem msB)) Bx).
{ apply (tw_kept TMAP_A (aview segs (w_H W3) mem3) _ _ HXtw). intros x Hx.
  pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KB1. lia. }
assert (QTF : trans_tframe_at B ly3 S3 W3 (ms_mem msB) (ms_regs msB) SRX_STK (Some (TI.TFrame a bytes))).
{ unfold trans_tframe_at. cbn [TI.tf_addr TI.tf_bytes].
  split; [lia|]. split; [change (map DSpec.bz bytes) with (TW.zs bytes); exact GARR|].
  split; [exact SRC | exact OFFW]. }
assert (QTFG : trans_tf_off_g (Some (TI.TFrame a bytes))).
{ intros fr Efr x Hx.
  assert (E' : TI.TFrame a bytes = fr)
    by exact (f_equal (fun o => match o with Some f => f | None => fr end) Efr).
  subst fr. cbn [TI.tf_addr TI.tf_bytes] in Hx. exact (NG x Hx). }
assert (K3b : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem msB) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)) by exact (mx_kept_view _ _ _ _ _ _ _ _ _ _ _ K3 KB1 GB1).
assert (QROM : trans_rom_view_rd W3 (ms_mem msB)) by exact (mx_rom _ _ _ _ _ _ _ _ _ HRU HRE K3b Hrom).
assert (QAP : srx_apart (Some (TI.TFrame a bytes)) bytes).
{ intros x Hw fr Efr Hx.
  assert (E' : TI.TFrame a bytes = fr)
    by exact (f_equal (fun o => match o with Some f => f | None => fr end) Efr).
  subst fr. cbn [TI.tf_addr TI.tf_bytes] in Hx. exact (NSRX x Hx Hw). }
assert (Q3 : DSpec.fr_code bytes = 0 -> srx_mac_bad Bx bytes = false -> TW.S_desk_known Bx <> 0 ->
  TS0.memeq 6 (DSpec.fr_src bytes) (TW.S_desk_mac Bx) = true -> TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
  DSpec.fr_cmd bytes = TS0.DIGINET_CMD_DATA -> ondata_dup Bx bytes = false -> DSpec.fr_keepalive bytes = false ->
  trans_src_ok B ly3 S3 W3 (ms_mem msB) (TC.OW_dn_body Bx (TW.GOT_ndata Bx)) (DSpec.fr_body_len bytes) /\
  decode_off_win (ms_regs msB) SRX_STK (TC.OW_dn_body Bx (TW.GOT_ndata Bx)) (DSpec.fr_body_len bytes)).
{ intros G1 G2 G3 G4 G5 G6 G7 G8.
  destruct (HDN G1 G2 G3 G4 G5 G6 G7 G8) as (fr' & Efr & Hlo & Hhi).
  assert (E' : TI.TFrame a bytes = fr')
    by exact (f_equal (fun o => match o with Some f => f | None => fr' end) Efr).
  subst fr'. cbn [TI.tf_addr TI.tf_bytes] in Hlo, Hhi.
  split.
  - unfold trans_src_ok, decode_in_block. left. exists a, (Z.max 1 (Z.of_nat (length bytes))).
    split; [exact Hinb3 | lia].
  - unfold decode_off_win. left. rewrite USPB, ESS. lia. }
assert (QC1 : count_cid SRX_CID (frames S3) < fs_frames SRX_CID) by (rewrite Hfr3, Hfr2; exact C2).
assert (QC2 : count_cid ONANN_CID (frames S3) < fs_frames ONANN_CID) by (rewrite Hfr3, Hfr2; exact C3).
assert (QC3 : count_cid TICK_CID (frames S3) < fs_frames TICK_CID)
  by (rewrite Hfr3, Hfr2; change TICK_CID with POLL_CID; lia).
assert (QC4 : count_cid SENDDATA_CID (frames S3) < fs_frames SENDDATA_CID) by (rewrite Hfr3, Hfr2; exact C4).
assert (QC5 : count_cid ONDATA_CID (frames S3) + 2 < fs_frames ONDATA_CID) by (rewrite Hfr3, Hfr2; exact C5).
assert (QEV : st_nev S + (k + 1) + SRX_EV <= EV_MAX) by (rewrite srx_ev_zero; unfold RECV_EV in Hnev; lia).
assert (QGP : YK11.getr (ms_regs msB) 3 = w64 (as_gp B)) by exact (eq_trans RB3 X3).
assert (QTP : YK11.getr (ms_regs msB) 4 = w64 (as_tp B)) by exact (eq_trans RB4 X4).
(* +0x270: diginet_session_rx, in the same G journal *)
eapply SRr_bind.
{ exact (RXC fx STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem msB) _ (k + 1) (ms_regs msB)
    a (TW.g_now Bx) rr bytes (Some (TI.TFrame a bytes)) Bx By
    HJ3 QRO QRA QGP QTP RB10 RB11 RB12 RB13 QS16 QWLO QWHI QNOW ltac:(lia) GARR SRC OFFW NG QTW Hgfx Erx
    QTF QTFG QROM QAP I1 I2 I2b I4 I4b I5a I5b Q3 QC1 QC2 QC3 QC4 QC5 QEV). }
intros W4 c4 _ HQ.
unfold transport_srx_post, transport_cg_post in HQ. cbv beta in HQ.
destruct HQ as (ly4 & S4 & regs4 & mem4 & md4 & e4 & Hc4 & He4 & HJ4 & HP4 & Hfr4 & Hperm4 & HK4 & Hmo4 &
  HY10 & HYtw & HYgf).
assert (He40 : e4 = 0) by (rewrite srx_ev_zero in He4; lia). subst e4.
rewrite Z.add_0_r in HJ4. rewrite RB1 in Hc4. subst c4.
assert (K4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W4 mem4 (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly3 S3 W memc W3 (ms_mem msB) W4 mem4
    (spZ regs - RECV_STK) (spZ regs) (spZ (ms_regs msB) - SRX_STK) (spZ (ms_regs msB)) (recv_wr bytes)
    (srx_wr bytes) (fun _ => False)).
  - lia.
  - lia.
  - intros c q. unfold frame_addr. rewrite ELF3, ELFc. reflexivity.
  - intros f Hf. rewrite Hfr3, Hfr2. exact Hf.
  - intros bm Hbm. apply (Permutation_in _ (Permutation_sym Hperm3)).
    exact (Permutation_in _ (Permutation_sym Hperm2) (in_cons _ _ _ Hbm)).
  - intros _ _ _ _ _ [].
  - intros _ _ _ _ _ [].
  - exact K3b.
  - exact HK4.
  - rewrite USPB, ESS. lia.
  - rewrite USPB. lia.
  - intros x Hx. left. unfold recv_wr. do 9 right. left. exact Hx. }
(* the saved words lie above both callees' windows *)
assert (KSTK : forall x, spZ regs - 64 <= x < spZ regs -> aview segs (w_H W4) mem4 x = aview segs (w_H W2) mem2 x).
{ intros x Hx.
  pose proof HK4 as (L41 & _). pose proof HK3 as (L31 & _).
  refine (eq_trans (L41 x ltac:(lia) ltac:(rewrite USPB; lia)) _).
  refine (eq_trans (KB1 x ltac:(lia)) _).
  refine (eq_trans (L31 x ltac:(lia) ltac:(rewrite USPA; lia)) _).
  apply KA1. lia. }
assert (HSo : forall o, In o RECV_SAVED -> 8 <= fst o <= 56).
{ intros o Ho. unfold RECV_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
(* the set cut, +0x274 *)
change (Z_to_bv 64 (BASE + 10208)) with (Z_to_bv 64 (BASE + RECV_SET)).
refine (SET LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw'
  ly4 S4 W4 mem4 md4 regs4 By ticked HFIX _ HRES HYtw HYgf RIy Eset _ _).
- unfold recv_cur.
  split; [exact HJ4|].
  split; [rewrite Hfr4, Hfr3; exact Hfr2|].
  split; [exact (Permutation_trans Hperm4 (Permutation_trans Hperm3 Hperm2))|].
  split.
  { pose proof (mo_le_trans MT MTL _ _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo3) Hmo4) as M.
    rewrite !Z.add_0_r in M. exact M. }
  split; [exact K4|].
  split; [|exact Ha4096].
  rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
- destruct T01 as [-> | ->]; lia.
- unfold recv_regs_set, recv_regs_keep.
  split; [split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]|split].
  + exact (eq_trans (HP4 2 ltac:(hnf; lia)) (eq_trans RB2 X2)).
  + exact (eq_trans (HP4 3 ltac:(hnf; lia)) (eq_trans RB3 (eq_trans (HP3 3 ltac:(hnf; lia))
      (eq_trans (HP0 3 ltac:(hnf; lia)) R3)))).
  + exact (eq_trans (HP4 4 ltac:(hnf; lia)) (eq_trans RB4 (eq_trans (HP3 4 ltac:(hnf; lia))
      (eq_trans (HP0 4 ltac:(hnf; lia)) R4)))).
  + exact (eq_trans (HP4 22 ltac:(hnf; lia)) (eq_trans RB22 (eq_trans (HP3 22 ltac:(hnf; lia))
      (eq_trans (HP0 22 ltac:(hnf; lia)) R22)))).
  + exact (eq_trans (HP4 23 ltac:(hnf; lia)) (eq_trans RB23 (eq_trans (HP3 23 ltac:(hnf; lia))
      (eq_trans (HP0 23 ltac:(hnf; lia)) R23)))).
  + exact (eq_trans (HP4 24 ltac:(hnf; lia)) (eq_trans RB24 (eq_trans (HP3 24 ltac:(hnf; lia))
      (eq_trans (HP0 24 ltac:(hnf; lia)) R24)))).
  + exact (eq_trans (HP4 25 ltac:(hnf; lia)) (eq_trans RB25 (eq_trans (HP3 25 ltac:(hnf; lia))
      (eq_trans (HP0 25 ltac:(hnf; lia)) R25)))).
  + exact (eq_trans (HP4 26 ltac:(hnf; lia)) (eq_trans RB26 (eq_trans (HP3 26 ltac:(hnf; lia))
      (eq_trans (HP0 26 ltac:(hnf; lia)) R26)))).
  + exact (eq_trans (HP4 27 ltac:(hnf; lia)) (eq_trans RB27 (eq_trans (HP3 27 ltac:(hnf; lia))
      (eq_trans (HP0 27 ltac:(hnf; lia)) R27)))).
  + exact (eq_trans (HP4 8 ltac:(hnf; lia)) (eq_trans RB8 X8)).
  + exact (eq_trans (HP4 9 ltac:(hnf; lia)) RB9).
Qed.
End s.
