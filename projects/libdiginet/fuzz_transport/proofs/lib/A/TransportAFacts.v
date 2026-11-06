(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from libdiginet/fuzz_frame lib/A/FrameAFacts.v (file sha256 4bd2511c3bc0;
   donor not released), libdiginet/fuzz_frame lib/A/FrameEnv.v (file sha256 9f74740f1d24; donor not released) and the
   HB_* rows of libdiginet/fuzz_frame lib/A/FrameClose.v (file sha256 db13ebe967ec; donor not released) that are facts
   about the record, for libdiginet/fuzz_transport's ASan image (e89be137db17): the record facts that the 64 image-A
   program statements and the entry statement take, each PROVED at the concrete record TransportB (lib/A/AD2l.v);
   module paths and names changed. *)
(* TransportAFacts: every fact about the record that lib/A/TransportClose.v gives to a program statement, stated with
   the type the statement gives it at B := TransportB and proved by computation over the record (FrameAFacts.v form):
   as_const := Tfib_const, as_owned_static := Tfib_owned_static, as_zero_shadow := Tfib_zero_shadow, as_errno :=
   TFIB_ERRNO (lib/A/AF0m.v), as_universe := Tfib_universe (lib/A/ACej.v), as_code := Tfib_code (lib/A/AF0l.v).
   - the cell rows: DgnTransportCg.v transport_cells and every trans_*_cells of a statement file (each conjunct a
     cell of Tfib_const, by fa_cell_mem, or a range inside one Tfib_zero_shadow range, by fa_zshadow_of_b);
   - the G rows: no byte of TransportG.v G_HARNESS is an owned static or errno (trans_g_unowned, trans_g_no_errno),
     so G_HARNESS is a G of W_journalG.v (gx_ok) and of TransportGCg.v (gx_noerrno); g_s is a zero-shadow range
     (trans_gs_zshadow); G_HARNESS lies in the driver's hull (g_in_hull);
   - the read-only rows: no TRANS_RO_RD byte is an owned static (trans_ro_rd_unowned), errno is not read-only
     (trans_rom_no_errno), the slot's read-only range [TRANSPORT_RLO, TRANSPORT_RHI) is the RELRO range TRANS_RLO ..
     TRANS_RHI, inside in_ro_tfa (lib/A/ACeg.v), and every read-only byte lies below the sink's ofl head
     (ro_below_ofl);
   - the code rows: the class entries pc_stack_malloc 0, 1, 2, 4, 5 and the malloc / free wrappers are the listing's;
   - the trace row: receive's malloc and free traces at the entry's contexts CTX_receive (transport_llvmf_utraces);
   - the environment rows: api_env (errno and the wrappers' one-element traces) and model_laws;
   - the sink and meta rows in the G form (HSINK_KEPT_G / HMETA_KEPT_G): the G journal ajournal_gx over G_HARNESS
     is the donor journal from a start memory memS that agrees with the true start memory outside G
     (W_journalG.v ajournal_g); the sink's cells and the meta pointer cells lie outside G's hull, and the meta
     region lies above every image byte, so asink_none / ameta_inv move to memS (lib/Reusable/YE00.v
     asink_none_frame / ameta_ok_frame) and lib/Reusable/YE01.v asink_none_kept / ameta_inv_kept carry them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0s YM05 YK04 YA0i YA0n YG00 YG01 YG05 YG0f YG0n YG0d YG0q YCbq YI00 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YE00 YE01 YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AF0l AF0m ACej AD2l ACeg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG W_journalG TransportDriver
  AD1y AD1u.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase DgnTransportSyms DgnTransportAddr
  DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGCg
  LLVMFuzzerTestOneInput_cg receive_cg diginet_session_config_default_cg settle_cg check_inflight_retry_cg
  check_inflight_settle_cg check_latest_queue_cg check_latest_sent_cg check_sent_frame_cg check_state_data_cg
  desk_named_cg diginet_personality_from_name_cg diginet_session_close_cg diginet_session_init_cg
  diginet_session_poll_cg diginet_session_rx_cg diginet_session_submit_cg diginet_session_tick_cg
  diginet_session_wake_cg io_send_cg m_lost_cg m_rx_cg maybe_online_cg notice_cg on_ack_cg on_announce_cg
  on_data_cg send_control_cg send_data_cg session_lost_cg take_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module WJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.W_journalG.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module YE00 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YE00.
Module YE01 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YE01.
Module AE2k := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AE2k.
Module TGCg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGCg.
Module PL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_cg.
Module PRECV := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_cg.
Module PSCFG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_config_default_cg.
Module PSETTLE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.settle_cg.
Module PCIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_retry_cg.
Module PCIS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_settle_cg.
Module PCLQ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_queue_cg.
Module PCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_sent_cg.
Module PCSF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_sent_frame_cg.
Module PCSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_data_cg.
Module PDN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.desk_named_cg.
Module PPF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_personality_from_name_cg.
Module PSCL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_cg.
Module PSINIT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_init_cg.
Module PPOLL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_poll_cg.
Module PSRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_rx_cg.
Module PSSUB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_submit_cg.
Module PTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_tick_cg.
Module PWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_wake_cg.
Module PIOS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_send_cg.
Module PMLOST := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_lost_cg.
Module PMRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_cg.
Module PMAYBEON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.maybe_online_cg.
Module PNOTICE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.notice_cg.
Module PONACK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_cg.
Module PONANN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_announce_cg.
Module PONDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_data_cg.
Module PSENDCTL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.send_control_cg.
Module PSENDDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.send_data_cg.
Module PSLOST := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.session_lost_cg.
Module PTAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_cg.

(* ===================================================================================================== *)
(* Deciders                                                                                               *)
(* ===================================================================================================== *)
(* Boolean equality and membership on the record's cells (lib/Reusable/YG0f.v aexp / aval / acell). *)
Fixpoint fa_aexp_eqb (x y : aexp) : bool :=
  match x, y with
  | ANum a, ANum b | ASp a, ASp b | AQ a, AQ b | AT a, AT b | AC a, AC b | AF a, AF b | ANB a, ANB b
  | ASB a, ASB b | ATop a, ATop b | ATsd a, ATsd b | AStk a, AStk b | AInst a, AInst b | ADepot a, ADepot b
  | AStore a, AStore b | ATp a, ATp b | AIal a, AIal b | AD a, AD b => Z.eqb a b
  | ASec r a, ASec s b => Nat.eqb r s && Z.eqb a b
  | ASh e, ASh f => fa_aexp_eqb e f
  | _, _ => false
  end.

Lemma fa_aexp_eqb_eq : forall x y, fa_aexp_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn [fa_aexp_eqb]; intros H; try discriminate H.
  all: repeat match goal with
       | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?]
       | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
       | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
       end.
  all: try (subst; reflexivity).
  f_equal. apply IHx. assumption.
Qed.

Definition fa_aval_eqb (x y : aval) : bool :=
  match x, y with
  | AV e, AV f => fa_aexp_eqb e f
  | AVmask m v, AVmask m' v' => Z.eqb m m' && Z.eqb v v'
  | _, _ => false
  end.

Lemma fa_aval_eqb_eq : forall x y, fa_aval_eqb x y = true -> x = y.
Proof.
  intros [e|m v] [f|m' v']; cbn [fa_aval_eqb]; intros H; try discriminate H.
  - f_equal. apply fa_aexp_eqb_eq, H.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition fa_cell_eqb (x y : acell) : bool :=
  fa_aexp_eqb (YG0f.c_at x) (YG0f.c_at y) && Nat.eqb (YG0f.c_w x) (YG0f.c_w y) &&
  fa_aval_eqb (YG0f.c_val x) (YG0f.c_val y).

Lemma fa_cell_eqb_eq : forall x y, fa_cell_eqb x y = true -> x = y.
Proof.
  intros [a w v] [a' w' v']. unfold fa_cell_eqb. cbn [YG0f.c_at YG0f.c_w YG0f.c_val]. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply fa_aexp_eqb_eq in H1. apply Nat.eqb_eq in H2. apply fa_aval_eqb_eq in H3. subst. reflexivity.
Qed.

Fixpoint fa_cell_mem (x : acell) (l : list acell) : bool :=
  match l with [] => false | y :: l' => fa_cell_eqb y x || fa_cell_mem x l' end.

Lemma fa_cell_mem_In : forall x l, fa_cell_mem x l = true -> In x l.
Proof.
  intros x l. induction l as [|y l IH]; cbn [fa_cell_mem In]; intros H; [discriminate H|].
  apply orb_prop in H as [H|H]; [left; apply fa_cell_eqb_eq, H | right; apply IH, H].
Qed.

(* A range [lo, hi) inside one 8-aligned Tfib_zero_shadow range. *)
Lemma fa_zshadow_of_b : forall lo hi,
  existsb (fun r => (fst r mod 8 =? 0) && (fst r <=? lo) && (hi <=? fst r + snd r))%bool
    (as_zero_shadow TransportB) = true ->
  decode_zshadow_at TransportB lo hi.
Proof.
  intros lo hi H. apply existsb_exists in H as (r & Hr & Hb).
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  exists r. split; [exact Hr|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* No byte of the ranges L lies in a range of R. *)
Definition fa_ranges_apart (L R : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun r' => (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r)) R)%bool L.

Lemma fa_ranges_apart_ok : forall L R a, fa_ranges_apart L R = true ->
  Exists (in_zr a) L -> ~ Exists (in_zr a) R.
Proof.
  intros L R a D Hin Hown. unfold fa_ranges_apart in D.
  apply Exists_exists in Hin as (r & Hr & Ha).
  apply Exists_exists in Hown as (r' & Hr' & Ha').
  pose proof (proj1 (forallb_forall _ _) D r Hr) as D1. cbv beta in D1.
  pose proof (proj1 (forallb_forall _ _) D1 r' Hr') as D2. cbv beta in D2.
  unfold in_zr in Ha, Ha'.
  apply orb_prop in D2 as [D2|D2]; apply Z.leb_le in D2; lia.
Qed.

(* Every conjunct of a cell row: a cell of the record's constant table, or a zero-shadow range. *)
Ltac fa_rows :=
  repeat match goal with
  | |- forall _ : alayout, _ => intro
  | |- decode_zshadow_at _ _ _ => apply fa_zshadow_of_b; vm_compute; reflexivity
  | |- _ /\ _ => split
  | |- In _ (as_const _ _) => apply fa_cell_mem_In; vm_compute; reflexivity
  end.

(* ===================================================================================================== *)
(* The cell rows                                                                                          *)
(* ===================================================================================================== *)
(* transport_cells: the 17 runtime cells of AsanCells.v, the payload shadow rows of the read-only globals, and their
   zero-shadow ranges (DgnTransportCg.v). *)
Lemma transport_cells_TB : transport_cells TransportB.
Proof. unfold transport_cells. fa_rows. Qed.

Lemma trans_scfg_cells_TB : PSCFG.trans_scfg_cells TransportB.
Proof. unfold PSCFG.trans_scfg_cells. fa_rows. Qed.

Lemma trans_recv_cells_TB : PRECV.trans_recv_cells TransportB.
Proof. unfold PRECV.trans_recv_cells. fa_rows. Qed.

Lemma trans_settle_cells_TB : PSETTLE.trans_settle_cells TransportB.
Proof. unfold PSETTLE.trans_settle_cells. fa_rows. Qed.

(* trans_llvmf_cells: M's zero shadow, the two unregistered zero ranges, g_last_counter's payload granule and the 40
   guard granules TRANS_LLVMF_F9 (0xf9). *)
Lemma trans_llvmf_cells_TB : PL.trans_llvmf_cells TransportB.
Proof.
  unfold PL.trans_llvmf_cells.
  split; [apply fa_zshadow_of_b; vm_compute; reflexivity|].
  split; [apply fa_zshadow_of_b; vm_compute; reflexivity|].
  split; [apply fa_zshadow_of_b; vm_compute; reflexivity|].
  intros ly. split; [apply fa_cell_mem_In; vm_compute; reflexivity|].
  assert (D : forallb (fun a => fa_cell_mem (z1 (ANum (AsanCells.shadow_addr a)) 0xf9) (Tfib_const ly))
                PL.TRANS_LLVMF_F9 = true) by (vm_compute; reflexivity).
  intros a Ha. apply fa_cell_mem_In. exact (proj1 (forallb_forall _ _) D a Ha).
Qed.

Lemma trans_cir_cells_TB : PCIR.trans_cir_cells TransportB.
Proof. unfold PCIR.trans_cir_cells. fa_rows. Qed.

Lemma trans_cis_cells_TB : PCIS.trans_cis_cells TransportB.
Proof. unfold PCIS.trans_cis_cells. fa_rows. Qed.

Lemma trans_clq_cells_TB : PCLQ.trans_clq_cells TransportB.
Proof. unfold PCLQ.trans_clq_cells. fa_rows. Qed.

Lemma trans_cls_cells_TB : PCLS.trans_cls_cells TransportB.
Proof. unfold PCLS.trans_cls_cells. fa_rows. Qed.

Lemma trans_csf_cells_TB : PCSF.trans_csf_cells TransportB.
Proof. unfold PCSF.trans_csf_cells. fa_rows. Qed.

Lemma trans_csdata_cells_TB : PCSD.trans_csdata_cells TransportB.
Proof. unfold PCSD.trans_csdata_cells. fa_rows. Qed.

Lemma trans_dnamed_cells_TB : PDN.trans_dnamed_cells TransportB.
Proof. unfold PDN.trans_dnamed_cells. fa_rows. Qed.

Lemma trans_pfrom_cells_TB : PPF.trans_pfrom_cells TransportB.
Proof. unfold PPF.trans_pfrom_cells. fa_rows. Qed.

Lemma trans_close_cells_TB : PSCL.trans_close_cells TransportB.
Proof. unfold PSCL.trans_close_cells. fa_rows. Qed.

(* trans_sinit_cells: g_s's zero shadow and the 5 guard granules after it (0xf9). *)
Lemma trans_sinit_cells_TB : PSINIT.trans_sinit_cells TransportB.
Proof.
  unfold PSINIT.trans_sinit_cells.
  split; [apply fa_zshadow_of_b; vm_compute; reflexivity|].
  intros ly i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct E as [-> | [-> | [-> | [-> | ->]]]]; apply fa_cell_mem_In; vm_compute; reflexivity.
Qed.

Lemma trans_poll_cells_TB : PPOLL.trans_poll_cells TransportB.
Proof. unfold PPOLL.trans_poll_cells. fa_rows. Qed.

Lemma trans_srx_cells_TB : PSRX.trans_srx_cells TransportB.
Proof. unfold PSRX.trans_srx_cells. fa_rows. Qed.

Lemma trans_ssubmit_cells_TB : PSSUB.trans_ssubmit_cells TransportB.
Proof. unfold PSSUB.trans_ssubmit_cells. fa_rows. Qed.

Lemma trans_tick_cells_TB : PTICK.trans_tick_cells TransportB.
Proof. unfold PTICK.trans_tick_cells. fa_rows. Qed.

Lemma trans_wake_cells_TB : PWAKE.trans_wake_cells TransportB.
Proof. unfold PWAKE.trans_wake_cells. fa_rows. Qed.

Lemma trans_iosend_cells_TB : PIOS.trans_iosend_cells TransportB.
Proof. unfold PIOS.trans_iosend_cells. fa_rows. Qed.

Lemma trans_ow_cells_TB : PMLOST.trans_ow_cells TransportB.
Proof. unfold PMLOST.trans_ow_cells. fa_rows. Qed.

Lemma trans_mrx_cells_TB : PMRX.trans_mrx_cells TransportB.
Proof. unfold PMRX.trans_mrx_cells. fa_rows. Qed.

Lemma trans_maybeon_cells_TB : PMAYBEON.trans_maybeon_cells TransportB.
Proof. unfold PMAYBEON.trans_maybeon_cells. fa_rows. Qed.

Lemma trans_notice_cells_TB : PNOTICE.trans_notice_cells TransportB.
Proof. unfold PNOTICE.trans_notice_cells. fa_rows. Qed.

Lemma trans_onack_cells_TB : PONACK.trans_onack_cells TransportB.
Proof. unfold PONACK.trans_onack_cells. fa_rows. Qed.

Lemma trans_onann_cells_TB : PONANN.trans_onann_cells TransportB.
Proof. unfold PONANN.trans_onann_cells. fa_rows. Qed.

Lemma trans_ondata_cells_TB : PONDATA.trans_ondata_cells TransportB.
Proof. unfold PONDATA.trans_ondata_cells. fa_rows. Qed.

Lemma trans_sendctl_cells_TB : PSENDCTL.trans_sendctl_cells TransportB.
Proof. unfold PSENDCTL.trans_sendctl_cells. fa_rows. Qed.

Lemma trans_senddata_cells_TB : PSENDDATA.trans_senddata_cells TransportB.
Proof. unfold PSENDDATA.trans_senddata_cells. fa_rows. Qed.

Lemma trans_slost_cells_TB : PSLOST.trans_slost_cells TransportB.
Proof. unfold PSLOST.trans_slost_cells. fa_rows. Qed.

Lemma trans_take_cells_TB : PTAKE.trans_take_cells TransportB.
Proof. unfold PTAKE.trans_take_cells. fa_rows. Qed.

(* ===================================================================================================== *)
(* The G rows                                                                                             *)
(* ===================================================================================================== *)
(* No byte of G_HARNESS is an owned static of the record: the 18 payload ranges are disjoint from every
   Tfib_owned_static range (the statics hold the globals' redzones, not their payloads). *)
Lemma trans_g_unowned_TB : trans_g_unowned TransportB.
Proof.
  assert (D : fa_ranges_apart TG.G_HARNESS (as_owned_static TransportB) = true) by (vm_compute; reflexivity).
  intros a Hin. exact (fa_ranges_apart_ok _ _ a D Hin).
Qed.

(* No byte of G_HARNESS is errno (TFIB_ERRNO 0x5f3a4c lies above G_HARNESS_HI 0x5f3190). *)
Lemma trans_g_no_errno_TB : trans_g_no_errno TransportB.
Proof.
  intros a Ha. pose proof (inG_G_HARNESS_hull a Ha) as H.
  cbn [as_errno TransportB]. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI, TFIB_ERRNO in *. lia.
Qed.

Lemma gx_ok_TB : WJ.gx_ok tfibsegs TransportB TG.G_HARNESS.
Proof. exact (G_HARNESS_gx_ok TransportB trans_g_unowned_TB). Qed.

Lemma gx_noerrno_TB : TGCg.gx_noerrno TransportB TG.G_HARNESS.
Proof. exact (G_HARNESS_gx_noerrno TransportB trans_g_no_errno_TB). Qed.

(* g_s (0x5df9c0, 18264 bytes) is a zero-shadow range of the record. *)
Lemma trans_gs_zshadow_TB : trans_gs_zshadow TransportB.
Proof. unfold trans_gs_zshadow. apply fa_zshadow_of_b. vm_compute. reflexivity. Qed.

(* G_HARNESS lies in the driver's hull [DRV_G_LO, DRV_G_HI) (lib/A/AD1y.v), the premise G_HULL of lib/A/AD1q.v. *)
Lemma g_in_hull_TB : TransportDriver.g_in_hull TG.G_HARNESS.
Proof.
  intros a Ha. pose proof (inG_G_HARNESS_hull a Ha) as H.
  unfold AD1y.DRV_G_LO, AD1y.DRV_G_HI, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
Qed.

(* ===================================================================================================== *)
(* The read-only rows                                                                                     *)
(* ===================================================================================================== *)
(* No TRANS_RO_RD byte is an owned static of the record. *)
Lemma trans_ro_rd_unowned_TB : trans_ro_rd_unowned TransportB.
Proof.
  assert (D : fa_ranges_apart TRANS_RO_RD (as_owned_static TransportB) = true) by (vm_compute; reflexivity).
  intros a Hin. exact (fa_ranges_apart_ok _ _ a D Hin).
Qed.

(* errno (0x5f3a4c) lies outside every non-writable loaded segment and outside the RELRO range. *)
Lemma trans_rom_errno_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? TFIB_ERRNO) ||
    (TFIB_ERRNO + 4 <=? Z.of_N (seg_base s)))%bool tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma trans_rom_no_errno_TB : trans_rom_no_errno TransportB.
Proof.
  intros a [(s & Hin & Hw & Hr) | Hr] He; cbn [as_errno TransportB] in He.
  - pose proof (proj1 (forallb_forall _ _) trans_rom_errno_chk s Hin) as Hb. cbv beta in Hb. rewrite Hw in Hb.
    cbn [orb] in Hb. apply Bool.orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
  - unfold TRANS_RLO, TRANS_RHI, TFIB_ERRNO in *. lia.
Qed.

(* The read-only range the slot is stated over: the RELRO range, .data.rel.ro (0xa3980) to the end of .got
   (0xa4d88), the second disjunct of lib/A/ACeg.v in_ro_tfa. *)
Definition TRANSPORT_RLO : Z := 0xa3980.
Definition TRANSPORT_RHI : Z := 0xa4d88.

Lemma trans_rlo_le : TRANSPORT_RLO <= TRANS_RLO.
Proof. unfold TRANSPORT_RLO, TRANS_RLO. lia. Qed.
Lemma trans_rhi_le : TRANS_RHI <= TRANSPORT_RHI.
Proof. unfold TRANSPORT_RHI, TRANS_RHI. lia. Qed.

Lemma trans_ro_in : forall a, TRANSPORT_RLO <= a < TRANSPORT_RHI -> in_ro_tfa a.
Proof. intros a H. right. unfold TRANSPORT_RLO, TRANSPORT_RHI in H. exact H. Qed.

(* Every non-writable loaded segment ends at or below the sink's ofl head (musl's ofl_head, 0x6141e8), and so does
   TRANSPORT_RHI. *)
Lemma trans_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s ||
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? YI16.sk_ofl_head (sink_head := AE2k.tfib_sink_head)))%bool
    tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma trans_rhi_below_ofl : TRANSPORT_RHI <= YI16.sk_ofl_head (sink_head := AE2k.tfib_sink_head).
Proof. vm_compute. discriminate. Qed.

Lemma ro_below_ofl_TB : @ro_below_ofl tfibsegs TRANSPORT_RLO TRANSPORT_RHI AE2k.tfib_sink_head.
Proof.
  intros a [(s & Hin & Hw & Hr) | Hr].
  - pose proof (proj1 (forallb_forall _ _) trans_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
    cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
  - pose proof trans_rhi_below_ofl. lia.
Qed.

(* ===================================================================================================== *)
(* The code rows                                                                                          *)
(* ===================================================================================================== *)
(* The class entries and the malloc / free wrappers of Tfib_code (lib/A/AF0l.v) are the listing's
   (lib/A/Prog/DgnTransportAddr.v): both are fuzz_transport.asan's symbol table. *)
Lemma pc_stack_malloc0_TB : pc_stack_malloc (as_code TransportB) 0 = transport_sigma TS___asan_stack_malloc_0.
Proof. reflexivity. Qed.
Lemma pc_stack_malloc1_TB : pc_stack_malloc (as_code TransportB) 1 = transport_sigma TS___asan_stack_malloc_1.
Proof. reflexivity. Qed.
Lemma pc_stack_malloc2_TB : pc_stack_malloc (as_code TransportB) 2 = transport_sigma TS___asan_stack_malloc_2.
Proof. reflexivity. Qed.
Lemma pc_stack_malloc4_TB : pc_stack_malloc (as_code TransportB) 4 = transport_sigma TS___asan_stack_malloc_4.
Proof. reflexivity. Qed.
Lemma pc_stack_malloc5_TB : pc_stack_malloc (as_code TransportB) 5 = transport_sigma TS___asan_stack_malloc_5.
Proof. reflexivity. Qed.
Lemma pc_wrap_malloc_TB : pc_wrap_malloc (as_code TransportB) = transport_sigma TS___interceptor_trampoline_malloc.
Proof. reflexivity. Qed.
Lemma pc_wrap_free_TB : pc_wrap_free (as_code TransportB) = transport_sigma TS___interceptor_trampoline_free.
Proof. reflexivity. Qed.

(* ===================================================================================================== *)
(* The trace row                                                                                          *)
(* ===================================================================================================== *)
(* receive's malloc trace (return address RECV_RA_MALLOC 0x83818, then the tail of the context) and free trace (the
   context), at the seven contexts CTX_receive, are in Tfib_universe. *)
Lemma transport_llvmf_utraces_TB : PL.transport_llvmf_utraces TransportB.
Proof.
  unfold PL.transport_llvmf_utraces, PRECV.trans_recv_uctx.
  assert (D : forallb (fun c =>
      memZL (decode_utrace (pc_malloc_ra0 (as_code TransportB)) (PRECV.RECV_RA_MALLOC :: tl c))
        (as_universe TransportB) &&
      memZL (decode_utrace (pc_free_ra0 (as_code TransportB)) c) (as_universe TransportB))%bool
      PL.CTX_receive = true) by (vm_compute; reflexivity).
  intros c Hc.
  pose proof (proj1 (forallb_forall _ _) D c Hc) as E. cbv beta in E.
  apply andb_prop in E as [E1 E2].
  split; apply memZL_In; assumption.
Qed.

(* ===================================================================================================== *)
(* The environment rows                                                                                   *)
(* ===================================================================================================== *)
(* errno lies below kLowMemEnd and inside one loaded segment, and the one-element traces of the malloc and free
   wrappers are in the record's trace universe (libdiginet/fuzz_frame lib/A/FrameEnv.v frame_api_env form). *)
Lemma api_env_TB : api_env tfibsegs TransportB.
Proof.
  assert (E : ((0 <=? as_errno TransportB) && (as_errno TransportB + 4 <=? kLowMemEnd) &&
    existsb (fun s : Segment => (Z.of_N (seg_base s) <=? as_errno TransportB) &&
      (as_errno TransportB + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs)%bool = true)
    by (vm_compute; reflexivity).
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  apply existsb_exists in E3 as (s & Hs & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [split; [exact E1 | exact E2] | split].
  - intros a Ha. unfold in_img. exists s. split; [exact Hs | lia].
  - split; apply In_of_existsb; vm_compute; reflexivity.
Qed.

(* The allocator model's laws at the record's universe (lib/Reusable/YG05.v model_laws_ok over the ts_universe field
   of TransportB_syms). *)
Lemma model_laws_TB : model_laws (as_universe TransportB).
Proof. exact (model_laws_ok (as_universe TransportB) (ts_universe TransportB TransportB_syms)). Qed.

(* ===================================================================================================== *)
(* The sink and meta rows in the G form                                                                   *)
(* ===================================================================================================== *)
(* lib/A/AD1u.v tfib_AIL at TransportB (libdiginet/fuzz_frame lib/A/FrameClose.v HB_SINK_IMG_LAWS form). *)
Lemma sink_img_laws_TB : @YE01.asink_img_laws AE2k.tfib_sink_head tfibsegs TransportB AE2k.tfib_K.
Proof. apply AD1u.tfib_AIL; first [exact TransportB_syms | apply AR_laws_ok]. Qed.

Section sink.
Context {rc : YM05.RunCeil}.
Local Notation SK := AE2k.tfib_sink_head.
Local Notation KS := AE2k.tfib_K.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* A byte outside G reads the same at two memories that agree outside G (W_journalG.v gagree). *)
Lemma mbyte_out_G : forall (W : world segs) (m m' : word -> option byte) a,
  WJ.gagree TG.G_HARNESS (w_H W) m m' -> 0 <= a < 2 ^ 64 -> ~ WJ.inG TG.G_HARNESS a ->
  mbyte segs (rd W m') a = mbyte segs (rd W m) a.
Proof.
  intros W m m' a Hag Ha Hn. unfold mbyte. rewrite (Hag (Z_to_bv 64 a)); [reflexivity|].
  apply WJ.inGb_false. rewrite YP03.unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* The sink's cells (musl's __libc.threaded / need_locks 0x613d81 / 0x613d83, ofl_lock 0x6141e0, ofl_head 0x6141e8,
   __stack_chk_guard 0x613b30) lie above G_HARNESS_HI; the meta pointer cells (0xac240, 0xac248) below
   G_HARNESS_LO. *)
Lemma sink_cells_out_G : forall a,
  YE00.aenv_core KS a \/ (YE00.ak_ofl_head KS <= a < YE00.ak_ofl_head KS + 8) ->
  0 <= a < 2 ^ 64 /\ ~ WJ.inG TG.G_HARNESS a.
Proof.
  intros a Ha. unfold YE00.aenv_core, YE00.ak_ofl_head in Ha.
  cbn [YE00.ak_threaded YE00.ak_need_locks YE00.ak_ofl_lock YE00.ak_canary AE2k.tfib_K] in Ha.
  unfold AE2k.A_threaded, AE2k.A_need_locks, AE2k.A_ofl_lock, AE2k.FF_canary in Ha.
  split; [change (2 ^ 64) with 18446744073709551616; lia|]. intros HG. pose proof (inG_G_HARNESS_hull a HG) as H.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in H. lia.
Qed.

Lemma meta_cells_out_G : forall a,
  (YE00.ak_meta_ptr KS <= a < YE00.ak_meta_ptr KS + 8) \/ (YE00.ak_meta_mem KS <= a < YE00.ak_meta_mem KS + 8) ->
  0 <= a < 2 ^ 64 /\ ~ WJ.inG TG.G_HARNESS a.
Proof.
  intros a Ha. cbn [YE00.ak_meta_ptr YE00.ak_meta_mem AE2k.tfib_K] in Ha.
  unfold AE2k.FF_meta_ptr, AE2k.FF_meta_mem in Ha.
  split; [change (2 ^ 64) with 18446744073709551616; lia|]. intros HG. pose proof (inG_G_HARNESS_hull a HG) as H.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in H. lia.
Qed.

(* HSINK_KEPT_G: the entry statement's premise of that name (YE01.v asink_none_kept over the G journal). *)
Lemma HSINK_KEPT_G :
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @WJ.ajournal_gx rc SK segs TransportB TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    YE00.asink_none segs KS (rd W0 mem0) md0 -> YE00.asink_none segs KS (rd W' mem') md'.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hc HS.
  destruct HJ as (_ & _ & (memS & HJd & Hag) & _). rewrite !Z.add_0_r in HJd.
  apply (YE01.asink_none_kept (rc := rc) (SK := SK) segs TransportB KS sink_img_laws_TB
    STK sp0 FP ly S W0 memS md0 own ly' S' W' mem' md' k HJd Hc).
  apply (YE00.asink_none_frame segs KS (rd W0 mem0) (rd W0 memS)); [|exact HS].
  intros a Ha. destruct (sink_cells_out_G a Ha) as [Hr Hn]. exact (mbyte_out_G W0 mem0 memS a Hag Hr Hn).
Qed.

(* HMETA_KEPT_G: the entry statement's premise of that name (YE01.v ameta_inv_kept over the G journal). The meta
   region [M, M + AMETA_SIZE) lies above every image byte (ameta_inv), and every byte of G is an image byte
   (DgnTransportCg.v trans_g_img), so the region has no byte of G. *)
Lemma HMETA_KEPT_G :
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @WJ.ajournal_gx rc SK segs TransportB TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    YE01.ameta_inv segs KS ly (rd W0 mem0) M -> YE01.ameta_inv segs KS ly' (rd W' mem') M.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM.
  destruct HJ as (_ & _ & (memS & HJd & Hag) & _). rewrite !Z.add_0_r in HJd.
  apply (YE01.ameta_inv_kept (rc := rc) (SK := SK) segs TransportB KS sink_img_laws_TB
    STK sp0 FP ly S W0 memS md0 own ly' S' W' mem' md' k M HJd).
  destruct HM as (Hx & Himg & Hok). split; [exact Hx|]. split; [exact Himg|].
  pose proof Hok as (_ & _ & HM0 & HM47 & _).
  apply (YE00.ameta_ok_frame segs KS (rd W0 mem0) (rd W0 memS) M); [|exact Hok].
  intros a [Ha | [Ha | Ha]].
  - destruct (meta_cells_out_G a (or_introl Ha)) as [Hr Hn]. exact (mbyte_out_G W0 mem0 memS a Hag Hr Hn).
  - destruct (meta_cells_out_G a (or_intror Ha)) as [Hr Hn]. exact (mbyte_out_G W0 mem0 memS a Hag Hr Hn).
  - apply (mbyte_out_G W0 mem0 memS a Hag);
      [unfold YE00.AMETA_SIZE in *; change (2 ^ 47) with 140737488355328 in HM47;
       change (2 ^ 64) with 18446744073709551616; lia|].
    intros HG. pose proof (Himg a (trans_g_img a HG)) as Hlt. lia.
Qed.
End sink.

Print Assumptions transport_cells_TB.
Print Assumptions trans_llvmf_cells_TB.
Print Assumptions trans_sinit_cells_TB.
Print Assumptions trans_g_unowned_TB.
Print Assumptions trans_rom_no_errno_TB.
Print Assumptions ro_below_ofl_TB.
Print Assumptions transport_llvmf_utraces_TB.
Print Assumptions api_env_TB.
Print Assumptions HSINK_KEPT_G.
Print Assumptions HMETA_KEPT_G.
