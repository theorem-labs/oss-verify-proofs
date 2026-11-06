(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 466 of its 517 lines of code are new or changed and 508 lines of the source are left out. *)
(* diginet_session_poll_seg_now1 (image B): Theorem pw_now1_piece : pw_now1_stmt
   (lib/B/Prog/diginet_session_poll_segs.v), the now piece: from the cut now1 (+0x1c4, 0x8ac5c) to the cut recv1
   (+0x23c, 0x8acd4). The code is image A's (lib/A/Prog/diginet_session_poll_seg_now1.v) at offsets + 8.
   - +0x1c4 `jalr a1`: a1 = io.now_us = io_now (the model's call_now; kit pw_m_go), the call through
     diginet_session_poll_seg_leaf.v pw_now_call; its return (+0x1c8) gives a0 = io_now_m Bw.
   - +0x1c8 .. +0x1d4: s10 = now, a0 = s, a1 = now, `jal diginet_session_deadline` (pw_deadline_call); a0 = due.
   - +0x1d8 .. +0x210: the wait of :512-515 (bgeu, the 8-byte read-only load at A_OBJ 91 = TRANS_K_POLL, which
     trans_rom_view_rd reads as the image's 0x20c49ba5e353f7cf, sub, addi, srli, mulhu, srli, sext.w, blt, bltz). It
     writes a0, a1 and a3 only, and io_recv reads none of them, so every path is run to the join +0x214 and closed by
     the one lemma pn_j214 at the join.
   - +0x214 .. +0x238: the checks of s + 80 and s + 64 (their shadow bytes at s11 and s5 are 0: g_s's zero shadow,
     trans_poll_cells), io.ctx and io.recv loaded (tw_at), s9 = buf, a2 = 1514, a1 = buf, to the cut recv1.
   No run stores a byte, so the facts of the cut are carried by diginet_session_poll_seg_kit.v pw_run_win at an
   unchanged view. *)
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
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require io_now_cg diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_rt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  diginet_session_poll_seg_leaf diginet_session_poll_seg_grecv diginet_session_poll_seg_grx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
(* The offsets: io_now's return (+0x1c8), the deadline's return (+0x1d8), the join of the wait (+0x214). *)
Definition PN_C1 : Z := AF_diginet_session_poll + 0x1c8.
Definition PN_C2 : Z := AF_diginet_session_poll + 0x1d8.
Definition PN_J : Z := AF_diginet_session_poll + 0x214.
(* The 8 bytes at TRANS_K_POLL (the division constant of :513). *)
Definition PN_KPOLL : Z := 0x20c49ba5e353f7cf.
Lemma pn_pcs : PW_NOW1 = 39356 /\ PN_C1 = 39360 /\ PN_C2 = 39376 /\ PN_J = 39436 /\ PW_RECV1 = 39476.
Proof. repeat split; reflexivity. Qed.

(* The state at +0x1d8: the read-only constant the not-taken arm of the bgeu loads. *)
Definition PN_RK : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 91)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SLit PN_KPOLL))].
Definition ss_pn2 : sstate := mkSS PN_C2 sr_atoms [PN_RK] None (mkFacts [] [] []).
(* The state at +0x214: the shadow byte of s + 80 at s11 (atom 27) and that of s + 64 at s5 (atom 21), each 0;
   io.ctx at s8 = s + 64 (atom 24) and io.recv at s6 = s + 80 (atom 22), valued by the atoms 32 and 33. *)
Definition PN_R80 : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition PN_R64 : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition PN_RCTX : YP09.region := YP09.mkRegion (Some 24%nat) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 32 0))].
Definition PN_RRCV : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 33 0))].
Definition ss_pn3 : sstate := mkSS PN_J sr_atoms [PN_R80; PN_R64; PN_RCTX; PN_RRCV] None (mkFacts [] [] []).
Definition PN_Bx : sv := SLit 0.
Definition PN_B0 : Z * Z := (0, 0).

(* The registers pw_rg_run names, all callee-saved. *)
Definition PN_KREGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 27]%bv.

(* The shadow addresses of s + 64 and s + 80. *)
Lemma pn_sh_vals : PW_SH64 = FCells.shadow_addr (POLL_S + 64) /\ PW_SH80 = FCells.shadow_addr (POLL_S + 80) /\
  PW_SH64 = 2148220624 /\ PW_SH80 = 2148220626.
Proof. repeat split; reflexivity. Qed.

(* The world fields the piece reads, at their numeral offsets. *)
Lemma pn_fields : forall Bw, TW.S_io_ctx Bw = TW.u_at Bw (TW.OFF_g_s + 64) 8 /\
  TW.S_io_recv Bw = TW.u_at Bw (TW.OFF_g_s + 80) 8 /\ TC.io_now_m Bw = TW.u_at Bw TW.OFF_g_now 8.
Proof. intros Bw. repeat split; reflexivity. Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac pn_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Register r holds the atom of register rs (number n) at the run's start, whose value Q states (EE: the valuation's
   registers). *)
Ltac pn_kreg HS EE r n rs Q H :=
  lazymatch type of Q with _ = ?v =>
    pn_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EE n rs eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The goal forall r, In r [..] -> getr (ms_regs ms) r = getr rg r, for registers the run left as their atoms. *)
Ltac pn_atoms_kept HS EE rg :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- YK11.getr _ ?rr = _ =>
        let n := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
        let Hq := fresh "Hq" in
        pn_reg HS rr (YK11.getr rg rr) Hq
          ltac:(cbn [sv_denot]; rewrite (EE n rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
        exact Hq end |]);
  destruct Hr.
(* The awr obligation's regions, computed. *)
Ltac pn_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The awr obligation of a run whose regions are all read-only. *)
Ltac pn_awr_ro :=
  pn_awr_rs;
  repeat (apply awr_ok_x_cons;
    [let a := fresh "a" in let Ha := fresh "Ha" in
     intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* After a run that stores no byte (HFr: its frame), every byte of the view in [0, 2 ^ 64) is the one at m0 (KD) and
   presence grows (GR); msF names the machine state the run ended in. *)
Ltac pn_after_run HS W KD GR m0 msF :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) => rename mf into msF
  end;
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m0 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      apply (YC4b.kept_of_frame E rs (w_H W) m0 (ms_mem msF) (fun _ => False) HFx); [ | exact Ha | tauto];
      let b := fresh "b" in let wl := fresh "wl" in let wh := fresh "wh" in let x := fresh "x" in
      let Hin := fresh "Hin" in let Hx := fresh "Hx" in
      intros b wl wh x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]); destruct Hin end
  | ];
  assert (GR : forall a, apresent (w_H W) m0 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A state with no region at offset pc, the registers as atoms. *)
Lemma pn_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof using All.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* TRANS_K_POLL is a byte range trans_rom_view_rd reads as the image's. *)
Lemma pn_kpoll_ro : forall k, 0 <= k < 8 -> trans_in_ro_rd (TRANS_K_POLL + k).
Proof using All.
  intros k Hk. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_K_POLL, 8). split.
  - unfold TRANS_RO_RD. apply in_or_app. left. do 5 right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.

(* The state at +0x1d8: the constant at TRANS_K_POLL, read through trans_rom_view_rd. *)
Lemma pn_entry2 : forall (W : world segs) regs mem,
  trans_rom_view_rd W mem ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_pn2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PN_C2)) mem (YK11.seg_rom segs))).
Proof using All.
  intros W regs mem HROM. rewrite restrict_mkst_fx. unfold ss_pn2.
  set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
  assert (V91 : VAL (A_OBJ 91) = TRANS_K_POLL) by (vm_compute; reflexivity).
  assert (UK : base_val E (Some (A_OBJ 91)) = TRANS_K_POLL).
  { cbn [base_val]. unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite unsigned_lit_small; [exact V91 | rewrite V91; unfold TRANS_K_POLL; lia]. }
  assert (HK : rdword (aview segs (w_H W) mem) TRANS_K_POLL = Some PN_KPOLL).
  { rewrite (rdword_ext (fun a => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a)))
      (aview segs (w_H W) mem) TRANS_K_POLL).
    - vm_compute. reflexivity.
    - intros k Hk. exact (HROM _ (pn_kpoll_ro k Hk)). }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [PN_RK YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite UK.
    split; [unfold TRANS_K_POLL; lia|]. split; [unfold TRANS_K_POLL; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TRANS_K_POLL 0 8 (SLit PN_KPOLL) PN_KPOLL);
      [reflexivity | unfold PN_KPOLL; zside | zside |].
    rewrite Z.add_0_r. exact (YE2y.val_mem_of_rdword (w_H W) mem TRANS_K_POLL PN_KPOLL HK).
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* g_s's shadow bytes are 0 at every AR state (trans_poll_cells), at the granule of s + off. *)
Lemma pn_zsh : forall ly S (W : world segs) mem md off,
  trans_poll_cells B -> @AR rc segs B ly S W mem md -> off mod 8 = 0 -> 0 <= off -> off + 8 <= TW.SZ_g_s ->
  aview segs (w_H W) mem (FCells.shadow_addr (POLL_S + off)) = Some 0.
Proof using All.
  intros ly S W mem md off HPC HAR Hm Hlo Hhi.
  apply (decode_zshadow_rd B ly S W mem md POLL_S (POLL_S + TW.SZ_g_s) (POLL_S + off) HAR); [| lia | lia | exact HPC].
  unfold POLL_S, TB_g_s. rewrite Z.add_mod, Hm by lia. reflexivity.
Qed.

(* The valuation at +0x214: the registers, then io.ctx and io.recv of the world. *)
Definition pn_E3 (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.S_io_ctx Bw); Z_to_bv 64 (TW.S_io_recv Bw)]).

(* The state at +0x214: the two shadow bytes the checks read, io.ctx and io.recv. *)
Lemma pn_entry3 : forall ly S (W : world segs) regs mem md Bw,
  trans_poll_cells B -> @AR rc segs B ly S W mem md -> tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 27 = w64 PW_SH80 -> YK11.getr regs 21 = w64 PW_SH64 ->
  YK11.getr regs 24 = w64 (POLL_S + 64) -> YK11.getr regs 22 = w64 (POLL_S + 80) ->
  st_ok_pi segs VAL (pn_E3 regs Bw) ss_pn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PN_J)) mem (YK11.seg_rom segs))).
Proof using All.
  intros ly S W regs mem md Bw HPC HAR Htw R27 R21 R24 R22.
  destruct pn_sh_vals as (V64 & V80 & N64 & N80).
  destruct (pn_fields Bw) as (FC & FR & _).
  assert (CS : POLL_S = 6157888) by reflexivity.
  rewrite restrict_mkst_fx. unfold ss_pn3.
  set (E := pn_E3 regs Bw).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, pn_E3; apply can_ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 (TW.S_io_ctx Bw); Z_to_bv 64 (TW.S_io_recv Bw)]
    (Z_to_bv 64 0))
    by (intros j Hj; unfold E, pn_E3; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth] in E32, E33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 64) 8) as RC.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 80) 8) as RR.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RC, RR. rewrite <- FC in RC. rewrite <- FR in RR.
  assert (U27 : bv_unsigned (ew E 27) = PW_SH80)
    by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; rewrite N80; lia).
  assert (U21 : bv_unsigned (ew E 21) = PW_SH64)
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; rewrite N64; lia).
  assert (U24 : bv_unsigned (ew E 24) = POLL_S + 64)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; rewrite CS; lia).
  assert (U22 : bv_unsigned (ew E 22) = POLL_S + 80)
    by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; rewrite CS; lia).
  assert (Z80 : aview segs (w_H W) mem PW_SH80 = Some 0)
    by (rewrite V80; apply (pn_zsh ly S W mem md 80 HPC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia]).
  assert (Z64 : aview segs (w_H W) mem PW_SH64 = Some 0)
    by (rewrite V64; apply (pn_zsh ly S W mem md 64 HPC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia]).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [PN_R80 PN_R64 PN_RCTX PN_RRCV YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U27, ?U21, ?U24, ?U22.
    + split; [rewrite N80; lia|]. split; [rewrite N80; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ PW_SH80 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. apply YE2y.val_mem1_of_aview. exact Z80.
    + split; [rewrite N64; lia|]. split; [rewrite N64; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ PW_SH64 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. apply YE2y.val_mem1_of_aview. exact Z64.
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (POLL_S + 64) 0 8 (SOff 32 0) (TW.S_io_ctx Bw));
        [cbn [sv_denot]; rewrite E32, (unsigned_lit_small _ RC), Z.add_0_r; reflexivity | exact RC | zside |].
      rewrite Z.add_0_r, FC.
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 64 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (POLL_S + 80) 0 8 (SOff 33 0) (TW.S_io_recv Bw));
        [cbn [sv_denot]; rewrite E33, (unsigned_lit_small _ RR), Z.add_0_r; reflexivity | exact RR | zside |].
      rewrite Z.add_0_r, FR.
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 80 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, PN_R80, PN_R64, PN_RCTX, PN_RRCV. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U27, U21, U24, U22. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite N80, N64, CS. repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* pw_rg_run at a register file that agrees with one of pw_rg_run on the callee-saved registers it names. *)
Lemma pn_rg_run_kept : forall c pos (regsA regsB : bvmap 5 word),
  pw_rg_run B c pos regsA -> (forall r : bv 5, In r PN_KREGS -> YK11.getr regsB r = YK11.getr regsA r) ->
  pw_rg_run B c pos regsB.
Proof using All.
  intros c pos regsA regsB ((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27) HK.
  unfold PN_KREGS in HK. unfold pw_rg_run, pw_rg_base.
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ _))))) (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ _)))))));
  (rewrite HK; [| cbn [In]; repeat (first [left; reflexivity | right])]).
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R8.
  - exact R9.
  - exact R18.
  - exact R19.
  - exact R20.
  - exact R21.
  - exact R22.
  - exact R23.
  - exact R24.
  - exact R27.
Qed.

(* aregs_preserved on the registers pw_rg_run names. *)
Lemma pn_kregs_preserved : forall (regsA regsB : bvmap 5 word),
  aregs_preserved regsA regsB -> forall r : bv 5, In r PN_KREGS -> YK11.getr regsB r = YK11.getr regsA r.
Proof using All.
  intros regsA regsB HP r Hr. unfold PN_KREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- YK11.getr _ ?rr = _ =>
        let n := eval vm_compute in (bv_unsigned rr) in
        change (YK11.getr regsB (Z_to_bv 5 n) = YK11.getr regsA (Z_to_bv 5 n));
        exact (HP n ltac:(unfold acallee_saved; lia)) end |]).
  destruct Hr.
Qed.

(* From the join +0x214: the checks of s + 80 and s + 64, a0 = io.ctx, a4 = io.recv, s9 = buf, a2 = 1514, a1 = buf,
   to the cut recv1 (+0x23c). The wait's register a3 is not read. *)
Lemma pn_j214 : forall c, pw_recv1_at B MT c ->
  forall pos ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) B1 r1 got,
  pw_rt B MT -> pw_keep -> pw_ok B c ->
  pw_run B MT c pos ly2 S2 W2 mem2 md2 (cx_Bw c) -> pw_rg_run B c pos regs2 ->
  TW.S_io_recv (cx_Bw c) = TI.ti_io_recv timg_B ->
  TC.io_recv_m timg_B (cx_TF c) (cx_Bw c) TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) ->
  pw_rest1 timg_B (cx_TF c) B1 r1 got (cx_Bw' c) (cx_r c) ->
  SRr segs W2 (@cfg_at fx segs (BASE + PN_J) regs2 mem2 md2) (pw_post B MT c).
Proof using All.
intros c REC pos ly2 S2 W2 mem2 md2 regs2 B1 r1 got HRT HKP HOK HRUN HRG HRI HM HREST.
pose proof HRT as (_ & _ & HPC & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _).
pose proof HRUN as ((HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htw & _) & _).
pose proof HRG as ((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (pw_cur_frame B MT c pos ly2 S2 W2 mem2 md2 (cx_Bw c) HRT HOK (proj1 HRUN))
  as (_ & _ & _ & _ & _ & _ & HF0 & _ & HFc & _).
pose proof (pw_ok_sp B) as SPK. try specialize (SPK MT).
destruct (SPK c HOK) as (_ & Hsp & Hceil & _). clear SPK.
assert (PS : 0 <= POLL_STK)
  by (assert (V : POLL_STK = ltac:(let v := eval vm_compute in POLL_STK in exact v)) by reflexivity; rewrite V; lia).
assert (HFr : 0 <= pw_F c pos /\ pw_F c pos + 32 < 2 ^ 64) by (unfold POLL_FBYTES in HFc; lia).
destruct (pn_fields (cx_Bw c)) as (_ & FR & _).
assert (RR : 0 <= TW.S_io_recv (cx_Bw c) < 2 ^ 64).
{ rewrite FR. pose proof (TWL.u_at_range (cx_Bw c) (TW.OFF_g_s + 80) 8) as R.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R. exact R. }
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (pn_entry3 ly2 S2 W2 regs2 mem2 md2 (cx_Bw c) HPC HAR Htw R27 R21 R24 R22) as HS.
set (E := pn_E3 regs2 (cx_Bw c)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, pn_E3; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E, pn_E3; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 (TW.S_io_recv (cx_Bw c)))
  by (unfold E, pn_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (SHOK : sh_ok segs PN_Bx (@nil shent) E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PN_J)) mem2 (YK11.seg_rom segs)) md2) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK PN_B0 PW_RECV1.
{ pn_awr_ro. }
pn_after_run HS W2 KD GR mem2 msF.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ _ _ _) ?mdx) _ => set (mdF := mdx) in * end.
pn_reg HS (11%bv : bv 5) (w64 (pw_F c pos + 32)) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; rewrite unsigned_lit_small by lia;
        reflexivity).
pn_reg HS (25%bv : bv 5) (w64 (pw_F c pos + 32)) Q25
  ltac:(cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; rewrite unsigned_lit_small by lia;
        reflexivity).
pn_reg HS (12%bv : bv 5) (w64 TS0.DIGINET_MAX_FRAME_LEN) Q12 ltac:(reflexivity).
pn_reg HS (14%bv : bv 5) (w64 (TI.ti_io_recv timg_B)) Q14
  ltac:(cbn [sv_denot]; rewrite E33, (unsigned_lit_small _ RR), Z.add_0_r, HRI; reflexivity).
assert (HKF : forall r : bv 5, In r PN_KREGS -> YK11.getr (ms_regs msF) r = YK11.getr regs2 r)
  by (unfold PN_KREGS; pn_atoms_kept HS EE regs2).
pose proof (pw_run_win B MT c pos ly2 S2 W2 mem2 md2 (cx_Bw c) (ms_mem msF) mdF HRT HOK HRUN HJ
  ltac:(intros a Ha _; exact (KD a Ha)) GR) as HRUNF.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (BASE + PW_RECV1) rg mm mdx) Q) end.
exact (REC HRT HKP HOK pos ly2 S2 W2 (ms_mem msF) mdF (ms_regs msF) B1 r1 got HRUNF
  (conj (pn_rg_run_kept c pos regs2 (ms_regs msF) HRG HKF) Q25) Q11 Q12 Q14 HRI HM HREST).
Qed.

(* The paths of the wait (+0x1d8 .. +0x210), each to the join +0x214: at a branch, its two arms, each run to the
   next stop with pw_run carried to the run's memory (pw_run_win: nothing is stored); at the join, LEAF with the
   pw_run of that memory and the registers pw_rg_run names, which no run of the wait writes (EE, rg: the valuation of
   the paths' first state). *)
Ltac pn_tree RUN RUNTO BR HS SHOK HJ HRT HOK EE rg LEAF W :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?ms0) =>
  let m0 := eval cbn [ms_mem YK11.mkst] in (ms_mem ms0) in
  let b := eval vm_compute in (ss_pc ss =? PN_J) in
  lazymatch b with
  | true =>
      pmkst HS;
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst ?fxx ?rgx _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (@cfg_at fxx sg (BASE + PN_J) rgx mm mdx) Q) end;
      apply LEAF;
      [ lazymatch goal with HR : pw_run _ _ _ _ _ _ _ m0 _ _ |- _ => exact HR end
      | unfold PN_KREGS; pn_atoms_kept HS EE rg ]
  | false =>
      psrr_branch_tok RUN BR HS SHOK PN_B0;
      (paj_run_to_tok RUNTO HS HJ SHOK PN_B0 PN_J;
       [ pn_awr_ro
       | let msF := fresh "msF" in let KD := fresh "KD" in let GR := fresh "GR" in
         pn_after_run HS W KD GR m0 msF;
         lazymatch goal with HR : pw_run ?Bq ?MTq ?c ?pos ?ly ?S ?Wr m0 ?md ?Bx |- _ =>
           let HR' := fresh "HRUN" in
           pose proof (pw_run_win Bq MTq c pos ly S Wr m0 md Bx _ _ HRT HOK HR HJ
             ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha _; exact (KD a Ha)) GR) as HR';
           clear KD GR end;
         pn_tree RUN RUNTO BR HS SHOK HJ HRT HOK EE rg LEAF W ])
  end end.

Lemma pw_now1_holds : @pw_now1_stmt fx rc B MT.
Proof using All.
unfold pw_now1_stmt. intros c REC. unfold pw_now1_at.
intros HRT HKP HOK pos ly2 S2 W2 mem2 md2 regs2 HRUN HRG R25 R11 HRZ HNZ.
pose proof HRT as (_ & _ & HPC & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _).
pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _).
destruct (pw_m_go _ _ _ _ _ _ Hm HRZ HNZ) as (HNI & HRI & due & B1 & r1 & got & HDL & HM & HREST).
pose proof HRUN as ((HJ & _) & _).
pose proof HRG as ((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* +0x1c4: `jalr a1`, a1 = io.now_us = io_now *)
pose proof (pn_entry0 W2 regs2 mem2 PW_NOW1) as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (TN : TI.ti_io_now timg_B = 0x83410) by reflexivity.
assert (R11' : YK11.getr regs2 11 = Z_to_bv 64 (TI.ti_io_now timg_B)) by (rewrite R11, HNI; reflexivity).
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PW_NOW1)) mem2 (YK11.seg_rom segs)) md2) Q) end.
eapply (SRr_jalr_call_pi (PL := PL_transportb) (PI := PI_transportb) W2 E0 _ _ _ _ 0x580e7 (1%bv : bv 5) (11%bv : bv 5)
  (TI.ti_io_now timg_B) HEI HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; unfold PW_NOW1, AF_diginet_session_poll; lia
  | exact R11' | rewrite TN; lia | rewrite TN; reflexivity |].
intros matC ms1 Ems1 _. subst ms1.
set (regsC := YK11.regupd (ms_regs (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PW_NOW1)) mem2 (YK11.seg_rom segs)))
  (1%bv : bv 5) (Z_to_bv 64 (BASE + (ss_pc (mkSS PW_NOW1 sr_atoms [] None (mkFacts [] [] [])) + 4)))).
set (mdC := with_vm_backing (m_vm_lazy md2) matC md2).
change (SRr segs W2 (@cfg_at fx segs (TI.ti_io_now timg_B) regsC mem2 mdC) (pw_post B MT c)).
assert (RC1 : YK11.getr regsC 1 = Z_to_bv 64 (BASE + 39360))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr regs2 r)
  by (intros r Hr; unfold regsC; apply YK11.getr_other; intros Er; apply Hr; rewrite Er; reflexivity).
assert (RC2 : YK11.getr regsC 2 = w64 (pw_sp1 c)) by (rewrite RCK by (vm_compute; discriminate); exact R2).
assert (RC3 : YK11.getr regsC 3 = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact R3).
assert (RC4 : YK11.getr regsC 4 = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact R4).
assert (EB1 : BASE + 39360 = 0x8ac60) by (vm_compute; reflexivity).
pose proof (pw_run_win B MT c pos ly2 S2 W2 mem2 md2 (cx_Bw c) mem2 mdC HRT HOK HRUN
  ltac:(unfold mdC; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ)
  ltac:(intros a _ _; reflexivity) ltac:(intros a Ha; exact Ha)) as HRUNC.
eapply SRr_bind.
{ exact (pw_now_call B MT c pos ly2 S2 W2 mem2 mdC (cx_Bw c) regsC HRT HOK HRUNC RC2 RC3 RC4
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EB1; rewrite unsigned_lit_small by lia; lia)). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HP3 & H10n & HRUN3 & _ & _).
rewrite RC1.
(* +0x1c8 .. +0x1d4: s10 = now, a0 = s, a1 = now, `jal diginet_session_deadline` *)
assert (HK3 : forall r : bv 5, In r PN_KREGS -> YK11.getr regs3 r = YK11.getr regsC r)
  by exact (pn_kregs_preserved _ _ HP3).
assert (HK3' : forall r : bv 5, In r PN_KREGS -> YK11.getr regs3 r = YK11.getr regs2 r).
{ intros r Hr. rewrite (HK3 r Hr). apply RCK. unfold PN_KREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [vm_compute; discriminate |]). destruct Hr. }
pose proof (pn_rg_run_kept c pos regs2 regs3 HRG HK3') as HRG3.
pose proof HRG3 as ((T2 & T3 & T4 & T8 & T9 & T18) & T19 & T20 & T21 & T22 & T23 & T24 & T27).
clear HS.
pose proof (pn_entry0 W2 regs3 mem3 PN_C1) as HS.
set (E1 := Eimg (PI := PI_transportb) (Ereg regs3 [])) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E1; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK1 : sh_ok segs PN_Bx (@nil shent) E1 (mrestrict (w_H W2) mem3)) by constructor.
pose proof HRUN3 as ((HJ3 & _) & _).
change (Z_to_bv 64 (BASE + 39360)) with (Z_to_bv 64 (BASE + PN_C1)).
paj_run_tok RUN HS HJ3 SHOK1 PN_B0.
{ pn_awr_rs. apply awr_ok_x_nil. }
pn_after_run HS W2 KD4 GR4 mem3 ms4.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ _ _ _) ?mdx) _ => set (md4 := mdx) in * end.
pn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 39376)) Q1 ltac:(apply codeptr_val; exact HEI1).
pn_kreg HS EE1 (10%bv : bv 5) 19%nat (19%bv : bv 5) T19 Q10.
pn_kreg HS EE1 (11%bv : bv 5) 10%nat (10%bv : bv 5) H10n Q11.
pn_kreg HS EE1 (2%bv : bv 5) 2%nat (2%bv : bv 5) T2 Q2.
pn_kreg HS EE1 (3%bv : bv 5) 3%nat (3%bv : bv 5) T3 Q3.
pn_kreg HS EE1 (4%bv : bv 5) 4%nat (4%bv : bv 5) T4 Q4.
assert (HK4 : forall r : bv 5, In r PN_KREGS -> YK11.getr (ms_regs ms4) r = YK11.getr regs3 r)
  by (unfold PN_KREGS; pn_atoms_kept HS EE1 regs3).
pose proof (pw_run_win B MT c pos ly2 S2 W2 mem3 md3 (cx_Bw c) (ms_mem ms4) md4 HRT HOK HRUN3 HJ3
  ltac:(intros a Ha _; exact (KD4 a Ha)) GR4) as HRUN4.
assert (EB2 : BASE + 39376 = 0x8ac70) by (vm_compute; reflexivity).
assert (Hnow : 0 <= TC.io_now_m (cx_Bw c) < 2 ^ 64).
{ destruct (pn_fields (cx_Bw c)) as (_ & _ & FN). rewrite FN.
  pose proof (TWL.u_at_range (cx_Bw c) TW.OFF_g_now 8) as R. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R.
  exact R. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_diginet_session_deadline) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (pw_deadline_call B MT c pos ly2 S2 W2 (ms_mem ms4) md4 (cx_Bw c) (ms_regs ms4) (TC.io_now_m (cx_Bw c)) due
    HRT HOK HRUN4 Q2 Q3 Q4
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EB2; rewrite unsigned_lit_small by lia; lia)
    Q10 Q11 Hnow HDL). }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HP5 & H10d & HRUN5 & _ & _).
rewrite Q1.
(* +0x1d8 .. +0x210: the wait, every path to the join +0x214 *)
assert (HK5 : forall r : bv 5, In r PN_KREGS -> YK11.getr regs5 r = YK11.getr regs2 r)
  by (intros r Hr; rewrite (pn_kregs_preserved _ _ HP5 r Hr), (HK4 r Hr); exact (HK3' r Hr)).
pose proof (pn_rg_run_kept c pos regs2 regs5 HRG HK5) as HRG5.
assert (LEAF : forall msF mdF, pw_run B MT c pos ly2 S2 W2 (ms_mem msF) mdF (cx_Bw c) ->
  (forall r : bv 5, In r PN_KREGS -> YK11.getr (ms_regs msF) r = YK11.getr regs5 r) ->
  SRr segs W2 (@cfg_at fx segs (BASE + PN_J) (ms_regs msF) (ms_mem msF) mdF) (pw_post B MT c)).
{ intros msF mdF HRF HKF.
  exact (pn_j214 c REC pos ly2 S2 W2 (ms_mem msF) mdF (ms_regs msF) B1 r1 got HRT HKP HOK HRF
    (pn_rg_run_kept c pos regs5 (ms_regs msF) HRG5 HKF) HRI HM HREST). }
clear HS SHOK1 HJ3 HRUN HRUNC HRUN3 HRUN4 HJ.
pose proof HRUN5 as ((HJ5 & _) & _).
pose proof (pn_entry2 W2 regs5 mem5 (pw_rom_at B MT c pos ly2 S2 W2 mem5 md5 (cx_Bw c) HRT HOK (proj1 HRUN5)))
  as HS.
set (E5 := Eimg (PI := PI_transportb) (Ereg regs5 [])) in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (unfold E5; apply Eimg_env).
assert (EE5 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E5 n = YK11.getr regs5 r)
  by (intros n r Hn; unfold E5; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK5 : sh_ok segs PN_Bx (@nil shent) E5 (mrestrict (w_H W2) mem5)) by constructor.
change (Z_to_bv 64 (BASE + 39376)) with (Z_to_bv 64 (BASE + PN_C2)).
pn_tree RUN RUNTO BR HS SHOK5 HJ5 HRT HOK EE5 regs5 LEAF W2.
Qed.

End s.

Theorem pw_now1_piece : forall fx rc B MT, @pw_now1_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pw_now1_holds fx rc B MT). Qed.
