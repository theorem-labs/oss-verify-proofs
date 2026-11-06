(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 613 of its 658 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/SlotPass9G.v, with its module paths, module names, addresses and numbers changed; 521 of its 718 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass1.v, with its module names changed; 287 of its 331 lines of code are new or changed and 674 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass2.v, with its module paths and addresses changed; 1518 of its 1667 lines of code are new or changed and 182 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass2.v, with its module paths changed; 1758 of its 1943 lines of code are new or changed and 1482 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame SlotReads SlotEntryRun SlotEntry.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotHeadQD SlotPass1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c pthread_mutex_lock_ro_c pthread_mutex_unlock_ro_c pthread_mutex_lock_ro pthread_mutex_unlock_ro.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass9G SlotPass2Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_no_loss_read_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import check_no_loss_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass2Check SlotPass2Aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require RelayCap relay_remove_b_aux SlotPass4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotMove SlotWalk SlotPass2Mv SlotPass2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require SlotRI3 SlotNcWt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Cells.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p2d_di : forall e e1 h NO CAP, p2_sbs e e1 -> drain_init NO CAP e1 h = drain_init NO CAP e h.
Proof.
  intros e e1 h NO CAP SB1.
  pose proof SB1 as (SF1 & SE1 & SS1 & SP1 & SBU1 & SU1 & SC1' & SH1 & SKH1 & SP2 & SK1 & SUU1 & SJ1).
  unfold drain_init, ent_ka. rewrite SC1', SUU1, SS1, SH1, SKH1, (p2_sbs_texts e e1 SB1). reflexivity.
Qed.

Lemma p2d_dsa : forall e e1 h kf o, p2_sbs e e1 -> drain_start kf o e1 h = drain_start kf o e h.
Proof.
  intros e e1 h kf o SB1.
  pose proof SB1 as (SF1 & SE1 & SS1 & SP1 & SBU1 & SU1 & SC1' & SH1 & SKH1 & SP2 & SK1 & SUU1 & SJ1).
  assert (MKA : map (fun k => kf (key_addr k)) (re_keys e1) = map (fun k => kf (key_addr k)) (re_keys e)).
  { pose proof (f_equal (map (fun x : Z * list byte => kf (fst x))) SK1) as X. rewrite !map_map in X. exact X. }
  unfold drain_start. rewrite SBU1, SH1, MKA. reflexivity.
Qed.

Lemma p2d_dtr : forall e e1 h kf o lv mx NO CAP, p2_sbs e e1 ->
  drain_tr lv mx NO CAP e1 h 0 (drain_start kf o e1 h) = drain_tr lv mx NO CAP e h 0 (drain_start kf o e h).
Proof.
  intros e e1 h kf o lv mx NO CAP SB1. unfold drain_tr, drain_go.
  rewrite (p2d_di e e1 h NO CAP SB1), (p2d_dsa e e1 h kf o SB1). reflexivity.
Qed.

Lemma p2d_dfn : forall e e1 h lv mx NO CAP, p2_sbs e e1 ->
  drain_fin lv mx NO CAP e1 h = drain_fin lv mx NO CAP e h.
Proof.
  intros e e1 h lv mx NO CAP SB1. unfold drain_fin, drain_go. rewrite (p2d_di e e1 h NO CAP SB1). reflexivity.
Qed.

Lemma p2d_dfa : forall e e1 h kf o lv mx NO CAP, p2_sbs e e1 ->
  drain_adr lv mx NO CAP e1 h 0 (drain_start kf o e1 h) = drain_adr lv mx NO CAP e h 0 (drain_start kf o e h).
Proof.
  intros e e1 h kf o lv mx NO CAP SB1. unfold drain_adr, drain_go.
  rewrite (p2d_di e e1 h NO CAP SB1), (p2d_dsa e e1 h kf o SB1). reflexivity.
Qed.

Ltac ugs := unfold HarnessRep.G_S, Statement.G_S, CF.drain_b_c.G_S, CF.source_reset_c.G_S, CF.gesture_model_c.G_S.
Ltac ugs_in H := unfold HarnessRep.G_S, Statement.G_S, CF.drain_b_c.G_S, CF.source_reset_c.G_S, CF.gesture_model_c.G_S in H.

Ltac ugl := unfold CF.relay_finish_b_c.G_THREAD_UP, Statement.G_THREAD_UP, CF.SlotInv.G_WAKE0, CheckRep.G_GONE,
  CF.check_no_loss_c.G_GONE, send_line_c.G_DEAD, CF.relay_add_b_c.G_NSRC, Statement.G_NSRC, check_bounded_c.G_NSRC,
  CF.op_add_c.G_NFD, CF.relay_add_b_c.G_SRC, check_bounded_c.G_SRC, CF.StatementKept.G_SRC, relay_event_c.G_LOCK,
  Statement.G_LOCK, send_line_c.G_BROKEN, send_line_c.G_EINTR, send_line_c.G_OUTV, CF.relay_finish_b_c.G_LISTEN,
  send_line_c.G_CLIENT, send_line_c.G_RELAY_LO, CF.StatementKept.G_NOUT, CF.StatementKept.G_OUT, check_shape_done_c.G_NOUT,
  relay_event_c.G_LOCK_HI, SRC_SIZE, SOURCES_MAX.
Ltac ugl_in H := unfold CF.relay_finish_b_c.G_THREAD_UP, Statement.G_THREAD_UP, CF.SlotInv.G_WAKE0, CheckRep.G_GONE,
  CF.check_no_loss_c.G_GONE, send_line_c.G_DEAD, CF.relay_add_b_c.G_NSRC, Statement.G_NSRC, check_bounded_c.G_NSRC,
  CF.op_add_c.G_NFD, CF.relay_add_b_c.G_SRC, check_bounded_c.G_SRC, CF.StatementKept.G_SRC, relay_event_c.G_LOCK,
  Statement.G_LOCK, send_line_c.G_BROKEN, send_line_c.G_EINTR, send_line_c.G_OUTV, CF.relay_finish_b_c.G_LISTEN,
  send_line_c.G_CLIENT, send_line_c.G_RELAY_LO, CF.StatementKept.G_NOUT, CF.StatementKept.G_OUT, check_shape_done_c.G_NOUT,
  relay_event_c.G_LOCK_HI, SRC_SIZE, SOURCES_MAX in H.

Ltac p2d_g :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn in Hk; ugl; ugs;
  split; [first [apply in_G_bss; clear - Hk; lia|apply g9_in_listen; clear - Hk; lia]|repeat split; lia2].

Ltac p2d_ch X5 PRc Q k :=
  etransitivity; [apply (getr_of_eqv _ _ _ X5); reflexivity|];
  etransitivity; [exact (PRc k (p2_cs k eq_refl))|]; exact Q.

Ltac p2d_q X3 PRd D k :=
  etransitivity; [apply (getr_of_eqv _ _ _ X3); reflexivity|]; exact (eq_trans (PRd k (p2_cs k eq_refl)) D).

Section P2D.
Variables (F : ResFormT) (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (rc : RunCeil) (fx : FPState) (j : nat) (E : sstart) (CS : list byte -> list Z)
  (RI : res_inv) (t K : Z).
Variables (fx' : FPState) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
  (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat))
  (i : nat) (e : rentry) (h : hsrc) (jj : nat) (R : bvmap 5 word) (m1 : word -> option byte).
Hypothesis HF : slot_frame B API LS SH SK ra empty rc fx j E CS.
Hypothesis HCB : check_bounded_contract.
Hypothesis ULK : pthread_mutex_unlock_contract.
Hypothesis DRN : forall fx'', @drain_contract fx'' rc B (API rc) F.
Hypothesis CNR : check_no_loss_read_contract.
Hypothesis CNL : forall fx'', @check_no_loss_contract fx'' rc B (API rc) F.
Hypothesis CSD : check_shape_done_contract.
Hypothesis DRES : p2_drain_res_s F RI.
Hypothesis CRES : p2_cnl_res_s F RI.
Hypothesis HWK : walk_at (ss_pl E) (t + 1) K.
Hypothesis FZ : frm_zero (@fp_csr fx').
Hypothesis Ht : 0 <= t < OPS_MAX.
Hypothesis Hk : 0 <= K <= ss_n E.
Hypothesis Hn : ss_n E < INPUT_MAX.
Hypothesis HMR : aa_MR (API rc) L A mem md.
Hypothesis HWF : WF A.
Hypothesis HBD : bounded A.
Hypothesis HINIT : st_init_done A = true.
Hypothesis HVM : exists vm, md = with_vmmaps vm (ss_md E).
Hypothesis HRO : ro_agree (ms_segs B) mem.
Hypothesis HIK : image_kept (rc := rc) B E mem.
Hypothesis HST : stack_mid B E mem.
Hypothesis HDK : driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem.
Hypothesis HGL : globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out.
Hypothesis Hnfd : 0 <= nfd <= t + 1.
Hypothesis HOUT : output_at (rc := rc) B L A mem nout cap out.
Hypothesis HREL : relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj.
Hypothesis Hes : (length es <= 4)%nat.
Hypothesis Hcost : slot_cost es hj <= K.
Hypothesis HRI : RI E K (view_of G (bv_unsigned out) es hj) L A.
Hypothesis HNO : bv_unsigned nout = 0.
Hypothesis Hi : nth_error es i = Some e.
Hypothesis Hh : nth_error hj i = Some (h, jj).
Hypothesis EOF : re_eof e = 0.
Hypothesis DR : p2_dregs E t K (G + 56 * Z.of_nat i) (G_S + SRC_SIZE * Z.of_nat jj) R.
Hypothesis MU1 : munch [(slot_sp E + 40, slot_sp E + 48); (0x318fc, 0x31900)] mem m1.
Hypothesis WM1 : wmono (ms_segs B) mem m1.
Hypothesis RO1 : ro_agree (ms_segs B) m1.
Hypothesis CK1 : rw_cells (ms_segs B) m1 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)].
Hypothesis C401 : rw_cells (ms_segs B) m1 (slot_sp E + 40) [C8 (Z_to_bv 64 0)].

Let SA := G + 56 * Z.of_nat i.
Let HA := G_S + SRC_SIZE * Z.of_nat jj.
Let Es0 := fun a => slot_sp E + 40 <= a < slot_sp E + 48 \/ 0x318fc <= a < 0x31900.
Let TA0 := bv_unsigned out :: G :: entry_blocks e ++ hs_blocks h.
Let TF0 := bv_unsigned out :: entry_blocks e ++ hs_blocks h.
Let Ls := lines (hs_state h) (bzs (pending_stream h)).
Let TOT := Z.of_nat (length (with_nul Ls)).
Let Ed := fun a => G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32 \/
    HA + 12 <= a < HA + SRC_SIZE \/ SA <= a < SA + SRC_ENTRY \/
    (exists v n, In (v, n) (blocks L A) /\ In v TF0 /\ v <= a < v + n).

Ltac p2d_base :=
  pose proof (pthread_mutex_unlock_ro_of ULK) as ULKR;
  destruct (p2_ff B API LS SH SK ra empty rc fx j E CS HF)
    as (SEG & ERR & ETP & FA & PL & SPLO & SPHI & ALIGN & TP & MR0 & PIN & NI);
  assert (AX : AllocExtra B (aa_MR (API rc))) by (clear - FA; unfold frame_allocator in FA; tauto);
  assert (BW : blocks_writable B (API rc)) by (clear - FA; unfold frame_allocator in FA; tauto);
  assert (NDB : blocks_nodup B (API rc)) by (clear - FA; unfold frame_allocator in FA; tauto);
  assert (GNO : forall L0 A0 m0 md0 a, aa_MR (API rc) L0 A0 m0 md0 -> in_globals frame_G a -> ~ owned B L0 A0 a)
    by (clear - FA; unfold frame_allocator in FA; tauto);
  pose proof (@YM05.alloc_ceiling_value rc) as (AC & ACmod);
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL;
  assert (EOFF : ms_errno_off B = -164) by (clear - ERR ETP; unfold errno_addr in ERR; lia);
  assert (SPB1 : @YM05.alloc_ceiling rc + 65344 <= slot_sp E)
    by (clear - SPLO; unfold slot_sp, SLOT_FRAME; unfold SLOT_STACK in SPLO; lia);
  assert (SPB2 : slot_sp E + 192 <= 2 ^ 63) by (clear - SPHI; unfold slot_sp, SLOT_FRAME; lia);
  assert (SPA : slot_sp E mod 16 = 0) by (clear - ALIGN; unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia);
  assert (HKc : @YM05.alloc_ceiling rc <= slot_sp E - (SLOT_STACK - SLOT_FRAME))
    by (clear - SPB1; unfold SLOT_STACK, SLOT_FRAME; lia);
  pose proof HREL as (TBL & GIN & GFR & HES & NDF & FDR & PA & NDH & ZH & NDA);
  let h0 := fresh "h0" in let jj0 := fresh "jj0" in let Hh0 := fresh "Hh0" in let PO := fresh "PO" in
  destruct (p2_f2_nth_l _ _ _ _ _ PA Hi) as ([h0 jj0] & Hh0 & PO); rewrite Hh in Hh0; injection Hh0 as <- <-;
  destruct PO as (SRC & JJ4 & FDH & EOFC & SSK & NDT & EXP0 & PN & PC & PS & EC & HC);
  cbn [fst snd] in SRC, JJ4, FDH, EOFC, SSK, NDT, EXP0, PN, PC, PS, EC, HC;
  destruct (EOFC EOF) as (SKO & WU);
  pose proof (p2_nth_forall _ _ _ _ HES Hi) as EOK;
  assert (GB : 4096 <= G /\ G + 896 <= @YM05.alloc_ceiling rc)
    by (clear - GFR; destruct GFR as (G0 & G1 & _); unfold SRC_TABLE, SRC_ENTRY in G1; lia);
  assert (IL : (i < length es)%nat) by (clear - Hi; apply nth_error_Some; rewrite Hi; discriminate);
  assert (IHJ : (i < length hj)%nat) by (clear - Hh; apply nth_error_Some; rewrite Hh; discriminate);
  assert (HAe : HA = 0x31920 + 96 * Z.of_nat jj) by reflexivity;
  assert (SAe : SA = G + 56 * Z.of_nat i) by reflexivity;
  assert (SSe : SRC_SIZE = 96) by reflexivity;
  assert (SEe : SRC_ENTRY = 56) by reflexivity;
  assert (HAB : 0x31920 <= HA /\ HA + 96 <= 0x31aa0) by (clear - JJ4 HAe; lia);
  assert (HA8 : HA mod 8 = 0)
    by (rewrite HAe; replace (0x31920 + 96 * Z.of_nat jj) with ((25380 + 12 * Z.of_nat jj) * 8) by lia;
        apply Z_mod_mult);
  pose proof DR as (D1 & D2 & D3 & D4 & D8 & D9 & D10 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27);
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GER & HCL & HBR & HGN &
    HDD & HEI & HGG & HMX);
  assert (HSA : bv_unsigned (YK11.getr R 10) = SA)
    by (rewrite D10; apply unsigned_lit; clear - GB IL Hes AC ACL SAe; lia);
  pose proof EOK as (EH1 & EH2 & EP1 & EP2 & EFD & ECAP & EUL & EU6 & EUZ & EBUF & ENH & EHP & END1 & END2 & EKS);
  assert (PCB : pair_cost e (h, jj) < 2 ^ 26)
    by exact (dc_cost B L A mem es hj e (h, jj) K (ss_n E) HES (p2_combine_nth es hj i e (h, jj) Hi Hh) Hcost
      (proj2 Hk) Hn);
  assert (PCK : pair_cost e (h, jj) <= K)
    by (eapply Z.le_trans; [|exact Hcost];
        apply (pair_cost_le_slot es hj e (h, jj) (p2_combine_nth es hj i e (h, jj) Hi Hh));
        eapply Forall_impl; [|exact HES]; intros e0 (_ & _ & _ & _ & _ & _ & U0 & _); lia);
  pose proof (bv_unsigned_in_range 64 mx) as MXR; pose proof (bv_unsigned_in_range 64 cap) as CPR;
  pose proof (bv_unsigned_in_range 64 out) as OUR; pose proof (bv_unsigned_in_range 64 nout) as NOR;
  change (bv_modulus 64) with (2 ^ 64) in MXR, CPR, OUR, NOR;
  pose proof (split_at es i e IL) as ESP; rewrite (nth_error_nth es i e Hi) in ESP;
  pose proof (split_at hj i (h, jj) IHJ) as HJP; rewrite (nth_error_nth hj i (h, jj) Hh) in HJP;
  pose proof (Forall2_firstn' _ i es hj PA) as PApre; pose proof (Forall2_skipn' _ (S i) es hj PA) as PApost;
  destruct (p2_forall_sub _ i es HES) as [ESpre _]; destruct (p2_forall_sub _ (S i) es HES) as [_ ESpost];
  assert (LHJ : length hj = length es) by (symmetry; exact (Forall2_length PA));
  pose proof (proj1 (NoDup_ListNoDup _) NDA) as NDAl;
  assert (NB0 : List.NoDup (map fst (blocks L A)))
    by (pose proof (NDB L A mem md HMR) as XN; first [exact XN|exact (proj1 (NoDup_ListNoDup _) XN)]);
  destruct (p2_nd_split _ _ _ _ (p2_nodup_sub G (bv_unsigned out) es hj i e h jj NDA Hi Hh))
    as (GO0 & GN0 & ON0 & NDE0 & NDH0 & DEH0).

Lemma b_R0 : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) Es0 (fun _ => False) L A mem md L A m1 md.
Proof.
  p2d_base.
  apply (rmid_A B (API rc) _ _ _ _ L A mem md m1 [(slot_sp E + 40, slot_sp E + 48); (0x318fc, 0x31900)] HMR HWF HBD
    (hg_img_low B SEG) HKc).
  - intros a Ha. destruct Ha as [Ha|Ha]; apply (proj2 (proj2 (proj2 HIK))); unfold lib_scratch;
      [left; clear - Ha SPB1; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|right; exact Ha].
  - exact MU1.
  - exact WM1.
  - intros x Hx HO. right. unfold Es0. cbn [outside] in HO. clear - HO. lia.
  - intros a HO. cbn [outside].
    pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO).
    split; [lia2|]. split; [|exact I].
    intros HX. exact (GNO _ _ _ _ a HMR (in_G_bss a ltac:(lia2)) HO).
  - intros p n k HP Hk0 HO. exfalso. apply HO.
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n k HMR HP Hk0) as (_ & _ & X & _).
    pose proof (ax_blocks_img AX L A mem md p n k HMR HP Hk0) as NIm. cbn [outside].
    split; [lia2|]. split; [|exact I].
    intros HX. apply NIm. exact (proj1 (PL _ (in_G_bss (ptr_addr L p + k) ltac:(lia2)))).
Qed.

Lemma b_KB : forall q, kept_block Es0 (fun _ => False) L A q.
Proof.
  p2d_base.
  intros q. split; [intros []|]. intros k a Hq Ha HE. unfold Es0 in HE.
  destruct (p2_blk rc fx B (API rc) L A mem md q k a FA HMR Hq Ha) as (NIm & _ & X2).
  destruct HE as [HE|HE]; [clear - HE X2 Ha SPB1; lia|].
  apply NIm. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(clear - HE; lia)))).
Qed.

Lemma b_SRC1 : src_at (rc := rc) B L A m1 HA h.
Proof.
  p2d_base. pose proof b_R0 as R0. pose proof b_KB as KB.
  apply (p2_src_rmid rc fx B (API rc) _ _ _ _ L A mem md L A m1 md HA h FA SEG HKc HMR R0 SRC); [|intros q _; apply KB].
  intros k Hk0. split; [apply PL; apply in_G_bss; clear - Hk0 HAB SSe; lia|].
  unfold Es0. clear - Hk0 HAB SPB1 AC SSe. lia.
Qed.

Lemma b_TW : forall a cs, rw_cells (ms_segs B) mem a cs ->
  disjoint_from [(slot_sp E + 40, slot_sp E + 48); (0x318fc, 0x31900)] a (Z.of_nat (cells_size cs)) ->
  rw_cells (ms_segs B) m1 a cs.
Proof. intros a cs H D. eapply rw_cells_transport; [exact H|exact MU1|exact WM1|exact D]. Qed.

Lemma b_EDB : forall a, Ed a -> in_img B a \/ (0 <= a < @YM05.alloc_ceiling rc /\ ~ in_img B a /\
    exists v n, In (v, n) (blocks L A) /\ In v TA0 /\ v <= a < v + n).
Proof.
  p2d_base.
  intros a [X|[X|[X|[X|[X|(v & n & Hv & Hvt & Ha)]]]]];
    try (left; apply (proj1 (PL a ltac:(apply in_G_bss; ugl_in X; clear - X HAB SSe; lia)))).
  - right.
    destruct (p2_blk rc fx B (API rc) L A mem md G 896 (a - G) FA HMR GIN ltac:(lia2)) as (NIa & B0 & B1).
    replace (G + (a - G)) with a in NIa by lia.
    split; [lia2|]. split; [exact NIa|]. exists G, 896. split; [exact GIN|]. split; [right; left; reflexivity|].
    lia2.
  - right. destruct (p2_blk rc fx B (API rc) L A mem md v n (a - v) FA HMR Hv ltac:(lia2)) as (NIa & B0 & B1).
    replace (v + (a - v)) with a in NIa by lia. split; [lia2|]. split; [exact NIa|]. exists v, n.
    split; [exact Hv|]. split; [|exact Ha]. destruct Hvt as [<-|Hvt]; [left; reflexivity|right; right; exact Hvt].
Qed.

Lemma b_EDI : forall a, Ed a -> in_img B a -> G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/
    G_OUTV + 8 <= a < G_OUTV + 32 \/ HA + 12 <= a < HA + SRC_SIZE.
Proof.
  p2d_base. pose proof b_EDB as EDB.
  intros a HE HI. destruct HE as [X|[X|[X|[X|HE]]]]; [left; exact X|right; left; exact X|right; right; left; exact X
    |right; right; right; exact X|].
  destruct (EDB a (or_intror (or_intror (or_intror (or_intror HE))))) as [_|(_ & NIa & _)]; [|contradiction].
  exfalso. destruct HE as [X|(v & n & Hv & _ & Ha)].
  - destruct (p2_blk rc fx B (API rc) L A mem md G 896 (a - G) FA HMR GIN ltac:(lia2)) as (NIa & _).
    replace (G + (a - G)) with a in NIa by lia. contradiction.
  - destruct (p2_blk rc fx B (API rc) L A mem md v n (a - v) FA HMR Hv ltac:(lia2)) as (NIa & _).
    replace (v + (a - v)) with a in NIa by lia. contradiction.
Qed.

Lemma b_EDH : forall a, Ed a -> a < @YM05.alloc_ceiling rc.
Proof.
  p2d_base. pose proof b_EDB as EDB.
  intros a HE. destruct (EDB a HE) as [HI|(X & _)]; [exact (proj2 (hg_img_low B SEG a HI))|lia2].
Qed.

Lemma b_NEDG : forall a, in_globals G_reply a -> ~ (G_BROKEN <= a < G_BROKEN + 1) -> ~ (G_EINTR <= a < G_EINTR + 1) ->
  ~ (G_OUTV + 8 <= a < G_OUTV + 32) -> ~ (HA + 12 <= a < HA + SRC_SIZE) -> ~ Ed a.
Proof.
  p2d_base. pose proof b_EDI as EDI.
  intros a HG N1 N2 N3 N4 HE. destruct (EDI a HE (proj1 (PL a HG))) as [X|[X|[X|X]]]; contradiction.
Qed.

Lemma b_NRO : RoAdapt.not_ro rsegs (slot_sp E - 96) 96.
Proof. p2d_base. intros k Hk1. unfold wa. apply ro_addr_hi. lia2. Qed.

Lemma b_OTX : forall x, In x (p2_oth es hj i) -> ~ In x TA0 /\ In x (target_addrs G (bv_unsigned out) es hj).
Proof.
  p2d_base.
  intros x Hx. destruct (p2_oth_out G (bv_unsigned out) es hj i e h jj x NDA Hi Hh Hx) as (N0 & I0).
  split; [|exact I0]. intros X. apply N0. destruct X as [<-|[<-|X]]; [right; left; reflexivity|left; reflexivity|].
  right; right; exact X.
Qed.

Lemma b_OTHP : forall x, In x (p2_oth es hj i) -> exists m, 0 < m /\ In (x, m) (blocks L A).
Proof.
  p2d_base.
  intros x Hx. unfold p2_oth in Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
  - apply in_concat in Hx. destruct Hx as (l0 & Hl & Hxl). apply in_map_iff in Hl. destruct Hl as (e0 & <- & He0).
    rewrite Forall_forall in ESpre. exact (p2_eb_pos rc B L A mem e0 (ESpre e0 He0) x Hxl).
  - apply in_app_or in Hx. destruct Hx as [Hx|Hx].
    + apply in_concat in Hx. destruct Hx as (l0 & Hl & Hxl). apply in_map_iff in Hl. destruct Hl as (e0 & <- & He0).
      rewrite Forall_forall in ESpost. exact (p2_eb_pos rc B L A mem e0 (ESpost e0 He0) x Hxl).
    + apply in_app_or in Hx. destruct Hx as [Hx|Hx].
      * apply in_concat in Hx. destruct Hx as (l0 & Hl & Hxl). apply in_map_iff in Hl. destruct Hl as (p & <- & Hp).
        destruct (pair_find _ _ _ _ _ p PApre Hp) as [e0 (S0 & _)]. cbv zeta in S0.
        exact (p2_hb_pos rc B L A mem _ (fst p) S0 x Hxl).
      * apply in_concat in Hx. destruct Hx as (l0 & Hl & Hxl). apply in_map_iff in Hl. destruct Hl as (p & <- & Hp).
        destruct (pair_find _ _ _ _ _ p PApost Hp) as [e0 (S0 & _)]. cbv zeta in S0.
        exact (p2_hb_pos rc B L A mem _ (fst p) S0 x Hxl).
Qed.

Lemma b_TA0S : forall v, In v TA0 -> In v (target_addrs G (bv_unsigned out) es hj).
Proof.
  intros v Hv. apply (p2_mid_in G (bv_unsigned out) es hj i e h jj v Hi Hh).
  destruct Hv as [<-|[<-|Hv]]; [right; left; reflexivity|left; reflexivity|right; right; exact Hv].
Qed.

Lemma b_GNT : ~ In G TF0.
Proof.
  destruct (p2_nd_split _ _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HREL)))))))))) as (GO & GNL & _).
  intros [EQ|X]; [exact (GO (eq_sym EQ))|]. apply GNL. apply in_app_or in X. destruct X as [X|X]; apply in_or_app.
  - left. apply in_concat. exists (entry_blocks e). split; [apply in_map; exact (nth_error_In es i Hi)|exact X].
  - right. apply in_concat. exists (hs_blocks h). split; [|exact X].
    exact (in_map (fun p => hs_blocks (fst p)) hj (h, jj) (nth_error_In hj i Hh)).
Qed.

Lemma b_NJ : forall p, In p (firstn i hj ++ skipn (S i) hj) -> snd p <> jj.
Proof.
  p2d_base.
  intros p Hp HE. apply NoDup_ListNoDup in NDH.
  assert (IH' : (i < length (map snd hj))%nat) by (rewrite length_map; exact IHJ).
  pose proof (proj1 (in_drop_split (map snd hj) i 0%nat (snd p) (proj2 (NoDup_ListNoDup _) NDH) IH')) as X.
  rewrite firstn_map, skipn_map, <- map_app in X. destruct (X (in_map snd _ p Hp)) as (_ & NX). apply NX. rewrite HE.
  rewrite (nth_error_nth (map snd hj) i 0%nat (eq_trans (nth_error_map snd i hj) (f_equal (option_map snd) Hh))).
  reflexivity.
Qed.

Lemma b_OPJ : slot_open hj jj = true.
Proof.
  unfold slot_open. apply existsb_exists. exists jj. split; [|apply Nat.eqb_refl].
  apply in_map_iff. exists (h, jj). split; [reflexivity|exact (nth_error_In hj i Hh)].
Qed.

Section S1.
Variables (O junk : list byte) (e1 : rentry) (live : bool) (L2 : layout) (A2 : astate) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) (e2 : rentry) (h2 : hsrc) (OUT2 CAP2 : Z) (junk2 LB : list byte)
  (qs2 : list sptr).
Hypothesis OC : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ O = []) \/
  (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L A) /\
   fresh_block B (bv_unsigned out) (bv_unsigned cap) /\ bytes_at (ms_segs B) mem (bv_unsigned out) (O ++ junk) /\
   Z.of_nat (length O) = bv_unsigned nout /\ Z.of_nat (length junk) = bv_unsigned cap - bv_unsigned nout).
Hypothesis CAPB : bv_unsigned cap <= TBBYTES.
Hypothesis SB1 : p2_sbs e e1.
Hypothesis EOK1 : CF.RelayRep.entry_ok (rc := rc) B L A m1 e1.
Hypothesis LVD : live = send_live cl br dd TOT.
Hypothesis ECF : ecap_ok (ds_ecap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)).
Hypothesis RV2 : p2_drain_RV_s RI E K L A G (bv_unsigned out) es hj e h (bv_unsigned cap) live
  (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)
  (drain_adr live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h 0
     (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h)) L2 A2 qs2.
Hypothesis RP : relay_post B (API rc) DRAIN_K
  (fun a => send_writes live (bv_unsigned out) (bv_unsigned cap) a \/
            bv_unsigned (PropExec.getr R 10) <= a < bv_unsigned (PropExec.getr R 10) + SRC_ENTRY \/
            HA + 12 <= a < HA + SRC_SIZE \/
            (exists q m, In q (entry_blocks e1 ++ hs_blocks h) /\ In (q, m) (blocks L A) /\ q <= a < q + m))
  (fun q => (live = true /\ q = bv_unsigned out) \/ In q (entry_blocks e1 ++ hs_blocks h))
  L A R m1 md L2 A2 regs2 mem2 md2.
Hypothesis INIT2 : st_init_done A2 = true.
Hypothesis OLK : live = true -> live_at L2 A2 (resolveF qs2 (da_out (drain_adr live (bv_unsigned mx) (bv_unsigned nout)
  (bv_unsigned cap) e h 0 (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h)))) OUT2 CAP2.
Hypothesis ELK : entry_links L2 A2 qs2 (drain_adr live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h 0
  (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h)) e2.
Hypothesis SLK : src_links L2 A2 qs2 (known_at L A) (drain_adr live (bv_unsigned mx) (bv_unsigned nout)
  (bv_unsigned cap) e h 0 (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h)) h2.
Hypothesis RO2 : ro_agree (ms_segs B) mem2.
Hypothesis SA2 : rw_cells (ms_segs B) mem2 (bv_unsigned (PropExec.getr R 10)) [CB 56%nat (entry_bytes e2)].
Hypothesis EOK2 : CF.RelayRep.entry_ok (rc := rc) B L2 A2 mem2 e2.
Hypothesis SRC2 : src_at (rc := rc) B L2 A2 mem2 HA h2.
Hypothesis FD2 : re_fd e2 = re_fd e1.
Hypothesis DC1 : re_cap e2 = ds_cap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h).
Hypothesis DC2 : bzs (re_U e2) = ds_u (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h).
Hypothesis DC4 : keys_texts (re_keys e2) = ds_H (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h).
Hypothesis DC5 : ent_ka e2 = ds_ka (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h).
Hypothesis DC6 : hl_cap (hs_expected h2) =
  ds_ecap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h).
Hypothesis HFD2 : hs_fd h2 = hs_fd h.
Hypothesis HPR2 : hl_recs (hs_pending h2) = [].
Hypothesis HPV2 : hl_v (hs_pending h2) = hl_v (hs_pending h).
Hypothesis HPC2 : hl_cap (hs_pending h2) = hl_cap (hs_pending h).
Hypothesis HPA2 : hs_partial h2 = hs_partial h.
Hypothesis HST2 : hs_state h2 = feed (hs_state h) (bzs (pending_stream h)).
Hypothesis HEX2 : map snd (hl_recs (hs_expected h2)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls.
Hypothesis HHL2 : hs_held h2 = hs_held h.
Hypothesis SKO2 : re_skip e2 = hs_overlong h2.
Hypothesis WU2 : re_skip e2 = 0 -> bzs (re_U e2) = bzs (hs_W h2).
Hypothesis NDK2 : NoDup (keys_texts (re_keys e2)).
Hypothesis SSK2 : same_set (keys_texts (re_keys e2)) (upds (keys_texts (re_keys e1)) Ls).
Hypothesis NDB2 : NoDup (G :: OUT2 :: entry_blocks e2 ++ hs_blocks h2).
Hypothesis GIN2 : In (G, SRC_TABLE) (blocks L2 A2).
Hypothesis SURV2 : forall q m, In (q, m) (blocks L A) -> q <> bv_unsigned out ->
  ~ In q (entry_blocks e1 ++ hs_blocks h) -> In (q, m) (blocks L2 A2).
Hypothesis BL2 : forall q m, In (q, m) (blocks L2 A2) ->
  (In (q, m) (blocks L A) /\ q <> bv_unsigned out /\ ~ In q (entry_blocks e1) /\ ~ In q (hs_blocks h)) \/
  In q (entry_blocks e2 ++ hs_blocks h2) \/ q = OUT2.
Hypothesis NEW2 : forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> bv_unsigned out ->
  ~ In q (entry_blocks e1 ++ hs_blocks h) -> q <> OUT2 /\ ~ In q (entry_blocks e2) /\ ~ In q (hs_blocks h2).
Hypothesis GBR2 : rw_cells (ms_segs B) mem2 G_BROKEN [C1 (Z_to_bv 8 (if send_off cl br TOT then br else dd))].
Hypothesis GEI2 : rw_cells (ms_segs B) mem2 G_EINTR [C1 (Z_to_bv 8 (if send_off cl br TOT then ei else 0))].
Hypothesis LBE : bzs LB = with_nul Ls.
Hypothesis LV0 : live = false -> rw_cells (ms_segs B) mem2 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
  (0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L2 A2) /\
     bytes_at (ms_segs B) mem2 (bv_unsigned out) (O ++ junk)) /\ OUT2 = bv_unsigned out.
Hypothesis LV1 : live = true -> bv_unsigned nout + TOT <= CAP2 /\
  CAP2 = ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e1 h) /\
  In (OUT2, CAP2) (blocks L2 A2) /\ fresh_block B OUT2 CAP2 /\ bytes_at (ms_segs B) mem2 OUT2 (O ++ LB ++ junk2) /\
  Z.of_nat (length junk2) = CAP2 - bv_unsigned nout - TOT /\
  rw_cells (ms_segs B) mem2 G_OUTV [C8 mx; C8 (Z_to_bv 64 (bv_unsigned nout + TOT)); C8 (Z_to_bv 64 CAP2);
    C8 (Z_to_bv 64 OUT2)].

Let es2 := firstn i es ++ e2 :: skipn (S i) es.
Let hj2 := firstn i hj ++ (h2, jj) :: skipn (S i) hj.
Let Ec := fun a => HA + 64 <= a < HA + 96 \/ slot_sp E + 40 <= a < slot_sp E + 48 \/
  (exists v n, In (v, n) (blocks L2 A2) /\ In v (hs_blocks h2) /\ v <= a < v + n).

Lemma s1_PRd : regs_preserved R regs2.
Proof. exact (proj2 (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP)). Qed.

Lemma s1_RDw : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) Ed (fun q => In q TF0) L A m1 md L2 A2 mem2 md2.
Proof.
  p2d_base. pose proof b_R0 as R0. pose proof b_EDH as EDH.
  pose proof R0 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC0).
  assert (SPR : spZ R = slot_sp E) by (unfold spZ; rewrite D2; apply unsigned_lit; lia2).
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RD0 _]. rewrite SPR in RD0.
  assert (RD1 : rmid B (API rc) DRAIN_K (slot_sp E) Ed (fun q => In q TF0) L A m1 md L2 A2 mem2 md2).
  { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ RD0).
    - intros a [SW|[SR0|[HR0|(q & m & Hq & Hm & Ha)]]].
      + destruct SW as [X|[X|[X|(LT & X)]]]; [left; exact X|right; left; exact X|right; right; left; exact X|].
        right; right; right; right; right. pose proof OC as [(C0 & _)|(C0 & _ & IN & _)]; [lia2|].
        exists (bv_unsigned out), (bv_unsigned cap). split; [exact IN|]. split; [left; reflexivity|lia2].
      + replace (bv_unsigned (PropExec.getr R 10)) with SA in SR0 by (symmetry; exact HSA).
        right; right; right; right; left. exact SR0.
      + right; right; right; left. exact HR0.
      + right; right; right; right; right. exists q, m. split; [exact Hm|]. split; [|exact Ha].
        rewrite (p2_sbs_blocks e e1 SB1) in Hq. right. exact Hq.
    - intros q [(_ & ->)|Hq]; [left; reflexivity|]. rewrite (p2_sbs_blocks e e1 SB1) in Hq. right. exact Hq. }
  apply (rmid_widen B (API rc) DRAIN_K (slot_sp E)); [exact HM1|rewrite p2_drain_k; unfold SLOT_STACK, SLOT_FRAME; lia2
    |lia2|exact HKc|lia2| | |exact RD1].
  - intros a Ha. apply SC0. unfold sk. left. exact Ha.
  - intros a Ha HE. pose proof (EDH a HE). lia2.
Qed.

Lemma s1_ST2 : stk rsegs mem2 (slot_sp E - 96) (slot_sp E).
Proof.
  p2d_base. pose proof s1_RDw as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
  split; [lia2|]. split; [lia2|]. intros a Ha.
  assert (WA : writable_at rsegs mem2 a)
    by (rewrite <- SEG; apply SC2; unfold sk; left; unfold SLOT_STACK, SLOT_FRAME; lia2).
  split; [exact WA|]. destruct (writable_hi_present mem2 a ltac:(lia2) WA) as [b HB].
  exists b. unfold mrd, wa. rewrite HB. reflexivity.
Qed.

Lemma s1_CK2 : rw_cells (ms_segs B) mem2 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)].
Proof.
  p2d_base. pose proof b_R0 as (HM1 & _). pose proof s1_RDw as RDw. pose proof b_EDI as EDI.
  apply (rmid_rw_img B (API rc) AX _ _ _ _ L A m1 md L2 A2 mem2 md2 0x318f8 _ (hg_img_low B SEG) HKc HM1 RDw CK1).
  intros k Hk1. cbn in Hk1. assert (HG : in_globals G_reply (0x318f8 + k)) by (apply in_G_bss; lia2).
  split; [exact (PL _ HG)|]. intros HE. destruct (EDI _ HE (proj1 (PL _ HG))) as [X|[X|[X|X]]];
    ugl_in X; clear - X Hk1 HAB; lia.
Qed.

Lemma s1_TD2 : forall a cs, rw_cells (ms_segs B) m1 a cs -> in_globals G_reply a ->
  (forall k, 0 <= k < Z.of_nat (cells_size cs) -> in_globals G_reply (a + k) /\ ~ Ed (a + k)) ->
  rw_cells (ms_segs B) mem2 a cs.
Proof.
  p2d_base. pose proof b_R0 as (HM1 & _). pose proof s1_RDw as RDw.
  intros a cs H _ D. apply (rmid_rw_img B (API rc) AX _ _ _ _ L A m1 md L2 A2 mem2 md2 a cs (hg_img_low B SEG)
    HKc HM1 RDw H). intros k Hk1. destruct (D k Hk1) as [D1' D2']. split; [exact (PL _ D1')|exact D2'].
Qed.

Lemma s1_OLD : forall x m, In (x, m) (blocks L A) -> 0 < m -> ~ In x TA0 ->
  In (x, m) (blocks L2 A2) /\ ~ In x (hs_blocks h2) /\ ~ In x (entry_blocks e2) /\ x <> OUT2.
Proof.
  intros x m Hx Hm NT.
  assert (N1 : x <> bv_unsigned out) by (intros ->; apply NT; left; reflexivity).
  assert (N2 : ~ In x (entry_blocks e1 ++ hs_blocks h)).
  { rewrite (p2_sbs_blocks e e1 SB1). intros X. apply NT. right. right. exact X. }
  destruct (NEW2 x m Hx Hm N1 N2) as (Y1 & Y2 & Y3).
  split; [exact (SURV2 x m Hx N1 N2)|]. split; [exact Y3|]. split; [exact Y2|exact Y1].
Qed.

Lemma s1_ND2T : NoDup (target_addrs G OUT2 es2 hj2).
Proof.
  p2d_base. pose proof b_OTX as OTX. pose proof b_OTHP as OTHP. pose proof s1_OLD as OLD.
  assert (FR : forall l, Forall2 p2_sbs l l) by (induction l as [|a l IHl]; constructor; [apply p2_sbs_refl|exact IHl]).
  destruct (p2_repl_facts (skipn (S i) es) (firstn i es) i e2 (p2_len_firstn es i IL)) as (_ & _ & NE2i).
  destruct (p2_repl_facts (skipn (S i) hj) (firstn i hj) i (h2, jj) (p2_len_firstn hj i IHJ)) as (_ & _ & NH2i).
  pose proof (p2_oth_repl es hj i (firstn i es) (skipn (S i) es) e2 (h2, jj) IL IHJ (FR _) (FR _)) as OTHEQ2.
  unfold es2, hj2. apply (p2_nd_join G OUT2 _ _ i e2 h2 jj NE2i NH2i NDB2);
    [rewrite OTHEQ2; exact (p2_oth_nd G (bv_unsigned out) es hj i e h jj NDA Hi Hh)|].
  intros x Hx. rewrite OTHEQ2 in Hx. destruct (OTX x Hx) as (NT & _). destruct (OTHP x Hx) as (m & Hm & Hxm).
  destruct (OLD x m Hxm Hm NT) as (Hx2 & NH2x & NE2x & NOx). intros [EQ|[EQ|X]].
  - apply NT. rewrite <- EQ. right; left; reflexivity.
  - exact (NOx (eq_sym EQ)).
  - apply in_app_or in X. destruct X as [X|X]; [exact (NE2x X)|exact (NH2x X)].
Qed.

Lemma s1_TOTP : live = true -> 0 < TOT.
Proof.
  p2d_base. intros LT.
  pose proof (dc_live gn cl br dd TOT HGN (proj1 HGG) (proj2 HGG)) as DL. rewrite <- LVD, LT in DL.
  assert (TN : 0 <= TOT) by (unfold TOT; lia).
  destruct (Z.eqb_spec TOT 0) as [X|X]; [rewrite andb_false_r in DL; discriminate|lia].
Qed.

Lemma s1_CBL : live = true -> CAP2 <= TBBYTES.
Proof.
  p2d_base. pose proof b_SRC1 as SRC1.
  pose proof SB1 as (SF1 & SE1 & SS1 & SP1 & SBU1 & SU1 & SC1' & SH1 & SKH1 & SP2 & SK1 & SUU1 & SJ1).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV & _).
  destruct (dc_counts B L A mem es hj e h h2 jj K (ss_n E) HES (p2_combine_nth es hj i e (h, jj) Hi Hh) Hcost
    (proj2 Hk) Hn SSK NDT EXP0 HOV SKO WU HEX2 HHL2) as (_ & TOT26 & _).
  intros LT. pose proof (LV1 LT) as (_ & CAPF & _).
  pose proof (CF.RelayCap.drain_ocap_le_tot true (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e1 h
    (p2_fin_no true (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) rc B L A m1 e1 h HA EOK1 SRC1
      ltac:(rewrite SS1; exact SKO) ltac:(rewrite SS1, SUU1; exact WU))) as OCB.
  rewrite LT in CAPF. rewrite <- CAPF in OCB.
  change (Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h)))))) with TOT in OCB, TOT26.
  clear - OCB CAPB HNO TOT26. unfold TBBYTES in *. rewrite HNO in OCB. lia.
Qed.

Lemma s1_GOV2 : rw_cells (ms_segs B) mem2 G_OUTV [C8 mx; C8 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout);
  C8 (if live then Z_to_bv 64 CAP2 else cap); C8 (if live then Z_to_bv 64 OUT2 else out)].
Proof.
  destruct (Sumbool.sumbool_of_bool live) as [LV|LV]; rewrite LV;
    [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (LV1 LV)))))))|exact (proj1 (LV0 LV))].
Qed.

Lemma s1_BOB2 : bytes_at (ms_segs B) mem2 OUT2 (if live then LB else []).
Proof.
  apply (dc_ob_bytes B mem2 live LB O junk2 out OUT2); [|exact (dc_O_nil B L A mem _ _ _ O junk OC HNO)|].
  - intros LT. exact (proj1 (proj2 (proj2 (proj2 (proj2 (LV1 LT)))))).
  - intros LF. exact (proj2 (proj2 (LV0 LF))).
Qed.

Ltac p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB :=
  pose proof s1_RDw as RDw;
  pose proof RDw as (HM2 & HWF2 & HBD2 & LY2 & LN2 & PA2 & SV2 & Z02 & OW2 & MD2 & BY2 & BK2 & SC2);
  pose proof s1_PRd as PRd;
  pose proof (dc_O_nil B L A mem _ _ _ O junk OC HNO) as O0;
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV & _);
  destruct (dc_counts B L A mem es hj e h h2 jj K (ss_n E) HES (p2_combine_nth es hj i e (h, jj) Hi Hh) Hcost
    (proj2 Hk) Hn SSK NDT EXP0 HOV SKO WU HEX2 HHL2) as (PL26 & TOT26 & NDH2 & EN26 & HB22);
  destruct (dc_no_loss B gn cl br dd live h h2 e2 Ls LB nout out OUT2 CAP2 G L2 A2 HGN (proj1 HGG) (proj2 HGG) LVD
    EXP0 HEX2 (dc_lines_range h) LBE HNO (fun LF => proj2 (proj2 (LV0 LF)))
    (fun LT => let X := LV1 LT in conj (proj1 X) (conj (proj1 (proj2 (proj2 X))) (proj1 (proj2 (proj2 (proj2 X))))))
    NDB2) as (DN1 & DN2 & DN3 & DN4 & DN5 & DN6);
  destruct (p2_repl_facts (skipn (S i) es) (firstn i es) i e2 (p2_len_firstn es i IL)) as (_ & _ & NE2i);
  destruct (p2_repl_facts (skipn (S i) hj) (firstn i hj) i (h2, jj) (p2_len_firstn hj i IHJ)) as (_ & _ & NH2i);
  assert (NB2 : List.NoDup (map fst (blocks L2 A2)))
    by (pose proof (NDB L2 A2 mem2 md2 HM2) as XN; first [exact XN|exact (proj1 (NoDup_ListNoDup _) XN)]);
  destruct (p2_nd_split _ _ _ _ NDB2) as (NG2 & NGL & NOL & NDE2 & NDH2' & DEH).

Lemma s1_CPF : live = false ->
  ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h) = bv_unsigned cap.
Proof. intros LF. rewrite LF. unfold drain_fin, drain_go. rewrite CF.RelayCap.drain_run_dead. reflexivity. Qed.

Lemma s1_CPT : live = true ->
  CAP2 = ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h).
Proof.
  intros LT. rewrite <- (p2d_dfn e e1 h live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) SB1).
  exact (proj1 (proj2 (LV1 LT))).
Qed.

Lemma s1_LEN2 : length es2 = length es /\ length hj2 = length hj.
Proof.
  p2d_base. split.
  - unfold es2. rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. clear - IL. lia.
  - unfold hj2. rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. clear - IHJ. lia.
Qed.

Lemma s1_MV2 : nc_move (view_of G (bv_unsigned out) es hj) L A (view_of G OUT2 es2 hj2) L2 A2
  (p2_dr_dels (bv_unsigned out) (bv_unsigned cap) OUT2
     (ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)) e e2
     (hs_expected h) (hs_expected h2))
  (p2_dr_adds (bv_unsigned out) (bv_unsigned cap) OUT2
     (ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)) e e2
     (hs_expected h) (hs_expected h2)).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof (proj1 (NoDup_ListNoDup _) s1_ND2T) as ND2Tl.
  destruct (p2_ta_nd _ _ _ _ NDAl) as (NV0 & _).
  destruct (p2_ta_nd _ _ _ _ ND2Tl) as (NV2 & NR2).
  pose proof (CF.SlotPass4.p4_src_blk_of B L A mem HA h SRC) as (P0P & P0T & P0E & P0H & _).
  pose proof (CF.SlotPass4.p4_src_blk_of B L2 A2 mem2 HA h2 SRC2) as (P2P & P2T & P2E & P2H & _).
  pose proof EOK2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EBUF2 & _ & EHP2 & _).
  pose proof s1_CPF as CPF. pose proof s1_CPT as CPT.
  apply (p2_drain_mv L A L2 A2 G (bv_unsigned out) (bv_unsigned cap) OUT2 _ es es2 hj hj2 (firstn i es)
    (skipn (S i) es) (firstn i hj) (skipn (S i) hj) e e2 h h2 jj ESP HJP eq_refl eq_refl NB0 NB2 NV0 NV2
    HPV2 HPC2 HPA2 HHL2).
  - intros x m Hx Hin.
    assert (NXT : x <> bv_unsigned out /\ ~ In x (entry_blocks e1 ++ hs_blocks h)).
    { rewrite (p2_sbs_blocks e e1 SB1). destruct Hin as [<-|Ho].
      - split; [exact GO0|exact GN0].
      - destruct (p2_oth_out G (bv_unsigned out) es hj i e h jj x NDA Hi Hh Ho) as (N0 & _).
        split; [intros EQ; apply N0; right; left; symmetry; exact EQ|intros X; apply N0; right; right; exact X]. }
    exact (SURV2 x m Hx (proj1 NXT) (proj2 NXT)).
  - exact (proj1 P0P).
  - exact (proj1 P2P).
  - exact P0T.
  - exact P2T.
  - exact (proj1 P0H).
  - exact (proj1 P2H).
  - exact (proj1 P0E).
  - exact (proj1 P2E).
  - intros S m Hm. unfold out_same in S. apply andb_true_iff in S as [S1 S2]. apply Z.eqb_eq in S1, S2.
    pose proof OC as [(CZ0 & OZ0 & _)|(CZ0 & _ & INq & _)].
    { exfalso. pose proof (p2_low rc B (API rc) L A mem md _ _ HMR Hm) as LW. clear - OZ0 LW. lia. }
    rewrite (p2_uniq L A _ _ _ NB0 Hm INq). destruct (Sumbool.sumbool_of_bool live) as [LV|LV].
    + pose proof (LV1 LV) as (_ & _ & INO & _). rewrite (CPT LV), S2, S1 in INO. exact INO.
    + exact (proj1 (proj1 (proj2 (LV0 LV)) CZ0)).
  - intros tt Hu. unfold out_move_dels in Hu.
    match type of Hu with In _ (if ?b then _ else _) => destruct b eqn:C end; [destruct Hu|].
    destruct Hu as [<-|[]]. apply orb_false_iff in C as [_ C]. apply Z.eqb_neq in C.
    pose proof OC as [(CZ0 & _)|(_ & _ & INq & _)]; [contradiction|exact INq].
  - intros tt Hu. unfold out_move_adds in Hu.
    match type of Hu with In _ (if ?b then _ else _) => destruct b eqn:C end; [destruct Hu|].
    destruct Hu as [<-|[]]. destruct (Sumbool.sumbool_of_bool live) as [LV|LV].
    + pose proof (LV1 LV) as (_ & _ & INO & _). rewrite <- (CPT LV). exact INO.
    + exfalso. unfold out_same in C. rewrite (CPF LV), (proj2 (proj2 (LV0 LV))), !Z.eqb_refl in C.
      cbn [andb] in C. discriminate.
  - intros CZ0 m Hm. pose proof OC as [(_ & OZ0 & _)|(CZ1 & _)]; [|clear - CZ0 CZ1; lia].
    pose proof (p2_low rc B (API rc) L A mem md _ _ HMR Hm) as LW. clear - OZ0 LW. lia.
  - intros C. destruct EBUF as [(X & _)|(_ & X & _)]; [contradiction|exact X].
  - intros C. destruct EHP as [(X & _)|(X & _)]; [contradiction|exact X].
  - intros C. destruct EBUF2 as [(X & _)|(_ & X & _)]; [contradiction|exact X].
  - intros C. destruct EHP2 as [(X & _)|(X & _)]; [contradiction|exact X].
  - intros q m Hq. exact (p2_pos rc B (API rc) L A mem md q m HMR Hq).
  - intros q m Hq. exact (p2_pos rc B (API rc) L2 A2 mem2 md2 q m HM2 Hq).
Qed.

Lemma s1_SV0 : forall x m, In (x, m) (blocks L A) -> In x (p2_oth es hj i) -> In (x, m) (blocks L2 A2).
Proof.
  intros x m Hx Ho. destruct (b_OTX x Ho) as (NT & _). apply (SURV2 x m Hx).
  - intros ->. apply NT. left. reflexivity.
  - rewrite (p2_sbs_blocks e e1 SB1). intros X. apply NT. right. right. exact X.
Qed.

Lemma s1_OB2 : CF.SlotRI3.nc_sz L2 A2 OUT2 <= TBBYTES.
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. pose proof b_SRC1 as SRC1.
  pose proof SB1 as (SF1 & SE1 & SS1 & SP1 & SBU1 & SU1 & SC1' & SH1 & SKH1 & SP2 & SK1 & SUU1 & SJ1).
  assert (TOT26' : TOT < 2 ^ 26) by exact TOT26.
  destruct (Sumbool.sumbool_of_bool live) as [LV|LV].
  - pose proof (LV1 LV) as (TL1 & CAPF & INO & _).
    pose proof (CF.RelayCap.drain_ocap_le_tot live (bv_unsigned mx) (bv_unsigned nout)
      (bv_unsigned cap) e1 h (p2_fin_no live (bv_unsigned mx) (bv_unsigned nout)
        (bv_unsigned cap) rc B L A m1 e1 h HA EOK1 SRC1 ltac:(rewrite SS1; exact SKO)
        ltac:(rewrite SS1, SUU1; exact WU))) as OCB.
    rewrite <- CAPF in OCB.
    change (Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h)))))) with TOT in OCB.
    rewrite (CF.SlotNcWt.nw_sz_at L2 A2 _ _ NB2 INO). clear - OCB CAPB HNO TOT26'. unfold TBBYTES in *.
    rewrite HNO in OCB. lia.
  - destruct (LV0 LV) as (_ & LV02 & LV03). rewrite LV03.
    pose proof OC as [(C0 & O0' & _)|(C0 & _)].
    + rewrite O0', (CF.SlotNcWt.nw_sz_none L2 A2 0); [unfold TBBYTES; lia2|].
      intros m Hm. pose proof (p2_low rc B (API rc) L2 A2 mem2 md2 _ _ HM2 Hm) as LW. lia2.
    + rewrite (CF.SlotNcWt.nw_sz_at L2 A2 _ _ NB2 (proj1 (LV02 C0))). exact CAPB.
Qed.

Lemma s1_NCS2 : CF.SlotRI3.ncs (view_of G OUT2 es2 hj2) L2 A2 <= nc_wt es2 hj2.
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof s1_SV0 as SV0. pose proof s1_LEN2 as (LEN2 & LHJ2).
  apply (p2_ncs_wt L2 A2 G OUT2 es2 hj2 NB2);
    [rewrite (CF.SlotNcWt.nw_sz_at L2 A2 _ _ NB2 GIN2); apply Z.le_refl|exact s1_OB2| |
     |rewrite LEN2; exact Hes|rewrite LHJ2, LHJ; exact Hes].
  - unfold es2. apply Forall_app. split; [|constructor].
    + apply Forall_forall. intros e0 He0. apply (p2_eb_keep L A L2 A2 e0).
      * intros x m Hx Hxe. apply SV0; [exact Hx|]. unfold p2_oth. apply in_or_app. left. apply in_concat.
        exists (entry_blocks e0). split; [apply in_map; exact He0|exact Hxe].
      * rewrite Forall_forall in ESpre.
        exact (CF.SlotPass4.p4_blk_eb _ _ _ (CF.SlotPass4.p4_ent_blk_of B L A mem e0 (ESpre e0 He0))).
    + exact (CF.SlotPass4.p4_blk_eb _ _ _ (CF.SlotPass4.p4_ent_blk_of B L2 A2 mem2 e2 EOK2)).
    + apply Forall_forall. intros e0 He0. apply (p2_eb_keep L A L2 A2 e0).
      * intros x m Hx Hxe. apply SV0; [exact Hx|]. unfold p2_oth. apply in_or_app. right. apply in_or_app. left.
        apply in_concat. exists (entry_blocks e0). split; [apply in_map; exact He0|exact Hxe].
      * rewrite Forall_forall in ESpost.
        exact (CF.SlotPass4.p4_blk_eb _ _ _ (CF.SlotPass4.p4_ent_blk_of B L A mem e0 (ESpost e0 He0))).
  - unfold hj2. apply Forall_app. split; [|constructor].
    + apply Forall_forall. intros p Hp. destruct (pair_find _ _ _ _ _ p PApre Hp) as [e0 (S0 & _)]. cbv zeta in S0.
      apply (p2_sb_keep L A L2 A2 (fst p)).
      * intros x m Hx Hxh. apply SV0; [exact Hx|]. unfold p2_oth. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. left. apply in_concat. exists (hs_blocks (fst p)).
        split; [exact (in_map (fun p => hs_blocks (fst p)) _ p Hp)|exact Hxh].
      * exact (CF.SlotPass4.p4_blk_sb _ _ _ (CF.SlotPass4.p4_src_blk_of B L A mem _ (fst p) S0)).
    + exact (CF.SlotPass4.p4_blk_sb _ _ _ (CF.SlotPass4.p4_src_blk_of B L2 A2 mem2 HA h2 SRC2)).
    + apply Forall_forall. intros p Hp. destruct (pair_find _ _ _ _ _ p PApost Hp) as [e0 (S0 & _)]. cbv zeta in S0.
      apply (p2_sb_keep L A L2 A2 (fst p)).
      * intros x m Hx Hxh. apply SV0; [exact Hx|]. unfold p2_oth. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. right. apply in_concat. exists (hs_blocks (fst p)).
        split; [exact (in_map (fun p => hs_blocks (fst p)) _ p Hp)|exact Hxh].
      * exact (CF.SlotPass4.p4_blk_sb _ _ _ (CF.SlotPass4.p4_src_blk_of B L A mem _ (fst p) S0)).
Qed.

Lemma s1_WT2 : nc_wt es2 hj2 <=
  drain_wt es hj e h (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h).
Proof.
  p2d_base. pose proof EOK2 as (_ & _ & _ & _ & _ & _ & EUL2 & _).
  unfold es2, hj2.
  rewrite (drain_wt_post (firstn i es) (skipn (S i) es) (firstn i hj) (skipn (S i) hj) e e2 h h2 jj jj _
    DC1 EUL2 DC2 DC5 DC4 HPR2 HPC2 DC6 HEX2 HHL2).
  rewrite <- ESP, <- HJP. apply Z.le_refl.
Qed.

Lemma s1_RI2 : RI E K (view_of G OUT2 es2 hj2) L2 A2.
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof s1_LEN2 as (LEN2 & LHJ2). pose proof s1_CPF as CPF. pose proof s1_CPT as CPT.
  pose proof s1_MV2 as MV2.
  apply (RV2 e2 h2 OUT2).
  - intros LT. rewrite <- (CPT LT). exact (OLK LT).
  - intros LF. split; [exact (proj2 (proj2 (LV0 LF)))|exact (CPF LF)].
  - exact ELK.
  - exact SLK.
  - exact DC1.
  - exact DC5.
  - exact DC6.
  - intros q m Hq. destruct (BL2 q m Hq) as [(Hq1 & _)|[HEH|HO]]; [left; exact Hq1|right|right].
    + apply (p2_mid_in G OUT2 es2 hj2 i e2 h2 jj q NE2i NH2i). right; right. exact HEH.
    + apply (p2_mid_in G OUT2 es2 hj2 i e2 h2 jj q NE2i NH2i). right; left. symmetry. exact HO.
  - exists (pend_view (firstn i hj)), (pend_view (skipn (S i) hj)). split.
    + transitivity (pend_view (firstn i hj ++ (h, jj) :: skipn (S i) hj)); [rewrite <- HJP; reflexivity|].
      unfold pend_view. rewrite map_app. reflexivity.
    + unfold hj2, pend_view. rewrite map_app. cbn [map fst]. rewrite HPR2. reflexivity.
  - exists (ek_view (firstn i hj)), (ek_view (skipn (S i) hj)). split.
    + transitivity (ek_view (firstn i hj ++ (h, jj) :: skipn (S i) hj)); [rewrite <- HJP; reflexivity|].
      apply p2_ek_split.
    + unfold hj2. rewrite p2_ek_split. cbn [fst].
      rewrite (p2_ekeys_app (hs_expected h) (hs_expected h2) Ls HEX2 (dc_lines_range h)), <- app_assoc. reflexivity.
  - rewrite LEN2. exact Hes.
  - rewrite LHJ2, LHJ. exact Hes.
  - exact MV2.
  - exact NB2.
  - exact (p2_nc_keep _ _ _ _ _ _ _ _ HWF LY2 MV2).
  - exact s1_NCS2.
  - exact s1_WT2.
Qed.

Lemma s1_COST2 : slot_cost es2 hj2 <= K.
Proof.
  p2d_base. pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV & _).
  unfold es2, hj2. rewrite (p2_cost_app (firstn i es) (firstn i hj) e2 (h2, jj) (skipn (S i) es) (skipn (S i) hj)
    ltac:(rewrite (p2_len_firstn es i IL), (p2_len_firstn hj i IHJ); reflexivity)).
  pose proof (p2_cost_app (firstn i es) (firstn i hj) e (h, jj) (skipn (S i) es) (skipn (S i) hj)
    ltac:(rewrite (p2_len_firstn es i IL), (p2_len_firstn hj i IHJ); reflexivity)) as CO.
  rewrite <- ESP, <- HJP in CO.
  pose proof EOK2 as (_ & _ & _ & _ & _ & _ & EUL2 & _).
  pose proof SRC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV2 & _).
  pose proof SSK2 as SSK2e. rewrite (p2_sbs_texts e e1 SB1) in SSK2e.
  pose proof (p2_pair_cost e e2 h h2 jj SKO WU HOV EUL SKO2 WU2 HOV2 EUL2 HST2 HPR2 NDK2 SSK2e) as PCC.
  clear - CO PCC Hcost. lia.
Qed.

Section S2.
Variables (m3 : word -> option byte) (R3 : bvmap 5 word).
Hypothesis Q1 : PropExec.getr R3 1 = Z_to_bv 64 0x14398.
Hypothesis Q2 : PropExec.getr R3 2 = Z_to_bv 64 (slot_sp E).
Hypothesis Q3 : PropExec.getr R3 3 = YK11.getr (ss_regs E) 3.
Hypothesis Q4 : PropExec.getr R3 4 = YK11.getr (ss_regs E) 4.
Hypothesis Q8 : PropExec.getr R3 8 = Z_to_bv 64 (ss_p E + K).
Hypothesis Q10 : PropExec.getr R3 10 = Z_to_bv 64 HA.
Hypothesis Q11 : PropExec.getr R3 11 = Z_to_bv 64 (slot_sp E + 40).
Hypothesis Q19 : PropExec.getr R3 19 = Z_to_bv 64 4.
Hypothesis Q20 : PropExec.getr R3 20 = Z_to_bv 64 G_RELAY_LO.
Hypothesis Q21 : PropExec.getr R3 21 = Z_to_bv 64 10.
Hypothesis Q22 : PropExec.getr R3 22 = Z_to_bv 64 t.
Hypothesis Q23 : PropExec.getr R3 23 = Z_to_bv 64 (slot_sp E + 32).
Hypothesis Q24 : PropExec.getr R3 24 = Z_to_bv 64 1.
Hypothesis Q25 : PropExec.getr R3 25 = Z_to_bv 64 DIV10.
Hypothesis Q26 : PropExec.getr R3 26 = Z_to_bv 64 (ss_n E - K).
Hypothesis Q27 : PropExec.getr R3 27 = Z_to_bv 64 (G_S + 4).
Hypothesis MU3 : munch [(slot_sp E - 96, slot_sp E); (0x318fc, 0x31900)] mem2 m3.
Hypothesis WM3 : wmono rsegs mem2 m3.
Hypothesis RO3 : MemNorm.ro_agree rsegs m3.
Hypothesis ST3 : stk rsegs m3 (slot_sp E - 96) (slot_sp E).
Hypothesis CK3 : rw_cells rsegs m3 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

Lemma s2_Ru : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) (fun a => 0x318fc <= a < 0x31900) (fun _ => False)
    L2 A2 mem2 md2 L2 A2 m3 md2.
Proof.
  p2d_base. pose proof s1_RDw as (HM2 & HWF2 & HBD2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
  apply (rmid_A B (API rc) _ _ _ _ L2 A2 mem2 md2 m3 [(slot_sp E - 96, slot_sp E); (0x318fc, 0x31900)] HM2 HWF2 HBD2
    (hg_img_low B SEG) HKc).
  - intros a Ha. exact (SC2 a Ha).
  - exact MU3.
  - rewrite SEG. exact WM3.
  - intros x Hx HO. destruct (p2_outW _ _ _ _ HO) as [X|X]; [left; unfold SLOT_STACK, SLOT_FRAME; lia2|right; exact X].
  - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM2 HO). cbn [outside].
    split; [intros HX; lia2|]. split; [|exact I].
    intros HX. exact (GNO _ _ _ _ a HM2 (in_G_bss a ltac:(lia2)) HO).
  - intros p n k HP Hk1 HO. exfalso. apply HO.
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n k HM2 HP Hk1) as (_ & _ & X & _).
    pose proof (ax_blocks_img AX L2 A2 mem2 md2 p n k HM2 HP Hk1) as NIm. cbn [outside].
    split; [intros HX; lia2|]. split; [|exact I].
    intros HX. apply NIm. exact (proj1 (PL _ (in_G_bss (ptr_addr L2 p + k) ltac:(lia2)))).
Qed.

Lemma s2_SRC3 : src_at (rc := rc) B L2 A2 m3 HA h2.
Proof.
  p2d_base. pose proof s1_RDw as (HM2 & _). pose proof s2_Ru as Ru.
  assert (KU : forall q, kept_block (fun a => 0x318fc <= a < 0x31900) (fun _ => False) L2 A2 q).
  { intros q. split; [intros []|]. intros k a Hq Ha HE.
    destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 q k a FA HM2 Hq Ha) as (NIa & _).
    apply NIa. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(clear - HE; lia)))). }
  apply (p2_src_rmid rc fx B (API rc) _ _ _ _ L2 A2 mem2 md2 L2 A2 m3 md2 HA h2 FA SEG HKc HM2 Ru SRC2);
    [|intros q _; apply KU].
  intros k Hk1.
  split; [apply PL; apply in_G_bss; clear - Hk1 HAB SSe; lia|clear - Hk1 HAB SSe; lia].
Qed.

Lemma s2_TM3 : forall a cs, rw_cells (ms_segs B) mem2 a cs ->
  disjoint_from [(slot_sp E - 96, slot_sp E); (0x318fc, 0x31900)] a (Z.of_nat (cells_size cs)) ->
  rw_cells (ms_segs B) m3 a cs.
Proof.
  p2d_base. intros a cs H D. rewrite SEG in H |- *. eapply rw_cells_transport; [exact H|exact MU3|exact WM3|exact D].
Qed.

Lemma s2_GOV3 : rw_cells (ms_segs B) m3 G_OUTV [C8 mx; C8 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout);
  C8 (if live then Z_to_bv 64 CAP2 else cap); C8 (if live then Z_to_bv 64 OUT2 else out)].
Proof. p2d_base. apply s2_TM3; [exact s1_GOV2|]. cbn. ugl. lia2. Qed.

Lemma s2_GG3 : bytes_at (ms_segs B) m3 G_GONE [Z_to_bv 8 gn].
Proof.
  p2d_base. pose proof b_NEDG as NEDG.
  apply p2_rw_bytes1. apply s2_TM3; [|cbn; ugl; lia2].
  apply s1_TD2; [apply b_TW; [exact G5|cbn; ugl; lia2]|apply in_G_bss; ugl; lia2|].
  intros k Hk1. cbn in Hk1. assert (HG : in_globals G_reply (G_GONE + k)) by (apply in_G_bss; ugl; lia2).
  split; [exact HG|]. apply NEDG; [exact HG|ugl; lia2|ugl; lia2|ugl; lia2|ugl; lia2].
Qed.

Lemma s2_C403 : rw_cells (ms_segs B) m3 (slot_sp E + 40) [C8 (Z_to_bv 64 0)].
Proof.
  p2d_base. pose proof b_R0 as (HM1 & _). pose proof s1_RDw as RDw. pose proof b_EDH as EDH.
  apply s2_TM3; [|cbn; lia2].
  apply (rmid_rw_hi B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) Ed (fun q => In q TF0) L A m1 md L2 A2 mem2 md2
    (slot_sp E + 40) _); [lia2|rewrite ERR; lia2|exact HM1|exact RDw|exact C401|lia2|cbn; lia2|].
  intros k Hk1 HE. pose proof (EDH _ HE). lia2.
Qed.

Lemma s2_BOB3 : bytes_at (ms_segs B) m3 (bv_unsigned (if live then Z_to_bv 64 OUT2 else out)) (if live then LB else []).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof s1_BOB2 as BOB2. pose proof s1_TOTP as TOTP.
  rewrite DN2. destruct (Sumbool.sumbool_of_bool live) as [LV|LV]; rewrite LV.
  - pose proof (LV1 LV) as (TL1 & _ & INO & FRO & _). rewrite LV in BOB2. rewrite SEG in BOB2 |- *.
    specialize (TOTP LV).
    eapply bytes_at_transport; [exact BOB2|exact MU3|].
    pose proof (with_nul_bzs Ls LB LBE) as LBL. pose proof FRO as (FR1 & FR2 & FR3).
    apply (entry_disjoint_pts [(slot_sp E - 96, slot_sp E); (0x318fc, 0x31900)]);
      [apply Forall_forall; intros iv Hiv; destruct Hiv as [<-|[<-|[]]]; cbn; lia2
      |rewrite LBL; change (0 < TOT); exact TOTP|].
    intros x Hx. cbn [outside]. split; [intros HX; lia2|]. split; [|exact I].
    intros HX. apply (FR3 (x - OUT2) ltac:(lia2)). replace (OUT2 + (x - OUT2)) with x by lia2.
    exact (proj1 (PL _ (in_G_bss x ltac:(lia2)))).
  - apply p2_bytes_nil. rewrite (proj2 (proj2 (LV0 LV))). lia2.
Qed.

Section S3.
Variables (L3 : layout) (A3 : astate) (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model)
  (E3 H3 : hlist) (qs3 : list sptr).
Let h3 := set_exp_held h2 E3 H3.
Hypothesis RV3 : p2_cnl_RV_s RI E K L2 A2 G OUT2 es2 hj2 h2 L3 A3 qs3.
Hypothesis SHR3 : sh_real L3 qs3 (check_no_loss_sh 0 (sh_of (known_at L2 A2) (hs_held h2))
  (map (shr (known_at L2 A2)) (hl_recs (hs_expected h2)))) H3.
Hypothesis SHL3 : sh_live A3 qs3 (check_no_loss_sh 0 (sh_of (known_at L2 A2) (hs_held h2))
  (map (shr (known_at L2 A2)) (hl_recs (hs_expected h2)))).
Hypothesis RPc : relay_post B (API rc) CHECK_NO_LOSS_K
  (fun a => HA + 64 <= a < HA + 96 \/
            bv_unsigned (PropExec.getr R3 11) <= a < bv_unsigned (PropExec.getr R3 11) + 8 \/
            (0 < hl_cap (hs_expected h2) /\
             hl_v (hs_expected h2) <= a < hl_v (hs_expected h2) + 16 * hl_cap (hs_expected h2)) \/
            (0 < hl_cap (hs_held h2) /\ hl_v (hs_held h2) <= a < hl_v (hs_held h2) + 16 * hl_cap (hs_held h2)))
  (fun q => In q (map fst (hl_recs (hs_expected h2)) ++ list_blocks (hs_held h2)))
  L2 A2 R3 m3 md2 L3 A3 regs4 mem4 md4.
Hypothesis INIT3 : st_init_done A3 = true.
Hypothesis RO4 : ro_agree (ms_segs B) mem4.
Hypothesis SRC4 : src_at (rc := rc) B L3 A3 mem4 HA h3.
Hypothesis E3R : hl_recs E3 = [].
Hypothesis E3V : hl_v E3 = hl_v (hs_expected h2).
Hypothesis E3C : hl_cap E3 = hl_cap (hs_expected h2).
Hypothesis NDH3 : NoDup (texts H3).
Hypothesis H3C : hl_cap H3 <= Z.max 8 (Z.max (hl_cap (hs_held h2))
  (2 * (hl_n (hs_held h2) + Z.of_nat (count_begin (texts (hs_expected h2)))))).
Hypothesis H3T : texts H3 = upds (texts (hs_held h2)) (texts (hs_expected h2)).
Hypothesis AT4 : rw_cells (ms_segs B) mem4 (bv_unsigned (PropExec.getr R3 11))
  [C8 (Z_to_bv 64 (if gn =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h2))) else 0))].
Hypothesis BNO4 : bytes_at (ms_segs B) mem4 G_NOUT (le8 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)).
Hypothesis SURV3 : forall q m, In (q, m) (blocks L2 A2) ->
  ~ In q (map fst (hl_recs (hs_expected h2)) ++ list_blocks (hs_held h2)) -> In (q, m) (blocks L3 A3).
Hypothesis BL3 : forall q m, In (q, m) (blocks L3 A3) ->
  (In (q, m) (blocks L2 A2) /\ (0 < m -> ~ In q (map fst (hl_recs (hs_expected h2)) ++ list_blocks (hs_held h2)))) \/
  In q (list_blocks H3).
Hypothesis NEW3 : forall q m, In (q, m) (blocks L2 A2) -> 0 < m ->
  ~ In q (map fst (hl_recs (hs_expected h2)) ++ list_blocks (hs_held h2)) -> ~ In q (list_blocks H3).

Lemma s3_PRc : regs_preserved R3 regs4.
Proof. exact (proj2 (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RPc)). Qed.

Lemma s3_AT3 : bv_unsigned (PropExec.getr R3 11) = slot_sp E + 40.
Proof. p2d_base. rewrite Q11. apply unsigned_lit. lia2. Qed.

Lemma s3_Rcw : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) Ec (fun q => In q (hs_blocks h2))
  L2 A2 m3 md2 L3 A3 mem4 md4.
Proof.
  p2d_base. pose proof s1_RDw as (HM2 & _). pose proof s2_Ru as Ru. pose proof s2_SRC3 as SRC3.
  pose proof s3_AT3 as AT3.
  assert (SPR3 : spZ R3 = slot_sp E)
    by (unfold spZ; change (bv_unsigned (PropExec.getr R3 2) = slot_sp E); rewrite Q2; apply unsigned_lit; lia2).
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RPc) as [RC0 _]. rewrite SPR3 in RC0.
  pose proof SRC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE3 & LH3 & _).
  assert (RC1 : rmid B (API rc) CHECK_NO_LOSS_K (slot_sp E) Ec (fun q => In q (hs_blocks h2)) L2 A2 m3 md2 L3 A3 mem4 md4).
  { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ RC0).
    - intros a [X|[X|[(Cp & X)|(Cp & X)]]].
      + left. exact X.
      + right; left. rewrite AT3 in X. lia2.
      + right; right. destruct LE3 as (_ & _ & [(C0 & _)|(_ & IN & _)] & _); [lia2|].
        exists (hl_v (hs_expected h2)), (16 * hl_cap (hs_expected h2)). split; [exact IN|].
        split; [apply p2_hb_exp, p2_lb_v; lia2|exact X].
      + right; right. destruct LH3 as (_ & _ & [(C0 & _)|(_ & IN & _)] & _); [lia2|].
        exists (hl_v (hs_held h2)), (16 * hl_cap (hs_held h2)). split; [exact IN|].
        split; [apply p2_hb_held, p2_lb_v; lia2|exact X].
    - intros q Hq. apply in_app_or in Hq. destruct Hq as [Hq|Hq]; [apply p2_hb_exp, p2_lb_recs; exact Hq|].
      apply p2_hb_held. exact Hq. }
  pose proof Ru as (HM3 & HWF3 & HBD3 & _ & _ & _ & _ & _ & _ & MD3 & _ & _ & SCu).
  assert (ECL : forall a, Ec a -> a < slot_sp E - (SLOT_STACK - SLOT_FRAME) \/ slot_sp E <= a).
  { intros a [X|[X|(v & n & Hv & _ & Ha)]].
    - left. unfold SLOT_STACK, SLOT_FRAME. lia2.
    - right. lia2.
    - left. destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a - v) FA HM2 Hv ltac:(lia2)) as (_ & _ & X2).
      unfold SLOT_STACK, SLOT_FRAME. lia2. }
  apply (rmid_widen B (API rc) CHECK_NO_LOSS_K (slot_sp E)); [exact HM3|rewrite p2_cnl_k; unfold SLOT_STACK, SLOT_FRAME; lia2
    |lia2|exact HKc|lia2| | |exact RC1].
  - intros a Ha. apply SCu. unfold sk. left. exact Ha.
  - intros a Ha HE. destruct (ECL a HE); lia2.
Qed.

Lemma s3_Rt : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E)
  (fun a => ((Es0 a \/ Ed a) \/ 0x318fc <= a < 0x31900) \/ Ec a)
  (fun q => ((False \/ In q TF0) \/ False) \/ In q (hs_blocks h2)) L A mem md L3 A3 mem4 md4.
Proof.
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ L A mem md L A m1 md L2 A2 mem2 md2 HWF b_R0 s1_RDw) as R01.
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ L A mem md L2 A2 mem2 md2 L2 A2 m3 md2 HWF R01 s2_Ru) as R012.
  exact (rmid_seq B (API rc) _ _ _ _ _ _ L A mem md L2 A2 m3 md2 L3 A3 mem4 md4 HWF R012 s3_Rcw).
Qed.

Lemma s3_Rum : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) (fun a => 0x318fc <= a < 0x31900 \/ Ec a)
  (fun q => False \/ In q (hs_blocks h2)) L2 A2 mem2 md2 L3 A3 mem4 md4.
Proof.
  pose proof s1_RDw as (_ & HWF2 & _).
  exact (rmid_seq B (API rc) _ _ _ _ _ _ L2 A2 mem2 md2 L2 A2 m3 md2 L3 A3 mem4 md4 HWF2 s2_Ru s3_Rcw).
Qed.

Lemma s3_KX : forall x m a, In (x, m) (blocks L A) -> ~ In x TA0 -> x <= a < x + m ->
  ~ (((Es0 a \/ Ed a) \/ 0x318fc <= a < 0x31900) \/ Ec a).
Proof.
  p2d_base. pose proof b_EDB as EDB. pose proof s1_OLD as OLD. pose proof s1_RDw as (HM2 & _).
  intros x m a Hx NT Ha.
  destruct (p2_blk rc fx B (API rc) L A mem md x m (a - x) FA HMR Hx ltac:(lia2)) as (NIa & B0 & B1).
  replace (x + (a - x)) with a in NIa by lia2.
  intros [[[X|X]|X]|X].
  - destruct X as [X|X]; [lia2|]. apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(lia2)))).
  - destruct (EDB a X) as [HI|(_ & _ & v & n & Hv & Hvt & Hva)]; [exact (NIa HI)|].
    assert (NE : x <> v) by (intros <-; exact (NT Hvt)).
    destruct (blocks_disjoint B (API rc) L A mem md x m v n HMR Hx Hv NE); lia2.
  - apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(lia2)))).
  - destruct X as [X|[X|(v & n & Hv & Hvh & Hva)]].
    + apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(lia2)))).
    + lia2.
    + destruct (OLD x m Hx ltac:(lia2) NT) as (Hx2 & NH2 & _).
      assert (NE : x <> v) by (intros <-; exact (NH2 Hvh)).
      destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 x m v n HM2 Hx2 Hv NE); lia2.
Qed.

Lemma s3_KF : forall x m, In (x, m) (blocks L A) -> 0 < m -> ~ In x TA0 ->
  ~ (((False \/ In x TF0) \/ False) \/ In x (hs_blocks h2)).
Proof.
  intros x m Hx Hm NT [[[[]|X]|[]]|X].
  - apply NT. destruct X as [<-|X]; [left; reflexivity|right; right; exact X].
  - exact (proj1 (proj2 (s1_OLD x m Hx Hm NT)) X).
Qed.

Lemma s3_KBt : forall q, ~ In q TA0 -> (exists m, 0 < m /\ In (q, m) (blocks L A)) ->
  kept_block (fun a => ((Es0 a \/ Ed a) \/ 0x318fc <= a < 0x31900) \/ Ec a)
    (fun q => ((False \/ In q TF0) \/ False) \/ In q (hs_blocks h2)) L A q.
Proof.
  intros q NT (m & Hm & Hq). split; [exact (s3_KF q m Hq Hm NT)|].
  intros k a Hkb Ha. exact (s3_KX q k (q + a) Hkb NT ltac:(lia)).
Qed.

Lemma s3_KSL : forall p k, In p (firstn i hj ++ skipn (S i) hj) -> (snd p < 4)%nat -> 0 <= k < 96 ->
  img_plain B (G_S + SRC_SIZE * Z.of_nat (snd p) + k) /\
  ~ (((Es0 (G_S + SRC_SIZE * Z.of_nat (snd p) + k) \/ Ed (G_S + SRC_SIZE * Z.of_nat (snd p) + k)) \/
      0x318fc <= G_S + SRC_SIZE * Z.of_nat (snd p) + k < 0x31900) \/ Ec (G_S + SRC_SIZE * Z.of_nat (snd p) + k)).
Proof.
  p2d_base. pose proof b_EDI as EDI. pose proof s1_RDw as (HM2 & _).
  intros p k Hp H4 Hk1. pose proof (b_NJ p Hp) as NE.
  assert (PE : G_S + SRC_SIZE * Z.of_nat (snd p) + k = 0x31920 + 96 * Z.of_nat (snd p) + k) by reflexivity.
  rewrite PE.
  assert (HG : in_globals G_reply (0x31920 + 96 * Z.of_nat (snd p) + k)) by (apply in_G_bss; clear - H4 Hk1; lia).
  assert (NE' : Z.of_nat (snd p) <> Z.of_nat jj) by (intros X; apply NE; lia).
  split; [exact (PL _ HG)|]. intros [[[X|X]|X]|X].
  - destruct X as [X|X]; lia2.
  - destruct (EDI _ X (proj1 (PL _ HG))) as [Y|[Y|[Y|Y]]]; ugl_in Y; clear - Y NE' H4 Hk1 HAe; lia.
  - clear - X H4 Hk1. lia.
  - destruct X as [X|[X|(v & n & Hv & _ & Hva)]].
    + clear - X NE' H4 Hk1 HAe. lia.
    + lia2.
    + destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (0x31920 + 96 * Z.of_nat (snd p) + k - v) FA HM2 Hv
        ltac:(lia2)) as (NIa & _). apply NIa. replace (v + (0x31920 + 96 * Z.of_nat (snd p) + k - v))
        with (0x31920 + 96 * Z.of_nat (snd p) + k) by lia2. exact (proj1 (PL _ HG)).
Qed.

Lemma s3_KPE : forall l, (forall q, In q (concat (map entry_blocks l)) -> In q (p2_oth es hj i)) ->
  Forall (CF.RelayRep.entry_ok (rc := rc) B L A mem) l ->
  forall q, In q (concat (map entry_blocks l)) ->
  kept_block (fun a => ((Es0 a \/ Ed a) \/ 0x318fc <= a < 0x31900) \/ Ec a)
    (fun q => ((False \/ In q TF0) \/ False) \/ In q (hs_blocks h2)) L A q.
Proof.
  intros l HO EL q Hq. apply s3_KBt; [exact (proj1 (b_OTX q (HO q Hq)))|].
  apply in_concat in Hq. destruct Hq as (l0 & Hl & Hql). apply in_map_iff in Hl. destruct Hl as (e0 & <- & He0).
  rewrite Forall_forall in EL. exact (p2_eb_pos rc B L A mem e0 (EL e0 He0) q Hql).
Qed.

Lemma s3_KPH : forall l hl, (forall q, In q (concat (map (fun p => hs_blocks (fst p)) hl)) -> In q (p2_oth es hj i)) ->
  Forall2 (pair_ok (rc := rc) B L A mem t) l hl ->
  forall q, In q (concat (map (fun p => hs_blocks (fst p)) hl)) ->
  kept_block (fun a => ((Es0 a \/ Ed a) \/ 0x318fc <= a < 0x31900) \/ Ec a)
    (fun q => ((False \/ In q TF0) \/ False) \/ In q (hs_blocks h2)) L A q.
Proof.
  intros l hl HO PF2 q Hq. apply s3_KBt; [exact (proj1 (b_OTX q (HO q Hq)))|].
  apply in_concat in Hq. destruct Hq as (l0 & Hl & Hql). apply in_map_iff in Hl. destruct Hl as (p & <- & Hp).
  destruct (pair_find _ _ _ _ _ p PF2 Hp) as [e0 (S0 & _)]. cbv zeta in S0.
  exact (p2_hb_pos rc B L A mem _ (fst p) S0 q Hql).
Qed.

Lemma s3_KSP : forall l hl, (forall p, In p hl -> In p (firstn i hj ++ skipn (S i) hj)) ->
  Forall2 (pair_ok (rc := rc) B L A mem t) l hl ->
  forall p k, In p hl -> 0 <= k < 96 ->
  img_plain B (G_S + SRC_SIZE * Z.of_nat (snd p) + k) /\
  ~ (((Es0 (G_S + SRC_SIZE * Z.of_nat (snd p) + k) \/ Ed (G_S + SRC_SIZE * Z.of_nat (snd p) + k)) \/
      0x318fc <= G_S + SRC_SIZE * Z.of_nat (snd p) + k < 0x31900) \/ Ec (G_S + SRC_SIZE * Z.of_nat (snd p) + k)).
Proof.
  intros l hl HI PF2 p k Hp Hk1. destruct (pair_find _ _ _ _ _ p PF2 Hp) as [e0 (_ & J4 & _)].
  exact (s3_KSL p k (HI p Hp) J4 Hk1).
Qed.

Lemma s3_KE2 : forall q, In q (entry_blocks e2) ->
  kept_block (fun a => 0x318fc <= a < 0x31900 \/ Ec a) (fun q => False \/ In q (hs_blocks h2)) L2 A2 q.
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  intros q Hq. split; [intros [[]|X]; exact (DEH q Hq X)|]. intros k a Hkb Ha HE.
  destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 q k a FA HM2 Hkb Ha) as (NIa & B0 & B1).
  destruct HE as [X|[X|[X|(v & n & Hv & Hvh & Hva)]]].
  - apply NIa. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(lia2)))).
  - apply NIa. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(lia2)))).
  - lia2.
  - assert (NE : q <> v) by (intros <-; exact (DEH q Hq Hvh)).
    destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 q k v n HM2 Hkb Hv NE); lia2.
Qed.

Lemma s3_LE3S : forall x, In x (list_blocks E3) -> In x (list_blocks (hs_expected h2)).
Proof.
  intros x Hx. unfold list_blocks in Hx |- *. rewrite E3R, E3C, E3V in Hx. cbn [map] in Hx. rewrite app_nil_r in Hx.
  apply in_or_app. left. exact Hx.
Qed.

Lemma s3_HB3 : forall x, In x (hs_blocks h3) -> In x (hs_blocks h2) \/ In x (list_blocks H3).
Proof.
  intros x Hx. unfold h3, hs_blocks in Hx. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held] in Hx.
  apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [left; apply p2_hb_pend; exact Hx|].
  apply in_app_or in Hx. destruct Hx as [[<-|[]]|Hx]; [left; apply p2_hb_part|].
  apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [left; apply p2_hb_exp, s3_LE3S; exact Hx|right; exact Hx].
Qed.

Lemma s3_HB23 : forall x, In x (hs_blocks h2) ->
  ~ In x (map fst (hl_recs (hs_expected h2)) ++ list_blocks (hs_held h2)) -> In x (hs_blocks h3).
Proof.
  intros x Hx NR. unfold h3, hs_blocks. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
  unfold hs_blocks in Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx|].
  apply in_or_app; right. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx|].
  apply in_or_app; right. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
  - apply in_or_app; left. unfold list_blocks in Hx |- *. rewrite E3R, E3C, E3V. cbn [map]. rewrite app_nil_r.
    apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact Hx|]. exfalso. apply NR. apply in_or_app. left. exact Hx.
  - exfalso. apply NR. apply in_or_app. right. exact Hx.
Qed.

Lemma s3_NH3M : forall x m, In (x, m) (blocks L2 A2) -> 0 < m -> ~ In x (hs_blocks h2) -> ~ In x (hs_blocks h3).
Proof.
  intros x m Hx Hm NX HX. destruct (s3_HB3 x HX) as [Y|Y]; [exact (NX Y)|]. apply (NEW3 x m Hx Hm); [|exact Y].
  intros HR. apply NX. apply in_app_or in HR. destruct HR as [HR|HR]; [apply p2_hb_exp, p2_lb_recs; exact HR|].
  apply p2_hb_held. exact HR.
Qed.

Lemma s3_KN2 : forall q k x, In (q, k) (blocks L2 A2) -> ~ In q (hs_blocks h2) -> q <= x < q + k ->
  ~ (0x318fc <= x < 0x31900 \/ Ec x).
Proof.
  p2d_base. pose proof s1_RDw as (HM2 & _).
  intros q k x Hq NQ Hx. destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 q k (x - q) FA HM2 Hq ltac:(lia2))
    as (NIa & B0 & B1). replace (q + (x - q)) with x in NIa by lia2.
  intros [X|[X|[X|(v & n & Hv & Hvh & Hva)]]].
  - apply NIa. exact (proj1 (PL _ (in_G_bss x ltac:(lia2)))).
  - apply NIa. exact (proj1 (PL _ (in_G_bss x ltac:(lia2)))).
  - lia2.
  - assert (NE : q <> v) by (intros <-; exact (NQ Hvh)).
    destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 q k v n HM2 Hq Hv NE); lia2.
Qed.

Lemma s3_TG : forall a cs, rw_cells (ms_segs B) mem a cs ->
  (forall k, 0 <= k < Z.of_nat (cells_size cs) -> in_globals G_reply (a + k) /\ ~ (G_BROKEN <= a + k < G_BROKEN + 1) /\
     ~ (G_EINTR <= a + k < G_EINTR + 1) /\ ~ (G_OUTV + 8 <= a + k < G_OUTV + 32) /\
     ~ (HA + 12 <= a + k < HA + SRC_SIZE) /\ ~ (0x318fc <= a + k < 0x31900)) ->
  rw_cells (ms_segs B) mem4 a cs.
Proof.
  p2d_base. pose proof b_EDI as EDI. pose proof s1_RDw as (HM2 & _).
  intros a cs H D. apply (rmid_rw_img B (API rc) AX _ _ _ _ L A mem md L3 A3 mem4 md4 a cs (hg_img_low B SEG) HKc HMR
    s3_Rt H).
  intros k Hk1. destruct (D k Hk1) as (HG & N1 & N2 & N3 & N4 & N5). pose proof (proj1 (PL _ HG)) as HI.
  pose proof (in_img_low B SEG _ HI) as LOW. split; [exact (PL _ HG)|]. intros [[[X|X]|X]|X].
  - destruct X as [X|X]; [lia2|exact (N5 X)].
  - destruct (EDI _ X HI) as [Y|[Y|[Y|Y]]]; contradiction.
  - exact (N5 X).
  - destruct X as [X|[X|(v & n & Hv & _ & Hva)]]; [apply N4; lia2|lia2|].
    destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a + k - v) FA HM2 Hv ltac:(lia2)) as (NIa & _).
    apply NIa. replace (v + (a + k - v)) with (a + k) by lia2. exact HI.
Qed.

Lemma s3_TC3 : forall a cs, rw_cells (ms_segs B) m3 a cs ->
  (forall k, 0 <= k < Z.of_nat (cells_size cs) -> in_globals G_reply (a + k) /\ ~ (HA + 64 <= a + k < HA + 96)) ->
  rw_cells (ms_segs B) mem4 a cs.
Proof.
  p2d_base. pose proof s2_Ru as (HM3 & _).
  intros a cs H D. apply (rmid_rw_img B (API rc) AX _ _ _ _ L2 A2 m3 md2 L3 A3 mem4 md4 a cs (hg_img_low B SEG) HKc HM3
    s3_Rcw H).
  intros k Hk1. destruct (D k Hk1) as (HG & N1). pose proof (proj1 (PL _ HG)) as HI. pose proof (in_img_low B SEG _ HI) as LOW.
  split; [exact (PL _ HG)|]. intros [X|[X|(v & n & Hv & _ & Hva)]]; [exact (N1 X)|lia2|].
  destruct (p2_blk rc fx B (API rc) L2 A2 m3 md2 v n (a + k - v) FA HM3 Hv ltac:(lia2)) as (NIa & _).
  apply NIa. replace (v + (a + k - v)) with (a + k) by lia2. exact HI.
Qed.

Lemma s3_GL4 : globals_at B mem4 cl (if send_off cl br TOT then br else dd) gn dd (if send_off cl br TOT then ei else 0)
    (Z.of_nat (length es)) G nfd mx (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
    (if live then Z_to_bv 64 CAP2 else cap) (if live then Z_to_bv 64 OUT2 else out).
Proof.
  p2d_base. pose proof s3_TG as TG. pose proof s3_TC3 as TC3. pose proof s2_TM3 as TM3.
  unfold globals_at.
  split.
  { apply TG; [exact G1|]. intros k Hk1. cbn in Hk1. split; [apply g9_in_listen; ugl; lia2|].
    ugl. repeat split; lia2. }
  split; [apply TG; [exact G2|]; p2d_g|].
  split; [apply TG; [exact G3|]; p2d_g|].
  split.
  { apply TC3; [apply TM3; [exact GBR2|cbn; ugl; lia2]|].
    intros k Hk1. cbn in Hk1. split; [apply in_G_bss; ugl; lia2|]. ugl. lia2. }
  split; [apply TG; [exact G5|]; p2d_g|].
  split; [apply TG; [exact G6|]; p2d_g|].
  split.
  { apply TC3; [apply TM3; [exact GEI2|cbn; ugl; lia2]|].
    intros k Hk1. cbn in Hk1. split; [apply in_G_bss; ugl; lia2|]. ugl. lia2. }
  split; [apply TG; [exact G8|]; p2d_g|].
  split; [apply TG; [exact G9|]; p2d_g|].
  split; [apply TG; [exact G10|]; p2d_g|].
  split.
  { apply TC3; [exact s2_GOV3|]. intros k Hk1. cbn in Hk1. split; [apply in_G_bss; ugl; lia2|].
    ugl. lia2. }
  split.
  { pose proof CK3 as CK3'. rewrite <- SEG in CK3'. apply TC3; [exact CK3'|]. intros k Hk1. cbn in Hk1. ugl.
    split; [apply in_G_bss; clear - Hk1; lia|]. clear - Hk1 HAB. lia. }
  split; [apply TG; [exact G13|]; p2d_g|].
  split; [destruct (entry_errno_cells B SEG ETP EOFF mem4) as [ev EV]; exists ev; rewrite SEG; exact EV|].
  split; [exact HCL|]. split; [destruct (send_off cl br TOT); [exact HBR|exact HDD]|]. split; [exact HGN|].
  split; [exact HDD|]. split; [destruct (send_off cl br TOT); [exact HEI|left; reflexivity]|].
  split; [|exact HMX].
  destruct (send_off cl br TOT) eqn:SO; [exact HGG|]. destruct HGG as [HG0 HG1].
  split; [intros X; destruct (HG0 X) as (Y1 & Y2 & Y3); split; [exact Y1|]; split; [exact Y3|exact Y3]|].
  intros X. destruct (HG1 X) as [Y|[Y|Y]]; [left; exact Y| |right; right; exact Y].
  exfalso. unfold send_off in SO. apply orb_false_iff in SO. destruct SO as [SO _]. apply orb_false_iff in SO.
  destruct SO as [_ SO]. rewrite Y in SO. discriminate.
Qed.

Lemma s3_OUT4 : output_at (rc := rc) B L3 A3 mem4 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
    (if live then Z_to_bv 64 CAP2 else cap) (if live then Z_to_bv 64 OUT2 else out).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof s3_Rum as Rum. pose proof s3_KN2 as KN2. pose proof s1_TOTP as TOTP.
  pose proof s1_CBL as CBL.
  destruct (Sumbool.sumbool_of_bool live) as [LV|LV]; rewrite LV.
  - pose proof (LV1 LV) as (TL1 & CAPF & INO & FRO & BYO & JL & _).
    specialize (TOTP LV). specialize (CBL LV).
    pose proof FRO as (FR1 & FR2 & FR3).
    assert (NOE : bv_unsigned (Z_to_bv 64 (bv_unsigned nout + TOT)) = TOT).
    { assert (T26 : TOT < 2 ^ 26) by exact TOT26. rewrite HNO. apply unsigned_lit. clear - T26 TOTP. lia. }
    assert (CAE : bv_unsigned (Z_to_bv 64 CAP2) = CAP2)
      by (apply unsigned_lit; clear - CBL TL1 TOTP HNO; unfold TBBYTES in *; lia).
    assert (OUE : bv_unsigned (Z_to_bv 64 OUT2) = OUT2) by (apply unsigned_lit; clear - FR1 FR2 ACL TL1 TOTP HNO; lia).
    assert (NFO : ~ (False \/ In OUT2 (hs_blocks h2))) by (intros [[]|X]; apply NOL; apply in_or_app; right; exact X).
    unfold output_at. cbv zeta. rewrite NOE, CAE, OUE. split; [|exact CBL]. exists LB, junk2. right.
    rewrite O0 in BYO. cbn [app] in BYO. pose proof (with_nul_bzs Ls LB LBE) as LBL.
    split; [clear - TL1 TOTP HNO; lia|]. split; [clear - TL1 HNO; lia|].
    split.
    { exact (proj1 (rmid_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 OUT2 CAP2 0 Rum INO
        ltac:(clear - TL1 TOTP HNO; lia) NFO ltac:(clear - TL1 TOTP HNO; lia)
        (KN2 OUT2 CAP2 (OUT2 + 0) INO (fun X => NOL (in_or_app _ _ _ (or_intror X))) ltac:(clear - TL1 TOTP HNO; lia)))). }
    split; [exact FRO|].
    split.
    { apply (rmid_bytes_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 OUT2 CAP2 OUT2 _ Rum INO
        ltac:(clear - TL1 TOTP HNO; lia) NFO BYO);
        [apply Z.le_refl|rewrite length_app; clear - LBL JL TOTP HNO; unfold TOT in *; lia|].
      intros k Hk1. rewrite length_app in Hk1.
      exact (KN2 OUT2 CAP2 (OUT2 + k) INO (fun X => NOL (in_or_app _ _ _ (or_intror X)))
        ltac:(clear - Hk1 LBL JL TOTP HNO; unfold TOT in *; lia)). }
    split; [exact LBL|]. clear - JL HNO. lia.
  - destruct (LV0 LV) as (_ & LV02 & LV03).
    unfold output_at. cbv zeta. split; [|exact CAPB]. exists O, junk.
    pose proof OC as [OCl|(C0 & C1' & C2' & C3' & C4' & C5' & C6')]; [left; exact OCl|right].
    destruct (LV02 C0) as (IN2 & BYO2).
    assert (NFO : ~ (False \/ In (bv_unsigned out) (hs_blocks h2))).
    { intros [[]|X]. apply NOL. rewrite LV03. apply in_or_app. right. exact X. }
    assert (NOH : ~ In (bv_unsigned out) (hs_blocks h2)) by (intros X; exact (NFO (or_intror X))).
    split; [exact C0|]. split; [exact C1'|].
    split; [exact (proj1 (rmid_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 _ _ 0 Rum IN2 C0 NFO
      ltac:(clear - C0; lia) (KN2 (bv_unsigned out) (bv_unsigned cap) (bv_unsigned out + 0) IN2 NOH
        ltac:(clear - C0; lia))))|].
    split; [exact C3'|].
    split; [|split; assumption].
    apply (rmid_bytes_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 _ _ _ _ Rum IN2 C0 NFO BYO2);
      [clear - C0; lia|rewrite length_app; clear - C5' C6'; lia|].
    intros k Hk1. rewrite length_app in Hk1.
    exact (KN2 (bv_unsigned out) (bv_unsigned cap) (bv_unsigned out + k) IN2 NOH ltac:(clear - Hk1 C5' C6'; lia)).
Qed.

Lemma s3_NDM : NoDup (G :: bv_unsigned (if live then Z_to_bv 64 OUT2 else out) :: entry_blocks e2 ++ hs_blocks h3).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof s3_NH3M as NH3M. pose proof s1_TOTP as TOTP. pose proof s3_Rcw as (HM4 & _).
  pose proof SRC4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDB4).
  rewrite DN2. apply NoDup_ListNoDup. apply NoDup_ListNoDup in NDB4.
  assert (DEH3 : forall q, In q (entry_blocks e2) -> ~ In q (hs_blocks h3)).
  { intros q Hq. destruct (p2_eb_pos rc B L2 A2 mem2 e2 EOK2 q Hq) as (m' & Hm' & Hq').
    exact (NH3M q m' Hq' Hm' (DEH q Hq)). }
  assert (NOH3 : ~ In OUT2 (hs_blocks h3)).
  { intros HX. destruct (p2_hb_pos rc B L3 A3 mem4 HA h3 SRC4 OUT2 HX) as (m' & Hm' & Hq').
    destruct (Sumbool.sumbool_of_bool live) as [LV|LV].
    - pose proof (LV1 LV) as (TL1 & _ & INO & _). specialize (TOTP LV).
      apply (NH3M OUT2 CAP2 INO); [|intros X; apply NOL; apply in_or_app; right; exact X|exact HX].
      clear - TL1 TOTP HNO. lia.
    - destruct (LV0 LV) as (_ & LV02 & LV03).
      pose proof OC as [(C0 & O0' & _)|(C0 & _)].
      + destruct (p2_blk rc fx B (API rc) L3 A3 mem4 md4 OUT2 m' 0 FA HM4 Hq' ltac:(clear - Hm'; lia)) as (_ & B0 & _).
        rewrite LV03, O0' in B0. clear - B0. lia.
      + destruct (LV02 C0) as (IN2 & _). rewrite LV03 in HX. apply (NH3M _ _ IN2 C0); [|exact HX].
        intros X. apply NOL. rewrite LV03. apply in_or_app. right. exact X. }
  constructor.
  - intros [EQ|X]; [exact (NG2 (eq_sym EQ))|]. apply in_app_or in X.
    destruct X as [X|X]; [exact (NGL (in_or_app _ _ _ (or_introl X)))|].
    exact (NH3M G 896 GIN2 ltac:(reflexivity) (fun Y => NGL (in_or_app _ _ _ (or_intror Y))) X).
  - constructor.
    + intros X. apply in_app_or in X. destruct X as [X|X]; [exact (NOL (in_or_app _ _ _ (or_introl X)))|exact (NOH3 X)].
    + apply (NoDup_count_occ Z.eq_dec). intros x. rewrite count_occ_app.
      pose proof (proj1 (NoDup_count_occ Z.eq_dec _) (proj1 (NoDup_ListNoDup _) NDE2) x) as C1.
      pose proof (proj1 (NoDup_count_occ Z.eq_dec _) NDB4 x) as C2.
      destruct (in_dec Z.eq_dec x (entry_blocks e2)) as [Y|Y].
      * pose proof (DEH3 x Y) as Y2. rewrite (count_occ_not_In Z.eq_dec) in Y2. lia.
      * rewrite (count_occ_not_In Z.eq_dec) in Y. lia.
Qed.

Lemma s3_KGE : forall a, G <= a < G + 896 -> ~ (SA <= a < SA + SRC_ENTRY) ->
  ~ (((Es0 a \/ Ed a) \/ 0x318fc <= a < 0x31900) \/ Ec a).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. pose proof b_GNT as GNT. pose proof s3_KN2 as KN2.
  assert (NGH2 : ~ In G (hs_blocks h2)) by (intros X; apply NGL; apply in_or_app; right; exact X).
  intros a Ha NSA. destruct (p2_blk rc fx B (API rc) L A mem md G 896 (a - G) FA HMR GIN ltac:(clear - Ha; lia))
    as (NIa & B0 & B1). replace (G + (a - G)) with a in NIa by (clear; lia).
  intros [[[X|X]|X]|X].
  - destruct X as [X|X]; [clear - X B1 SPB1 Ha; lia|apply NIa; exact (proj1 (PL _ (in_G_bss a ltac:(clear - X; lia))))].
  - destruct X as [X|[X|[X|[X|[X|(v & n & Hv & Hvt & Hva)]]]]];
      try (apply NIa; apply (proj1 (PL a ltac:(apply in_G_bss; ugl_in X; clear - X HAB SSe; lia)))).
    + exact (NSA X).
    + assert (NE : G <> v) by (intros <-; exact (GNT Hvt)).
      destruct (blocks_disjoint B (API rc) L A mem md G 896 v n HMR GIN Hv NE) as [DJ|DJ]; clear - Ha Hva DJ; lia.
  - apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(clear - X; lia)))).
  - exact (KN2 G 896 a GIN2 NGH2 Ha (or_intror X)).
Qed.

Lemma s3_GIN3 : In (G, SRC_TABLE) (blocks L3 A3).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. pose proof s3_KN2 as KN2.
  assert (NGH2 : ~ In G (hs_blocks h2)) by (intros X; apply NGL; apply in_or_app; right; exact X).
  exact (proj1 (rmid_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 G SRC_TABLE 0 s3_Rum GIN2
    ltac:(reflexivity) (fun X => match X with or_introl F => F | or_intror Y => NGH2 Y end)
    ltac:(unfold SRC_TABLE, SRC_ENTRY; clear; lia)
    (KN2 G SRC_TABLE (G + 0) GIN2 NGH2 ltac:(unfold SRC_TABLE, SRC_ENTRY; clear; lia)))).
Qed.

Lemma s3_PAI : forall e3, p2_sbs e2 e3 -> pair_ok (rc := rc) B L3 A3 mem4 (t + 1) e3 (h3, jj).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof SB1 as (SF1 & SE1 & SS1 & SP1 & SBU1 & SU1 & SC1' & SH1 & SKH1 & SP2 & SK1 & SUU1 & SJ1).
  intros e3 SB3.
  pose proof SB3 as (S31 & S32 & S33 & _ & _ & _ & _ & _ & _ & _ & S311 & S312 & _).
  unfold pair_ok. cbv zeta. cbn [fst snd]. split; [exact SRC4|]. split; [exact JJ4|].
  split; [unfold h3; cbn; rewrite S31, FD2, SF1, HFD2; exact FDH|].
  split; [intros _; unfold h3; cbn; rewrite S33, S312; split; [exact SKO2|exact WU2]|].
  split.
  { rewrite (p2_sbs_texts e2 e3 SB3). unfold h3; cbn [set_exp_held hs_held]. rewrite H3T, HHL2.
    rewrite (texts_lines (hs_expected h2) Ls ltac:(rewrite HEX2, EXP0; reflexivity) (dc_lines_range h)).
    pose proof SSK2 as SSK2e. rewrite (p2_sbs_texts e e1 SB1) in SSK2e.
    exact (same_set_trans _ _ _ SSK2e (upds_same_set Ls _ _ SSK)). }
  split; [exact NDH3|]. split; [exact E3R|].
  unfold h3; cbn [set_exp_held hs_pending hs_expected hs_held].
  split; [unfold hl_n; rewrite HPR2; cbn; clear - Ht; lia|].
  split; [rewrite HPC2; clear - PC Ht; lia|].
  split; [unfold pending_stream; cbn [hs_pending set_exp_held]; rewrite HPR2; cbn; clear - Ht; unfold WRITE_MAX; lia|].
  split; [rewrite E3C, DC6; exact ECF|].
  pose proof H3C as H3C'. rewrite HHL2 in HB22, H3C'. clear - H3C' HC HB22. lia.
Qed.

Section S4.
Variables (pre' post' : list rentry) (e3 : rentry).
Hypothesis SBpre : Forall2 p2_sbs (firstn i es) pre'.
Hypothesis EOpre : Forall (CF.RelayRep.entry_ok (rc := rc) B L3 A3 mem4) pre'.
Hypothesis PApre' : Forall2 (pair_ok (rc := rc) B L3 A3 mem4 t) pre' (firstn i hj).
Hypothesis SBpost : Forall2 p2_sbs (skipn (S i) es) post'.
Hypothesis EOpost : Forall (CF.RelayRep.entry_ok (rc := rc) B L3 A3 mem4) post'.
Hypothesis PApost' : Forall2 (pair_ok (rc := rc) B L3 A3 mem4 t) post' (skipn (S i) hj).
Hypothesis SB3 : p2_sbs e2 e3.
Hypothesis EOK3 : CF.RelayRep.entry_ok (rc := rc) B L3 A3 mem4 e3.

Ltac p2d_s4 IL IHJ :=
  destruct (p2_sbs_maps _ _ SBpre) as (M1pre & M2pre & M3pre & LPRE0);
  rewrite (p2_len_firstn es i IL) in LPRE0;
  destruct (p2_sbs_maps _ _ SBpost) as (M1post & M2post & M3post & LPOST0);
  destruct (p2_repl_facts post' pre' i e3 LPRE0) as (_ & _ & NE3);
  destruct (p2_repl_facts (skipn (S i) hj) (firstn i hj) i (h3, jj) (p2_len_firstn hj i IHJ)) as (_ & _ & NH3);
  pose proof (p2_oth_repl es hj i pre' post' e3 (h3, jj) IL IHJ SBpre SBpost) as OTHEQ;
  pose proof (p2_sbs_blocks e2 e3 SB3) as ENB3.

Lemma s4_LEN : length (pre' ++ e3 :: post') = length es.
Proof.
  p2d_base. p2d_s4 IL IHJ. rewrite ESP. rewrite !length_app. cbn [length].
  rewrite (p2_len_firstn es i IL). clear - LPOST0 LPRE0. lia.
Qed.

Lemma s4_KEPT : image_kept (rc := rc) B E mem4 /\ stack_mid B E mem4 /\
  driver_kept B E (target_addrs G (bv_unsigned (if live then Z_to_bv 64 OUT2 else out)) (pre' ++ e3 :: post')
    (firstn i hj ++ (h3, jj) :: skipn (S i) hj)) L3 A3 mem4.
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. p2d_s4 IL IHJ.
  pose proof b_EDB as EDB. pose proof b_EDI as EDI. pose proof b_EDH as EDH.
  pose proof s1_OLD as OLD. pose proof b_TA0S as TA0S. pose proof b_OTX as OTX.
  pose proof s3_HB3 as HB3. pose proof s3_HB23 as HB23.
  pose proof s3_AT3 as AT3. pose proof AT4 as AT4'. rewrite AT3 in AT4'.
  pose proof s2_SRC3 as SRC3.
  pose proof SRC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE3 & LH3 & _).
  apply (p2_kept B API LS SH SK ra empty rc fx j E CS L A mem md L3 A3 mem4 md4 _ _
    (target_addrs G (bv_unsigned out) es hj) _ HF HMR HWF HIK HST HDK s3_Rt).
  - intros a [[[X|X]|X]|X].
    + destruct X as [X|X]; [right; left; lia2|left; apply in_G_bss; lia2].
    + destruct (EDB a X) as [HI|(XA & NIa & v & n & Hv & Hvt & Hva)].
      * left. destruct (EDI a X HI) as [Y|[Y|[Y|Y]]]; apply in_G_bss; ugl_in Y; clear - Y HAB SSe; lia.
      * exact (p2_es_blk rc fx B (API rc) (slot_sp E) _ L A mem md v n a FA HMR Hv (TA0S v Hvt) Hva).
    + left. apply in_G_bss. lia2.
    + destruct X as [X|[X|(v & n & Hv & Hvh & Hva)]].
      * left. apply in_G_bss. clear - X HAB. lia.
      * right. left. lia2.
      * right. right. destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a - v) FA HM2 Hv ltac:(lia2))
          as (NIa & B0 & B1).
        replace (v + (a - v)) with a in NIa by lia2. split; [lia2|]. split; [exact NIa|].
        intros x m Hx NT. destruct (Z_le_gt_dec m 0) as [M0|M0]; [lia2|].
        destruct (OLD x m Hx ltac:(lia2) (fun Y => NT (TA0S x Y))) as (Hx2 & NH2 & _).
        assert (NE : x <> v) by (intros <-; exact (NH2 Hvh)).
        destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 x m v n HM2 Hx2 Hv NE); lia2.
  - intros a Ha. destruct (Z_lt_le_dec a (slot_sp E + 40)) as [La|La];
      [left|destruct (Z_lt_le_dec a (slot_sp E + 48)) as [Lb|Lb]].
    + intros [[[X|X]|X]|X].
      * destruct X as [X|X]; lia2.
      * pose proof (EDH a X). lia2.
      * lia2.
      * destruct X as [X|[X|(v & n & Hv & _ & Hva)]]; [lia2|lia2|].
        destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a - v) FA HM2 Hv ltac:(lia2)) as (_ & _ & B1). lia2.
    + right. eapply cells_writable; [exact AT4'|cbn; lia2].
    + left. intros [[[X|X]|X]|X].
      * destruct X as [X|X]; lia2.
      * pose proof (EDH a X). lia2.
      * lia2.
      * destruct X as [X|[X|(v & n & Hv & _ & Hva)]]; [lia2|lia2|].
        destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a - v) FA HM2 Hv ltac:(lia2)) as (_ & _ & B1). lia2.
  - intros q [[[[]|X]|[]]|X] x m Hx Hm NT <-.
    + apply NT. apply TA0S. destruct X as [<-|X]; [left; reflexivity|right; right; exact X].
    + exact (proj1 (proj2 (OLD q m Hx Hm (fun Y => NT (TA0S q Y)))) X).
  - intros x Hx. destruct (p2_TA_cases G _ _ _ i e3 h3 jj x NE3 NH3 Hx) as [HM|HO'].
    + destruct HM as [<-|[<-|HM]].
      * left. left. reflexivity.
      * right. rewrite DN2. intros q m Hq Hm NT. exact (proj2 (proj2 (proj2 (OLD q m Hq Hm (fun Y => NT (TA0S q Y)))))).
      * right. intros q m Hq Hm NT. destruct (OLD q m Hq Hm (fun Y => NT (TA0S q Y))) as (Hq2 & NH2q & NE2q & _).
        apply in_app_or in HM. intros <-. destruct HM as [HM|HM]; [rewrite ENB3 in HM; exact (NE2q HM)|].
        destruct (HB3 q HM) as [Y|Y]; [exact (NH2q Y)|]. apply (NEW3 q m Hq2 Hm); [|exact Y].
        intros HR. apply NH2q. apply in_app_or in HR. destruct HR as [HR|HR]; [apply p2_hb_exp, p2_lb_recs; exact HR|].
        apply p2_hb_held. exact HR.
    + left. rewrite OTHEQ in HO'. exact (proj2 (OTX x HO')).
  - intros q m Hq. destruct (BL3 q m Hq) as [(Hq2 & NR)|HH3].
    + destruct (BL2 q m Hq2) as [(Hq1 & NOq & NEq & NHq)|[HEH|HO]].
      * destruct (in_dec Z.eq_dec q (target_addrs G (bv_unsigned out) es hj)) as [IT|NIT]; [right|left; split; assumption].
        destruct (p2_TA_cases G (bv_unsigned out) es hj i e h jj q Hi Hh IT) as [HM|HO'].
        -- destruct HM as [<-|[<-|HM]]; [apply (p2_mid_in G _ _ _ i e3 h3 jj _ NE3 NH3); left; reflexivity
             |exfalso; exact (NOq eq_refl)|].
           exfalso. apply in_app_or in HM. destruct HM as [HM|HM]; [apply NEq; rewrite (p2_sbs_blocks e e1 SB1); exact HM
             |exact (NHq HM)].
        -- apply (p2_oth_in G _ _ _ i e3 h3 jj q NE3 NH3). rewrite OTHEQ. exact HO'.
      * right. apply (p2_mid_in G _ _ _ i e3 h3 jj q NE3 NH3). right; right. apply in_app_or in HEH.
        destruct HEH as [HEH|HEH]; apply in_or_app; [left; rewrite ENB3; exact HEH|right].
        apply HB23; [exact HEH|]. intros HR. destruct (Z_lt_le_dec 0 m) as [MP|MN]; [exact (NR MP HR)|].
        assert (HL2 : In q (list_blocks (hs_expected h2)) \/ In q (list_blocks (hs_held h2))).
        { apply in_app_or in HR. destruct HR as [HR|HR]; [left; apply p2_lb_recs; exact HR|right; exact HR]. }
        destruct HL2 as [HL2|HL2];
          [destruct (p2_lb_pos _ _ _ _ _ _ _ _ LE3 q HL2) as (m' & Hm' & Hq')
          |destruct (p2_lb_pos _ _ _ _ _ _ _ _ LH3 q HL2) as (m' & Hm' & Hq')];
          pose proof (p2_block_size rc fx B (API rc) L2 A2 mem2 md2 q m m' FA HM2 Hq2 Hq') as EQm; lia2.
      * right. apply (p2_mid_in G _ _ _ i e3 h3 jj q NE3 NH3). right; left. rewrite DN2. symmetry. exact HO.
    + right. apply (p2_mid_in G _ _ _ i e3 h3 jj q NE3 NH3). right; right. apply in_or_app; right.
      apply p2_hb_held. exact HH3.
Qed.

Lemma s4_TAB4 : exists tail, table_at B mem4 G (pre' ++ e3 :: post') tail.
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. p2d_s4 IL IHJ.
  pose proof s3_KGE as KGE. pose proof s3_KN2 as KN2. pose proof s3_Rum as Rum.
  pose proof s3_Rt as Rt. pose proof b_GNT as GNT.
  assert (NGH2 : ~ In G (hs_blocks h2)) by (intros X; apply NGL; apply in_or_app; right; exact X).
  assert (NFG : ~ (((False \/ In G TF0) \/ False) \/ In G (hs_blocks h2))).
  { intros [[[[]|X]|[]]|X]; [exact (GNT X)|exact (NGH2 X)]. }
  assert (FE4 : Forall (CF.RelayRep.entry_ok (rc := rc) B L3 A3 mem4) (pre' ++ e3 :: post')).
  { apply Forall_app. split; [exact EOpre|constructor; [exact EOK3|exact EOpost]]. }
  destruct TBL as (tail & TL & TB).
  pose proof (p2_table_split rc B L A mem es tail G i e HES Hi TL TB) as TS.
  exists tail. split; [rewrite s4_LEN; exact TL|].
  destruct (hg_cut _ _ _ [_] [_; _] TS) as [TC1 TS2']. destruct (hg_cut _ _ _ [_] [_] TS2') as [_ TC3'].
  cbn [cells_size csize] in TS2', TC3'.
  assert (TC1m := rmid_rw_block B (API rc) BW _ _ _ _ L A mem md L3 A3 mem4 md4 G 896 G _ Rt GIN ltac:(reflexivity) NFG TC1
    ltac:(clear - IL; lia) ltac:(cbn [cells_size csize]; clear - IL Hes; lia)
    (fun k Hk1 => KGE (G + k) ltac:(cbn [cells_size csize] in Hk1; clear - Hk1 IL Hes; lia)
                   ltac:(cbn [cells_size csize] in Hk1; rewrite SAe, SEe; clear - Hk1; lia))).
  set (a3 := G + Z.of_nat (56 * i + 0) + Z.of_nat (56 + 0)) in TC3'.
  assert (A3E : a3 = G + 56 * Z.of_nat i + 56) by (unfold a3; clear; lia).
  assert (C3E : Z.of_nat (cells_size [CB (896 - 56 * S i) (concat (map entry_bytes (skipn (S i) es)) ++ tail)]) =
    896 - 56 * Z.of_nat (S i)) by (cbn [cells_size csize]; clear - IL Hes; lia).
  assert (TC3m : rw_cells (ms_segs B) mem4 a3
      [CB (896 - 56 * S i) (concat (map entry_bytes (skipn (S i) es)) ++ tail)]).
  { apply (rmid_rw_block B (API rc) BW _ _ _ _ L A mem md L3 A3 mem4 md4 G 896 a3 _ Rt GIN ltac:(reflexivity) NFG TC3').
    - rewrite A3E. clear. lia.
    - rewrite C3E, A3E. clear - IL Hes. lia.
    - intros k Hk1. rewrite C3E in Hk1. apply KGE.
      + rewrite A3E. clear - Hk1 IL Hes. lia.
      + rewrite A3E, SAe, SEe. clear - Hk1. lia. }
  assert (TM2 : rw_cells (ms_segs B) mem4 (G + Z.of_nat (56 * i + 0)) [CB 56 (entry_bytes e2)]).
  { replace (G + Z.of_nat (56 * i + 0)) with SA by (rewrite SAe; clear - IL; lia).
    pose proof SA2 as SA2'.
    replace (bv_unsigned (PropExec.getr R 10)) with SA in SA2' by (symmetry; exact HSA).
    apply (rmid_rw_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 G 896 SA _ Rum GIN2 ltac:(reflexivity)
      (fun X => match X with or_introl F => F | or_intror Y => NGH2 Y end) SA2');
      [rewrite SAe; clear - IL; lia|cbn [cells_size csize]; rewrite SAe; clear - IL Hes; lia|].
    intros k Hk1. cbn [cells_size csize] in Hk1.
    exact (KN2 G 896 (SA + k) GIN2 NGH2 ltac:(rewrite SAe; clear - Hk1 IL Hes; lia)). }
  pose proof (hg_join _ _ _ _ _ _ TM2 TC3m ltac:(cbn [cells_size csize]; rewrite A3E; clear; lia)) as J23.
  pose proof (hg_join _ _ _ _ _ _ TC1m J23 ltac:(cbn [cells_size csize]; clear - IL; lia)) as J123.
  eapply rw_cells_retype; [exact J123| |].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_app, (p2_eb_len rc B L3 A3 mem4 _ FE4), s4_LEN.
    clear - TL. lia.
  - cbn [app cells_bytes cbytes]. rewrite map_app, concat_app. cbn [map concat].
    rewrite M2pre, M2post, (p2_sbs_bytes e2 e3 SB3), !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma s4_REL4 : relay_at (rc := rc) B L3 A3 mem4 (t + 1) nfd G (bv_unsigned (if live then Z_to_bv 64 OUT2 else out))
  (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. p2d_s4 IL IHJ.
  pose proof s3_NH3M as NH3M. pose proof s3_NDM as NDM. pose proof s3_TG as TG.
  pose proof b_OTX as OTX. pose proof b_OTHP as OTHP. pose proof s1_OLD as OLD. pose proof b_OPJ as OPJ.
  assert (FE4 : Forall (CF.RelayRep.entry_ok (rc := rc) B L3 A3 mem4) (pre' ++ e3 :: post')).
  { apply Forall_app. split; [exact EOpre|constructor; [exact EOK3|exact EOpost]]. }
  pose proof SB1 as (SF1 & _).
  assert (MFD : map re_fd (pre' ++ e3 :: post') = map re_fd es).
  { transitivity (map re_fd (firstn i es ++ e :: skipn (S i) es)); [|rewrite <- ESP; reflexivity].
    rewrite !map_app. cbn [map]. rewrite M3pre, M3post, (proj1 SB3), FD2, SF1. reflexivity. }
  assert (MSND : map snd (firstn i hj ++ (h3, jj) :: skipn (S i) hj) = map snd hj).
  { transitivity (map snd (firstn i hj ++ (h, jj) :: skipn (S i) hj)); [|rewrite <- HJP; reflexivity].
    rewrite !map_app. reflexivity. }
  unfold relay_at.
  split; [exact s4_TAB4|].
  split; [exact s3_GIN3|]. split; [exact GFR|]. split; [exact FE4|].
  split; [rewrite MFD; exact NDF|].
  split.
  { assert (FDR' : Forall (fun z => FIRST_FD <= z < FIRST_FD + nfd) (map re_fd es)) by (apply Forall_map; exact FDR).
    rewrite <- MFD in FDR'. apply Forall_map in FDR'. exact FDR'. }
  split.
  { apply Forall2_app; [|constructor; [exact (s3_PAI e3 SB3)|]].
    - eapply Forall2_impl; [|exact PApre']. intros e0 p0 H0. exact (pair_ok_t rc B L3 A3 mem4 t (t + 1) e0 p0 H0
        ltac:(clear - Ht; lia)).
    - eapply Forall2_impl; [|exact PApost']. intros e0 p0 H0. exact (pair_ok_t rc B L3 A3 mem4 t (t + 1) e0 p0 H0
        ltac:(clear - Ht; lia)). }
  split; [rewrite MSND; exact NDH|].
  split.
  { intros k Hk4 SO. assert (SO' : slot_open hj k = false) by (unfold slot_open in SO |- *; rewrite MSND in SO; exact SO).
    assert (KJ : k <> jj) by (intros ->; rewrite OPJ in SO'; discriminate).
    assert (KJ' : Z.of_nat k <> Z.of_nat jj) by (intros X; apply KJ; lia).
    apply TG; [exact (ZH k Hk4 SO')|]. intros k' Hk'. cbn in Hk'. ugl. ugs.
    split; [apply in_G_bss; clear - Hk' Hk4; lia|repeat split; clear - Hk' Hk4 KJ' HAe; lia]. }
  apply (p2_nd_join G _ _ _ i e3 h3 jj NE3 NH3); [rewrite ENB3; exact NDM
    |rewrite OTHEQ; exact (p2_oth_nd G (bv_unsigned out) es hj i e h jj NDA Hi Hh)|].
  intros x Hx. rewrite OTHEQ in Hx. destruct (OTX x Hx) as (NT & _). destruct (OTHP x Hx) as (m & Hm & Hxm).
  destruct (OLD x m Hxm Hm NT) as (Hx2 & NH2x & NE2x & NOx). intros [EQ|[EQ|X]].
  - apply NT. rewrite <- EQ. right; left; reflexivity.
  - rewrite DN2 in EQ. exact (NOx (eq_sym EQ)).
  - apply in_app_or in X. destruct X as [X|X]; [rewrite ENB3 in X; exact (NE2x X)|exact (NH3M x m Hx2 Hm NH2x X)].
Qed.

Lemma s4_COST4 : slot_cost (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj) <= K.
Proof.
  p2d_base. p2d_s4 IL IHJ.
  rewrite (p2_cost_app pre' (firstn i hj) e3 (h3, jj) post' (skipn (S i) hj)
    ltac:(rewrite LPRE0, (p2_len_firstn hj i IHJ); reflexivity)).
  rewrite (p2_cost_sbs _ _ _ SBpre), (p2_cost_sbs _ _ _ SBpost), (p2_sbs_cost e2 e3 (h3, jj) SB3).
  pose proof (p2_cost_app (firstn i es) (firstn i hj) e (h, jj) (skipn (S i) es) (skipn (S i) hj)
    ltac:(rewrite (p2_len_firstn es i IL), (p2_len_firstn hj i IHJ); reflexivity)) as CO.
  rewrite <- ESP, <- HJP in CO.
  pose proof EOK2 as (_ & _ & _ & _ & _ & _ & EUL2 & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV & _).
  pose proof SRC4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV4 & _).
  pose proof SSK2 as SSK2e. rewrite (p2_sbs_texts e e1 SB1) in SSK2e.
  pose proof (p2_pair_cost e e2 h h3 jj SKO WU HOV EUL SKO2 WU2 HOV4 EUL2 HST2 HPR2 NDK2 SSK2e) as PCC.
  clear - CO PCC Hcost. lia.
Qed.

Lemma s4_MV3 : nc_move (view_of G OUT2 es2 hj2) L2 A2
  (view_of G OUT2 (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj)) L3 A3
  (p2_arr_dels (hs_held h2) H3) (p2_arr_adds (hs_held h2) H3).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. p2d_s4 IL IHJ.
  pose proof s4_REL4 as REL4. rewrite DN2 in REL4.
  pose proof REL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ND4).
  destruct (p2_ta_nd _ _ _ _ (proj1 (NoDup_ListNoDup _) ND4)) as (NV3 & _).
  pose proof s3_Rcw as (HM4 & _).
  assert (NB3 : List.NoDup (map fst (blocks L3 A3))).
  { pose proof (NDB L3 A3 mem4 md4 HM4) as XN3. first [exact XN3|exact (proj1 (NoDup_ListNoDup _) XN3)]. }
  pose proof (CF.SlotPass4.p4_src_blk_of B L3 A3 mem4 HA h3 SRC4) as (_ & _ & _ & P3H & _).
  pose proof (CF.SlotPass4.p4_src_blk_of B L2 A2 mem2 HA h2 SRC2) as (_ & _ & _ & P2H & _).
  pose proof (proj1 (NoDup_ListNoDup _) s1_ND2T) as ND2Tl.
  destruct (p2_ta_nd _ _ _ _ ND2Tl) as (NV2 & NR2).
  apply (p2_cnl_mv L2 A2 L3 A3 G OUT2 es2 (pre' ++ e3 :: post') hj2 (firstn i hj ++ (h3, jj) :: skipn (S i) hj)
    (firstn i hj) (skipn (S i) hj) h2 h3 jj eq_refl eq_refl).
  - unfold es2. rewrite !map_app, !concat_app. cbn [map concat].
    rewrite (p2_sbs_cnc _ _ SBpre), (p2_sbs_cnc _ _ SBpost), (p2_sbs_enc _ _ SB3). reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold h3. cbn [set_exp_held hs_expected]. unfold arr_nc. rewrite E3V, E3C. reflexivity.
  - exact NB2.
  - exact NB3.
  - exact NV2.
  - exact NV3.
  - intros xq mq Hxq Hvq NAq. apply SURV3; [exact Hxq|]. intros HRq. apply in_app_or in HRq as [HRq|HRq].
    + apply (NR2 xq Hvq). apply (p2_rest_in es2 hj2 h2 jj xq (nth_error_In _ _ NH2i)). unfold p2_srecs.
      apply in_or_app; right; apply in_or_app; left; exact HRq.
    + unfold list_blocks in HRq. apply in_app_or in HRq as [HRq|HRq]; [exact (NAq HRq)|].
      apply (NR2 xq Hvq). apply (p2_rest_in es2 hj2 h2 jj xq (nth_error_In _ _ NH2i)). unfold p2_srecs.
      apply in_or_app; right; apply in_or_app; right; exact HRq.
  - exact (proj1 P2H).
  - exact (proj1 P3H).
  - intros xq mq Hqq. exact (p2_pos rc B (API rc) L2 A2 mem2 md2 xq mq HM2 Hqq).
  - intros xq mq Hqq. exact (p2_pos rc B (API rc) L3 A3 mem4 md4 xq mq HM4 Hqq).
Qed.

Lemma s4_WT3 : nc_wt (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj) <= cnl_wt es2 hj2 h2.
Proof.
  assert (SB2 : Forall2 p2_sbs es2 (pre' ++ e3 :: post')).
  { unfold es2. apply Forall2_app; [exact SBpre|constructor; [exact SB3|exact SBpost]]. }
  rewrite (p2_sbs_wt _ _ _ SB2). unfold hj2, h3.
  exact (cnl_wt_post es2 (firstn i hj) (skipn (S i) hj) h2 jj E3 H3 E3R E3C H3C H3T).
Qed.

Lemma s4_NCS3 : CF.SlotRI3.ncs (view_of G OUT2 (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj)) L3 A3 <=
  nc_wt (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj).
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. pose proof s3_Rcw as (HM4 & _).
  assert (NB3 : List.NoDup (map fst (blocks L3 A3))).
  { pose proof (NDB L3 A3 mem4 md4 HM4) as XN3. first [exact XN3|exact (proj1 (NoDup_ListNoDup _) XN3)]. }
  pose proof (CF.SlotNcWt.ncs_le_wt (rc := rc) B (API rc) L3 A3 mem4 md4 (t + 1) nfd G _ _ _ _ _ HM4 s3_OUT4 s4_REL4
    ltac:(rewrite s4_LEN; exact Hes) NB3) as NCS3.
  rewrite DN2 in NCS3. exact NCS3.
Qed.

Lemma s4_RI4 : RI E K (view_of G OUT2 (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj)) L3 A3.
Proof.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB. p2d_s4 IL IHJ.
  pose proof s3_Rcw as (HM4 & _). pose proof s3_Rum as (_ & _ & _ & LYu & _).
  assert (NB3 : List.NoDup (map fst (blocks L3 A3))).
  { pose proof (NDB L3 A3 mem4 md4 HM4) as XN3. first [exact XN3|exact (proj1 (NoDup_ListNoDup _) XN3)]. }
  pose proof (CF.SlotPass4.p4_src_blk_of B L3 A3 mem4 HA h3 SRC4) as P3S.
  pose proof s4_MV3 as MV3.
  apply (RV3 E3 H3 SHR3 SHL3 E3R E3V E3C NDH3 H3T BL3 NEW3).
  - intros xq mq Hxq NXq. apply SURV3; [exact Hxq|]. intros HRq. apply NXq. apply in_app_or in HRq.
    destruct HRq as [HRq|HRq]; [apply p2_hb_exp, p2_lb_recs; exact HRq|apply p2_hb_held; exact HRq].
  - exact P3S.
  - intros xq mq Hqq. destruct (BL3 xq mq Hqq) as [(Hqq2 & _)|HHq]; [left; exact Hqq2|right].
    apply (p2_mid_in G OUT2 _ _ i e3 h3 jj xq NE3 NH3). right; right. apply in_or_app; right. apply p2_hb_held.
    exact HHq.
  - unfold pend_view, hj2. rewrite !map_app. reflexivity.
  - exists (ek_view (firstn i hj)), (ek_view (skipn (S i) hj)). split.
    + unfold hj2. apply p2_ek_split.
    + rewrite p2_ek_split. cbn [fst]. unfold h3. cbn [set_exp_held hs_expected]. unfold ekeys_hl. rewrite E3R.
      reflexivity.
  - rewrite s4_LEN. exact Hes.
  - rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. clear - Hes IHJ LHJ. lia.
  - exact MV3.
  - exact NB3.
  - exact (p2_nc_keep _ _ _ _ _ _ _ _ HWF2 LYu MV3).
  - exact s4_NCS3.
  - exact s4_WT3.
Qed.

Lemma s4_MI : forall R5, tail_regs E t K R5 ->
  MI (rc := rc) B (API rc) E RI t K TAIL_CHECK (fun _ _ _ r => tail_regs E t K r)
    (mkCfg (@YK11.mkst fx' R5 (Z_to_bv 64 TAIL_CHECK) mem4 (seg_rom (ms_segs B))) md4).
Proof using All.
  intros R5 TR5.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof s4_KEPT as (IK4 & ST4 & DK4).
  pose proof s3_Rcw as (HM4 & HWF4 & HBD4 & _ & _ & _ & _ & _ & _ & MD4 & _).
  exists fx', L3, A3, R5, mem4, md4, cl, (if send_off cl br TOT then br else dd), gn, dd,
    (if send_off cl br TOT then ei else 0), G, nfd, mx, (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout),
    (if live then Z_to_bv 64 CAP2 else cap), (if live then Z_to_bv 64 OUT2 else out), (pre' ++ e3 :: post'),
    (firstn i hj ++ (h3, jj) :: skipn (S i) hj).
  split; [reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split; [exact TR5|]. split; [exact HM4|]. split; [exact HWF4|]. split; [exact HBD4|]. split; [exact INIT3|].
  split; [destruct MD4 as [v4 EV4]; destruct MD2 as [v2 EV2]; pose proof HVM as [v0 EV0]; exists v4;
    rewrite EV4, EV2, EV0, !with_vmmaps_twice; reflexivity|].
  split; [exact RO4|]. split; [exact IK4|]. split; [exact ST4|]. split; [exact DK4|].
  split; [rewrite s4_LEN; exact s3_GL4|].
  split; [change (0 <= nfd <= t + 2); clear - Hnfd; lia|]. split; [exact s3_OUT4|]. split; [exact s4_REL4|].
  split; [rewrite s4_LEN; exact Hes|]. split; [exact s4_COST4|].
  rewrite DN2. exact s4_RI4.
Qed.

End S4.

Lemma s3_main : SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs4 (PropExec.getr R3 1) mem4 (seg_rom (ms_segs B))) md4)
  (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof using All.
  p2d_base. pose proof s3_Rcw as Rcw. pose proof Rcw as (HM4 & HWF4 & HBD4 & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  pose proof s3_PRc as PRc.
  assert (NV : (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout) =
      Z_to_bv 64 (if gn =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h2))) else 0))
    by exact (dc_nout_w gn cl br dd live (hs_expected h) (hs_expected h2) Ls LB nout HGN (proj1 HGG) (proj2 HGG) LVD
      EXP0 HEX2 (dc_lines_range h) LBE HNO).
  pose proof BNO4 as BNO4'. rewrite NV in BNO4'.
  pose proof s3_AT3 as AT3. pose proof AT4 as AT4'. rewrite AT3 in AT4'.
  assert (RDv : ov_read_bytes rsegs mem4 (Z_to_bv 64 (slot_sp E + 40)) 8 =
      Some (le8 (Z_to_bv 64 (if gn =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h2))) else 0)))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C8 _) AT4' eq_refl) as X. rewrite SEG in X.
    change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
  replace (PropExec.getr R3 1) with (Z_to_bv 64 0x14398) by (symmetry; exact Q1).
  assert (P42 : reg_get regs4 2 = Z_to_bv 64 (slot_sp E)) by exact (eq_trans (PRc 2 ltac:(unfold callee_saved; lia)) Q2).
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh4|exact Hl4|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite P42.
    rewrite SEG in BNO4'. apply (op2_end CSD (slot_sp E)); [exact RDv|exact BNO4']. }
  intros ms5 (can5 & (a1' & ->) & EQ5).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  rewrite <- SEG.
  eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail_regs E t K r));
    [exact HF|exact HCB|intros; assumption|exact HWK|]|intros c5 HC5; exists K; exact HC5].
  pose proof s3_Rt as Rt. pose proof s1_RDw as (HM2 & _). pose proof s3_Rum as Rum.
  destruct (p2_pairs_rmid rc fx B (API rc) _ _ _ _ L A mem md L3 A3 mem4 md4 t (firstn i es) (firstn i hj) FA SEG HKc
    HMR Rt PApre ESpre
    (s3_KPE _ (fun q Hq => in_or_app _ _ _ (or_introl Hq)) ESpre)
    (s3_KPH _ _ (fun q Hq => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hq))))))
      PApre)
    (s3_KSP _ _ (fun p Hp => in_or_app _ _ _ (or_introl Hp)) PApre)) as (pre' & SBpre & EOpre & PApre').
  destruct (p2_pairs_rmid rc fx B (API rc) _ _ _ _ L A mem md L3 A3 mem4 md4 t (skipn (S i) es) (skipn (S i) hj) FA SEG
    HKc HMR Rt PApost ESpost
    (s3_KPE _ (fun q Hq => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hq)))) ESpost)
    (s3_KPH _ _ (fun q Hq => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hq))))))
      PApost)
    (s3_KSP _ _ (fun p Hp => in_or_app _ _ _ (or_intror Hp)) PApost)) as (post' & SBpost & EOpost & PApost').
  destruct (p2_entry_rmid rc fx B (API rc) _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 e2 FA HM2 Rum EOK2 s3_KE2)
    as (e3 & SB3 & EOK3).
  apply (s4_MI pre' post' e3 SBpre EOpre PApre' SBpost EOpost PApost' SB3 EOK3 R5).
  unfold tail_regs, base_regs, fix_regs. repeat split.
  - geq X5.
  - p2d_ch X5 PRc Q3 3.
  - p2d_ch X5 PRc Q4 4.
  - p2d_ch X5 PRc Q20 20.
  - p2d_ch X5 PRc Q23 23.
  - p2d_ch X5 PRc Q25 25.
  - p2d_ch X5 PRc Q21 21.
  - p2d_ch X5 PRc Q19 19.
  - p2d_ch X5 PRc Q27 27.
  - p2d_ch X5 PRc Q24 24.
  - p2d_ch X5 PRc Q8 8.
  - p2d_ch X5 PRc Q26 26.
  - p2d_ch X5 PRc Q22 22.
Qed.

End S3.

Lemma s2_main : SR (ms_segs B) (mkCfg (@YK11.mkst fx' R3 (Z_to_bv 64 CHECK_NO_LOSS) m3 (seg_rom (ms_segs B))) md2)
  (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof using All.
  p2d_base. p2d_s1 SRC HES SSK NDT EXP0 SKO WU HGN HGG IL IHJ NDB.
  pose proof s2_Ru as Ru. pose proof s2_SRC3 as SRC3.
  pose proof s1_RI2 as RI2. pose proof s1_COST2 as COST2. pose proof s1_ND2T as ND2T.
  destruct (CRES E K L2 A2 G OUT2 es2 hj2 i e2 h2 jj RI2 NB2 Hk COST2 ND2T NE2i NH2i
    (CF.SlotPass4.p4_src_blk_of B L2 A2 mem2 HA h2 SRC2) HB22) as (bnd2 & RFOK2 & ROOM2 & RPOST2).
  assert (Q4t : PropExec.getr R3 4 = Z_to_bv 64 (ms_tp B)) by (rewrite Q4; exact TP).
  assert (SPR3 : spZ R3 = slot_sp E)
    by (unfold spZ; change (bv_unsigned (PropExec.getr R3 2) = slot_sp E); rewrite Q2; apply unsigned_lit; lia2).
  assert (AT3 : bv_unsigned (PropExec.getr R3 11) = slot_sp E + 40) by (rewrite Q11; apply unsigned_lit; lia2).
  assert (SPQ : slot_sp E = 16 * (slot_sp E / 16))
    by (pose proof (Z.div_mod (slot_sp E) 16 ltac:(lia)) as DM; rewrite SPA in DM; clear - DM; lia).
  pose proof s2_GOV3 as GOV3. destruct (outv_bytes _ _ _ _ _ _ GOV3) as (BNO3 & BOU3).
  pose proof s2_GG3 as GG3. pose proof s2_C403 as C403. pose proof s2_BOB3 as BOB3.
  pose proof (CNL fx' L2 A2 R3 m3 md2 bnd2 h2 jj gn 0 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
    (if live then Z_to_bv 64 OUT2 else out) (if live then LB else [])) as CC. cbv zeta in CC.
  eapply SR_bind.
  { apply CC.
    - exact SEG.
    - apply (cpk_of_rmid B (API rc) _ _ _ _ L2 A2 mem2 md2 L2 A2 m3 md2 R3 CHECK_NO_LOSS_K Ru INIT2).
      + change (YK0s.ret_ok (PropExec.getr R3 1)). rewrite Q1. apply ret_ok_even. rewrite unsigned_lit by lia2.
        reflexivity.
      + exact Q4t.
      + rewrite SPR3. exact SPA.
      + rewrite SPR3, p2_cnl_k. unfold SLOT_STACK, SLOT_FRAME. lia2.
      + rewrite SPR3. lia2.
      + rewrite p2_cnl_k. lia2.
      + rewrite SPR3, p2_cnl_k. lia2.
      + rewrite SPR3. lia2.
    - exact INIT2.
    - rewrite SEG. exact RO3.
    - intros a Ha. apply PL. apply in_G_bss. ugl_in Ha. ugs_in Ha. lia2.
    - exact JJ4.
    - exact Q10.
    - exact SRC3.
    - rewrite HHL2. exact NDT.
    - exact EN26.
    - exact HB22.
    - rewrite AT3, SPQ. replace (16 * (slot_sp E / 16) + 40) with ((2 * (slot_sp E / 16) + 5) * 8) by ring.
      apply Z_mod_mult.
    - rewrite AT3, SPR3. lia2.
    - rewrite AT3. lia2.
    - rewrite AT3. exact C403.
    - destruct HGN as [X|X]; rewrite X; lia.
    - exact GG3.
    - exact BNO3.
    - exact BOU3.
    - exact BOB3.
    - exact DN3.
    - exact DN4.
    - exact DN5.
    - exact DN6.
    - exact RFOK2.
    - exact ROOM2. }
  intros c4 (L3 & A3 & regs4 & mem4 & md4 & E3 & H3 & -> & RPc & INIT3 & (qs3 & LQ3 & RF3 & SHR3 & SHL3) & RO4 & SRC4 &
    E3R & E3V & E3C & NDH3 & H3C & H3T & AT4 & GG4 & BNO4 & BOU4 & BOB4 & SURV3 & BL3 & NEW3).
  exact (s3_main L3 A3 regs4 mem4 md4 E3 H3 qs3 (RPOST2 L3 A3 qs3 LQ3 RF3) SHR3 SHL3 RPc INIT3 RO4 SRC4 E3R E3V E3C
    NDH3 H3C H3T AT4 BNO4 SURV3 BL3 NEW3).
Qed.

End S2.

Lemma s1_main : SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs2 (PropExec.getr R 1) mem2 (seg_rom (ms_segs B))) md2)
  (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof using All.
  p2d_base. pose proof s1_RDw as RDw. pose proof RDw as (HM2 & HWF2 & HBD2 & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  pose proof s1_ST2 as ST2. pose proof b_NRO as NRO. pose proof s1_CK2 as CK2. pose proof s1_PRd as PRd.
  pose proof (dc_read B L2 A2 mem2 HA h2 SRC2 HPR2) as RD24. pose proof RO2 as RO2r.
  replace (PropExec.getr R 1) with (Z_to_bv 64 0x14378) by (symmetry; exact D1).
  assert (P2 : reg_get regs2 2 = Z_to_bv 64 (slot_sp E)) by exact (eq_trans (PRd 2 ltac:(unfold callee_saved; lia)) D2).
  assert (P9 : reg_get regs2 9 = Z_to_bv 64 HA) by exact (eq_trans (PRd 9 ltac:(unfold callee_saved; lia)) D9).
  assert (P19 : reg_get regs2 19 = Z_to_bv 64 0x318f8) by exact (eq_trans (PRd 19 ltac:(unfold callee_saved; lia)) D19).
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh2|exact Hl2|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite P2, P9, P19.
    rewrite SEG in RD24, CK2, RO2r.
    apply (op2_mid ULKR CNR (slot_sp E) HA); [lia2|lia2|lia2|lia2|exact HA8|exact ST2|exact NRO|exact CK2|exact RD24
      |exact RO2r]. }
  intros ms1 (can1 & (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MU3 & WM3 &
    RO3 & ST3 & CK3) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R3 & -> & X3).
  rewrite <- SEG.
  apply (s2_main m3 R3).
  - geq X3.
  - geq X3.
  - p2d_q X3 PRd D3 3.
  - p2d_q X3 PRd D4 4.
  - p2d_q X3 PRd D8 8.
  - geq X3.
  - geq X3.
  - geq X3.
  - p2d_q X3 PRd D20 20.
  - p2d_q X3 PRd D21 21.
  - p2d_q X3 PRd D22 22.
  - p2d_q X3 PRd D23 23.
  - p2d_q X3 PRd D24 24.
  - p2d_q X3 PRd D25 25.
  - p2d_q X3 PRd D26 26.
  - p2d_q X3 PRd D27 27.
  - exact MU3.
  - exact WM3.
  - exact RO3.
  - exact ST3.
  - exact CK3.
Qed.

End S1.

Lemma p2d_main : SR (ms_segs B) (mkCfg (@YK11.mkst fx' R (Z_to_bv 64 DRAIN) m1 (seg_rom (ms_segs B))) md)
  (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof using All.
  p2d_base. pose proof b_R0 as R0. pose proof b_KB as KB. pose proof b_SRC1 as SRC1. pose proof b_TW as TW.
  destruct (p2_entry_rmid rc fx B (API rc) _ _ _ _ L A mem md L A m1 md e FA HMR R0 EOK (fun q _ => KB q))
    as (e1 & SB1 & EOK1).
  assert (GCL1 : rw_cells (ms_segs B) m1 G_CLIENT [C4 (Z_to_bv 64 cl)]).
  { apply TW; [exact (proj2 (hg_cut _ _ _ [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 cl)] G1))|cbn; ugl; lia2]. }
  assert (GBR1 : rw_cells (ms_segs B) m1 G_BROKEN [C1 (Z_to_bv 8 br)]) by (apply TW; [exact G4|cbn; ugl; lia2]).
  assert (GDD1 : rw_cells (ms_segs B) m1 G_DEAD [C1 (Z_to_bv 8 dd)]) by (apply TW; [exact G6|cbn; ugl; lia2]).
  assert (GEI1 : rw_cells (ms_segs B) m1 G_EINTR [C1 (Z_to_bv 8 ei)]) by (apply TW; [exact G7|cbn; ugl; lia2]).
  assert (GOV1 : rw_cells (ms_segs B) m1 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out])
    by (apply TW; [exact G11|cbn; ugl; lia2]).
  assert (GER1 : exists ev, rw_cells (ms_segs B) m1 (errno_addr B) [C4 ev]).
  { destruct GER as [ev GE]. exists ev. apply TW; [exact GE|rewrite ERR; cbn; lia2]. }
  pose proof HOUT as ((O & junk & OC) & CAPB).
  assert (OC1 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ O = []) \/
    (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L A) /\
     fresh_block B (bv_unsigned out) (bv_unsigned cap) /\ bytes_at (ms_segs B) m1 (bv_unsigned out) (O ++ junk) /\
     Z.of_nat (length O) = bv_unsigned nout /\ Z.of_nat (length junk) = bv_unsigned cap - bv_unsigned nout)).
  { destruct OC as [OC'|(C0 & C1 & C2 & C3 & C4' & C5 & C6)]; [left; exact OC'|right].
    split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [|split; assumption].
    eapply bytes_at_transport; [exact C4'|exact MU1|].
    apply entry_disjoint_pts; [repeat constructor; cbn; lia2|rewrite length_app; lia2|].
    intros x Hx. rewrite length_app in Hx.
    destruct (p2_blk rc fx B (API rc) L A mem md _ _ (x - bv_unsigned out) FA HMR C2 ltac:(lia2)) as (NIm & _ & X2).
    replace (bv_unsigned out + (x - bv_unsigned out)) with x in NIm by lia.
    cbn [outside]. split; [lia2|]. split; [|exact I]. intros HX. apply NIm.
    exact (proj1 (PL _ (in_G_bss x ltac:(lia2)))). }
  destruct (p2_others rc B L A mem t nfd G (bv_unsigned out) es hj i e h jj HREL Hi Hh) as (fs & os & OTH).
  assert (OTH1 : others_at B m1 jj (re_fd e1) fs os).
  { destruct SB1 as (SF & _). rewrite SF. destruct OTH as (OL1 & OL2 & OT). split; [exact OL1|]. split; [exact OL2|].
    intros k Hk0 NK. destruct (OT k Hk0 NK) as (OC0 & OR). split; [|exact OR].
    apply TW; [exact OC0|cbn; ugs; unfold SRC_SIZE; lia2]. }
  destruct TBL as (tail & TL & TB).
  pose proof (p2_table_split rc B L A mem es tail G i e HES Hi TL TB) as TS.
  pose proof (proj2 (hg_cut _ _ _ [_] [_; _] TS)) as TS2.
  pose proof (proj1 (hg_cut _ _ _ [_] [_] TS2)) as TSE.
  cbn [cells_size csize] in TSE. replace (G + Z.of_nat (56 * i + 0)) with SA in TSE by (rewrite SAe; lia).
  assert (TSE1 : rw_cells (ms_segs B) m1 SA [CB 56 (entry_bytes e1)]).
  { rewrite (p2_sbs_bytes e e1 SB1).
    apply (rmid_rw_block B (API rc) BW _ _ _ _ L A mem md L A m1 md G 896 SA _ R0 GIN ltac:(lia) (fun X => X) TSE);
      [rewrite SAe; lia|cbn; rewrite SAe; lia|].
    intros k Hk0. cbn in Hk0. replace (SA + k) with (G + (SA - G + k)) by lia.
    destruct (KB G) as (_ & KE). apply (KE 896 (SA - G + k) GIN). rewrite SAe. lia. }
  pose proof SB1 as (SF1 & SE1 & SS1 & SP1 & SBU1 & SU1 & SC1' & SH1 & SKH1 & SP2 & SK1 & SUU1 & SJ1).
  assert (NH19 : 19 * Z.of_nat (length (re_keys e)) <= keys_total (re_keys e)).
  { apply keys_total_count. eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & _ & (L14 & _) & _). exact L14. }
  set (live := send_live cl br dd TOT).
  pose proof (p2d_dtr e e1 h (known_at L A) (known_at L A (bv_unsigned out)) live (bv_unsigned mx) (bv_unsigned nout)
    (bv_unsigned cap) SB1) as DTR.
  pose proof (p2d_dfn e e1 h live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) SB1) as DFN.
  pose proof (p2d_dfa e e1 h (known_at L A) (known_at L A (bv_unsigned out)) live (bv_unsigned mx) (bv_unsigned nout)
    (bv_unsigned cap) SB1) as DFA.
  assert (OCX : bv_unsigned cap = 0 \/ In (bv_unsigned out, bv_unsigned cap) (blocks L A))
    by (destruct OC1 as [(C0 & _)|(_ & _ & IN & _)]; [left; exact C0|right; exact IN]).
  assert (RCAP : 0 <= re_cap e) by (clear - ECAP; lia).
  assert (RKA : 0 <= ent_ka e).
  { unfold ent_ka. destruct (Z.eqb_spec (re_hp e) 0) as [_|N]; [lia|].
    destruct EHP as [(X & _)|(_ & _ & _ & K8 & _)]; [contradiction|clear - K8; lia]. }
  assert (J1E : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)).
  { unfold J1, hs_state. cbn [ls_k ls_w]. rewrite SKO.
    split; [reflexivity|]. split.
    - intros F0. apply WU. destruct EH2 as [S|S]; [exact S|]. rewrite <- SKO, S in F0. discriminate.
    - split.
      + unfold bzs. rewrite length_map. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000.
        clear - EUL EU6. lia.
      + unfold nozero, bzs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
        intros Z0. apply EUZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. unfold bz in Z0.
        rewrite Z0. reflexivity. }
  assert (OFF0 : 0 <= hs_off h).
  { pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & OFFD & _).
    destruct OFFD as [(_ & X)|(r & rs & _ & X)]; clear - X; lia. }
  assert (NHP : re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26).
  { unfold re_nheld. unfold pair_cost in PCB. cbn [fst] in PCB. pose proof (keys_total_nonneg (re_keys e)).
    destruct (re_skip e =? 0); lia2. }
  assert (UUL : Z.of_nat (length (re_U e)) <= re_used e) by (clear - EUL; lia).
  assert (KH2 : re_hp e <> 0 -> re_kh e <> 0).
  { intros HP0. destruct EHP as [(X & _)|(_ & _ & _ & K8 & _)]; [contradiction|lia]. }
  assert (OCN : ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h) <= SlotCaps3.NMAX).
  { pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV0 & _).
    pose proof (CF.RelayCap.drain_ocap_le_tot live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h
      (p2_fin_no live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) rc B L A mem e h HA EOK SRC SKO WU))
      as OCB.
    pose proof (reads_bound e h SKO WU HOV0 EUL) as RB.
    change (Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h)))))) with TOT in OCB, RB.
    unfold pair_cost in PCB. cbn [fst] in PCB. pose proof (keys_total_nonneg (re_keys e)) as KN.
    pose proof (Zle_0_nat (length (pending_stream h))) as PN0.
    clear - OCB RB PCB KN PN0 CAPB HNO EUL. unfold SlotCaps3.NMAX, TBBYTES in *.
    destruct (re_skip e =? 0); lia. }
  assert (OZN : bv_unsigned cap = 0 -> forall m, ~ In (bv_unsigned out, m) (blocks L A)).
  { intros C0 m Hm. destruct OC1 as [(_ & OZ & _)|(CP & _)]; [|lia].
    pose proof (p2_low rc B (API rc) L A mem md _ _ HMR Hm) as LW. lia. }
  destruct (DRES E K L A G (bv_unsigned out) es hj i e h jj live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap)
    HRI NB0 Hk Hcost PCK NDA Hi Hh EOF (CF.SlotPass4.p4_ent_blk_of B L A mem e EOK)
    (CF.SlotPass4.p4_src_blk_of B L A mem HA h SRC)
    OCX ltac:(clear - HMX MXR; lia) ltac:(clear - HNO CPR; lia) CAPB EXP0 EC
    ltac:(clear - PS Ht; unfold WRITE_MAX, OPS_MAX in *; lia) RCAP RKA J1E OFF0 NHP UUL KH2 OCN OZN Hes
    ltac:(pose proof (Forall2_length PA); lia))
    as (ECF & bnd & RFOK & ROOM & RPOST).
  rewrite <- DTR in ROOM.
  assert (SPR : spZ R = slot_sp E) by (unfold spZ; rewrite D2; apply unsigned_lit; lia2).
  assert (CPK : call_pre_k B (aa_MR (API rc)) DRAIN_K L A R m1 md).
  { apply (cpk_of_rmid B (API rc) _ _ _ _ L A mem md L A m1 md R DRAIN_K R0 HINIT).
    - rewrite D1. apply ret_ok_even. rewrite unsigned_lit by lia2. reflexivity.
    - rewrite D4. exact TP.
    - rewrite SPR. exact SPA.
    - rewrite SPR, p2_drain_k. unfold SLOT_STACK, SLOT_FRAME. lia2.
    - rewrite SPR. lia2.
    - rewrite p2_drain_k. lia2.
    - rewrite SPR, p2_drain_k. lia2.
    - rewrite SPR. lia2. }
  pose proof (DRN fx' L A R m1 md bnd e1 h jj fs os G O junk cl br dd ei mx nout cap out) as DC. cbv zeta in DC.
  eapply SR_bind.
  { apply DC.
    - exact SEG.
    - exact CPK.
    - exact HINIT.
    - unfold errno_addr, ERRNO_OFF. rewrite EOFF. reflexivity.
    - rewrite ERR. reflexivity.
    - rewrite ERR. ugl. lia2.
    - exact RO1.
    - intros a Ha. apply PL. apply in_G_bss. ugl_in Ha. ugs_in Ha. lia2.
    - intros a Ha. apply PL, g9_in_listen. ugl_in Ha. lia2.
    - intros a Ha. exact (proj1 (entry_errno_image B SEG ETP EOFF a Ha)).
    - exact JJ4.
    - match goal with |- context [bv_unsigned (getr R ?r)] =>
        replace (bv_unsigned (getr R r)) with SA by (symmetry; exact HSA) end.
      split; [exact GIN|]. split; [exact GFR|]. rewrite SAe. unfold SRC_TABLE, SRC_ENTRY.
      split; [lia2|]. split; [lia2|]. replace (G + 56 * Z.of_nat i - G) with (Z.of_nat i * 56) by lia2. apply Z_mod_mult.
    - match goal with |- context [bv_unsigned (getr R ?r)] =>
        replace (bv_unsigned (getr R r)) with SA by (symmetry; exact HSA) end.
      exact TSE1.
    - exact EOK1.
    - exact SRC1.
    - exact OTH1.
    - rewrite SF1. exact FDH.
    - rewrite SS1. exact SKO.
    - rewrite SS1, SUU1. exact WU.
    - rewrite (p2_sbs_blocks e e1 SB1). exact (p2_nodup_sub G (bv_unsigned out) es hj i e h jj NDA Hi Hh).
    - unfold pair_cost in PCB. cbn [fst] in PCB. pose proof (keys_total_nonneg (re_keys e)).
      destruct (re_skip e =? 0); lia2.
    - exact (proj2 (ecap_ok_lt _ EC)).
    - unfold re_nheld. rewrite (p2_fst_len _ _ SK1). unfold pair_cost in PCB. cbn [fst] in PCB.
      destruct (re_skip e =? 0); lia2.
    - exact HCL.
    - exact HBR.
    - exact HDD.
    - exact HEI.
    - exact GCL1.
    - exact GBR1.
    - exact GDD1.
    - exact GEI1.
    - exact GOV1.
    - exact GER1.
    - exact OC1.
    - exact RFOK.
    - exact ROOM. }
  intros c' (L2 & A2 & regs2 & mem2 & md2 & e2 & h2 & OUT2 & CAP2 & junk2 & LB & -> & RP & INIT2 &
    (qs2 & LQ2 & RF2 & OLK & ELK & SLK) & RO2 & SA2 &
    EOK2 & SRC2 & OTH2 & FD2 & EOF2 & CAP2P & DC1 & DC2 & DC3 & DC4 & DC5 & DC6 & _ & _ & HFD2 & HCL2 & HEI2 & HPR2 &
    HOF2 & HPV2 & HPC2 & HPA2 & HST2 & HEX2 & HFX2 & HHL2 & SKO2 & WU2 & NDK2 & SSK2 & NDB2 & GIN2 & SURV2 & BL2 &
    NEW2 & GCL2 & GBR2 & GDD2 & GEI2 & GER2 & LBE & LV0 & LV1).
  repeat match goal with H : context [lines (hs_state h) (bzs (pending_stream h))] |- _ =>
    change (lines (hs_state h) (bzs (pending_stream h))) with Ls in H end.
  repeat match goal with H : context [Z.of_nat (length (with_nul Ls))] |- _ =>
    change (Z.of_nat (length (with_nul Ls))) with TOT in H end.
  repeat match goal with H : context [send_live cl br dd TOT] |- _ => change (send_live cl br dd TOT) with live in H end.
  assert (LVD : live = send_live cl br dd TOT) by reflexivity.
  clearbody live.
  rewrite DFN in DC1, DC2, DC4, DC5, DC6. rewrite DTR in LQ2, RF2. rewrite DFA in OLK, ELK, SLK.
  exact (s1_main O junk e1 live L2 A2 regs2 mem2 md2 e2 h2 OUT2 CAP2 junk2 LB qs2 OC CAPB SB1 EOK1 LVD ECF
    (RPOST L2 A2 qs2 LQ2 RF2) RP INIT2 OLK ELK SLK RO2 SA2 EOK2 SRC2 FD2 DC1 DC2 DC4 DC5 DC6 HFD2 HPR2 HPV2 HPC2
    HPA2 HST2
    HEX2 HHL2 SKO2 WU2 NDK2 SSK2 NDB2 GIN2 SURV2 BL2 NEW2 GBR2 GEI2 LBE LV0 LV1).
Qed.

End P2D.

Lemma p2_drain_path : forall F B API LS SH SK ra empty rc fx j E CS RI t K c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract -> pthread_mutex_unlock_contract ->
  (forall fx', @drain_contract fx' rc B (API rc) F) -> check_no_loss_read_contract ->
  (forall fx', @check_no_loss_contract fx' rc B (API rc) F) -> check_shape_done_contract ->
  p2_drain_res_s F RI -> p2_cnl_res_s F RI -> walk_at (ss_pl E) (t + 1) K ->
  p2_drain_st B API rc E RI t K c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof.
  intros F B API LS SH SK ra empty rc fx j E CS RI t K c HF HCB ULK DRN CNR CNL CSD DRES CRES HWK
    (fx' & L & A & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj & i & e & h & jj &
     R & m1 & -> & FZ & Ht & Hk & Hn & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT &
     HREL & Hes & Hcost & HRI & HNO & Hi & Hh & EOF & DR & MU1 & WM1 & RO1 & CK1 & C401).
  exact (p2d_main F B API LS SH SK ra empty rc fx j E CS RI t K fx' L A mem md cl br gn dd ei G nfd mx nout cap out es hj
    i e h jj R m1 HF HCB ULK DRN CNR CNL CSD DRES CRES HWK FZ Ht Hk Hn HMR HWF HBD HINIT HVM HRO HIK HST HDK HGL Hnfd
    HOUT HREL Hes Hcost HRI HNO Hi Hh EOF DR MU1 WM1 RO1 CK1 C401).
Qed.
