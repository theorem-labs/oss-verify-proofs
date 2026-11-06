(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 311 of its 378 lines of code are new or changed and 492 lines of the source are left out. *)
(* SrxArmKit: what the on_announce and on_data arms of the image-A walk of diginet_session_rx (SrxAnn.v at +0x3dc,
   SrxData.v at +0x44c) share. Each arm is three register moves and a `jal` to a G-form session callee, then `j +0x480`
   to the tick cut (SrxCut.v srx_tick_at), so the arms differ only in the callee's contract. The kit holds:
   - srxa_fld_G and the tactic srxa_split: a byte of a written range built of TWorldG fields of TMAP_A rows (the rows
     twa_fld of TWorldA.v's globals) is a byte of G;
   - the symbolic state the token engine starts from, with no region and no fact, at any pc (srxa_entry), and its
     environment (srxa_E: the registers as atoms 0 .. 31);
   - the window facts of srx_fix (srxa_win), the frame argument f and the bytes at buf as the callees' contracts state
     them (srxa_dframe: on_ack_cg.v trans_dframe_at), and the heap frame TF at a callee's window (srxa_tframe_call);
   - srxa_tframe: TF across a callee whose written range is bytes of G (trans_tf_off_g puts TF outside G);
   - srxa_after: from the cut's srx_cur and the callee's post (TransportGCg.v transport_cg_post), srx_cur, TF and the
     read-only bytes at the state the callee returns, with the own class-1 frame live (dk_kept_trans_nf_g);
   - srxa_regs_base: srx_regs_base across a run that keeps every callee-saved register. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_mac_is_digidesign_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. Written ranges: bytes of G                                       *)
(* ------------------------------------------------------------------ *)

(* A field of a TMAP_A row, inside the row, is a range of G. *)
Lemma srxa_fld_G : forall o b n A w a, In (o, b, n) TMAP_A -> o <= A -> A + w <= o + n ->
  twa_fld o b A w a -> inG TG.G_HARNESS a.
Proof.
  intros o b n A w a Hin H1 H2 Hf. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr, twa_fld in *; cbn [fst snd]; lia].
Qed.

(* A side condition of srxa_fld_G: a comparison of TWorld offsets, by lia over the indexed fields GOT.t[] and
   g_cmd[] (their index bounded by the written range's guard), else closed and decided by vm_compute (never on a
   goal that still holds a world). *)
Ltac srxa_off :=
  first
    [ unfold TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT, TC.TRANS_MAX, TW.A_Cmd_st, TW.OFF_g_cmd,
        TW.SZ_g_cmd, TC.CMDS_MAX in *; lia
    | lazymatch goal with |- context [TW.GOT_n _] => fail | _ => idtac end;
      apply Z.leb_le; vm_compute; reflexivity ].

(* A leaf of a written range: its twa_fld is a field of one of the TMAP_A rows the session callees write. *)
Ltac srxa_wr_leaf :=
  match goal with Hf : twa_fld ?o ?b ?A ?w ?x |- inG _ _ =>
    eapply (srxa_fld_G o b _ A w x);
    [ first [ exact TMAP_A_g_s | exact TMAP_A_GOT | exact TMAP_A_M | exact TMAP_A_g_cmd | exact TMAP_A_g_q
            | exact TMAP_A_g_nq | exact TMAP_A_g_fail_next | exact TMAP_A_g_last_counter ]
    | srxa_off | srxa_off | exact Hf ]
  end.

(* A written range unfolded to its rows: each disjunct, each witness, each guarded conjunct (the guard on the left,
   kept as a hypothesis), down to a twa_fld leaf. *)
Ltac srxa_split H :=
  lazymatch type of H with
  | twa_fld _ _ _ _ _ => srxa_wr_leaf
  | _ \/ _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 | H2]; [srxa_split H1 | srxa_split H2]
  | @ex _ _ => let x := fresh "x" in let H1 := fresh "H" in destruct H as [x H1]; srxa_split H1
  | _ /\ _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2]; srxa_split H2
  end.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic state with no region and no fact                    *)
(* ------------------------------------------------------------------ *)

(* Register moves, a call and a jump: no region and no fact. *)
Definition srxa_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* The empty shadow span: the runs read no shadow byte. *)
Definition SRXA_B0 : Z * Z := (0, 0).

(* An eight-byte word of a view, kept by a step that keeps its eight bytes. *)
Lemma srxa_rdword : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a Hk. unfold rdword.
  pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)),
          (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)). reflexivity.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxa_reg HS r v H tac :=
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

(* A callee-saved register of R3, from a register equality at R2 and aregs_preserved R2 R3. *)
Ltac srxa_keep :=
  lazymatch goal with |- YK11.getr ?R3x ?r = ?v =>
    match goal with HP : aregs_preserved ?R2x R3x, Hr : YK11.getr ?R2x r = v |- _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      exact (eq_trans (HP z ltac:(hnf; lia)) Hr) end end.

Lemma srxa_regs_base : forall (regs regs2 regs4 : bvmap 5 word) now sp1 F,
  srx_regs_base regs regs2 now sp1 F -> aregs_preserved regs2 regs4 -> srx_regs_base regs regs4 now sp1 F.
Proof.
  intros regs regs2 regs4 now sp1 F ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) HP.
  unfold srx_regs_base, srx_regs_core.
  repeat match goal with |- _ /\ _ => split end.
  all: srxa_keep.
Qed.

Section kit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The environment: the thirty-two registers as atoms 0 .. 31, and the image's own values above A_TEXT. *)
Definition srxa_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma srxa_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (srxa_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold srxa_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma srxa_env : forall regs, img_env VAL A_LIM (srxa_E regs).
Proof. intros regs. unfold srxa_E. apply Eimg_env. Qed.

Lemma srxa_agree : forall regs, env_agree 32 (Ereg regs []) (srxa_E regs).
Proof.
  intros regs. split; [intros n Hn; unfold srxa_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma srxa_entry : forall pc (W : world segs) regs mem,
  st_ok_pi segs VAL (srxa_E regs) (srxa_ss pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros pc W regs mem. rewrite restrict_mkst_fx. unfold srxa_ss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat split; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The caller's window and the callee's arguments                   *)
(* ------------------------------------------------------------------ *)

(* sp1 (the realigned sp) and the windows: the switch callee's window [sp1 - ONANN_STK, sp1) (the largest of the four,
   srx_stk_eq) lies inside the call's [spZ regs - SRX_STK, spZ regs), above the own frame and below 2 ^ 47. *)
Lemma srxa_win : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) buf now r b TF
    Bw Bw' pos sp1 F,
  srx_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  sp1 mod 16 = 0 /\ spZ regs - SRX_STK <= sp1 - ONANN_STK /\ sp1 + 160 <= spZ regs /\
  sp0 - STK <= sp1 - ONANN_STK /\ F + 128 <= sp1 - ONANN_STK /\ spZ regs <= sp0 /\ sp0 <= 2 ^ 47 /\
  0 <= ONANN_STK.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX.
  destruct HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hwin0 & Hhi0 & Hnow & Hbuf & Hgb
    & Hsrcb & Howb & Hboff & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hapart & Hinv0 & Hnd0 & Hc1 & Hc4 & Hc5 & Hc0
    & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSS : SRX_STK = SRX_FRAME + SRX_ALIGN + ONANN_STK) by exact srx_stk_eq.
  assert (HO0 : 0 <= ONANN_STK) by (apply Z.leb_le; vm_compute; reflexivity).
  unfold SRX_FRAME, SRX_ALIGN in HSS.
  assert (Hx0 : 0 <= spZ regs - SRX_FRAME) by (unfold SRX_FRAME; lia).
  assert (Hx16 : (spZ regs - SRX_FRAME) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
  destruct (can_sp1_facts (spZ regs - SRX_FRAME) Hx0 Hx16) as (Hs1 & Hs2 & Hs3).
  rewrite <- Esp1 in Hs1, Hs2, Hs3. unfold SRX_FRAME in Hs1.
  unfold SRX_FBYTES in HFc.
  repeat split; lia.
Qed.

(* The frame argument f = F + 32 and the bytes at buf, as a switch callee's contract states them (on_ack_cg.v
   trans_dframe_at) at a window of at most ONANN_STK bytes below sp1. *)
Lemma srxa_dframe : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regsC : bvmap 5 word) buf now r
    b fj TF Bw Bw' pos sp1 F ly2 S2 (W2 : world segs) mem2 md2 e K,
  srx_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
  srx_rd B ly2 S2 W2 mem2 regs buf b TF Bw ->
  decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srx_fbytes W2 mem2 F buf b fj ->
  DSpec.fr_code b = 0 -> spZ regsC = sp1 -> K <= ONANN_STK ->
  trans_dframe_at B ly2 S2 W2 mem2 regsC K (F + SRX_F) buf b fj.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsC buf now r b fj TF Bw Bw' pos sp1 F ly2 S2 W2
    mem2 md2 e K HFIX HCUR HRD HDF HFB Hc0 Hsp HK.
  pose proof (srxa_win STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX)
    as (Wm & Wa & Wb & Wc & Wd & We & Wf & Wg).
  destruct HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hwin0 & Hhi0 & Hnow & Hbuf & Hgb
    & Hsrcb & Howb & Hboff & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hapart & Hinv0 & Hnd0 & Hc1 & Hc4 & Hc5 & Hc0'
    & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  destruct HCUR as (_ & _ & Hfrs & _ & HlyF & _).
  destruct HRD as (Hgb2 & Hsrcb2 & _).
  destruct HFB as (Hfjl & Hfb).
  assert (DFm8 : (F + SRX_F) mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. unfold SRX_F. rewrite D.
    replace (64 * (F / 64) + 32) with ((8 * (F / 64) + 4) * 8) by ring. apply Z.mod_mul. lia. }
  unfold trans_dframe_at.
  split; [exact Hc0|]. split; [exact Hbuf|]. split; [exact Hgb2|]. split; [exact Hsrcb2|].
  split.
  { unfold decode_off_win in Howb |- *. rewrite Hsp. destruct Howb as [Hw | Hw]; [left | right]; lia. }
  split; [exact Hboff|].
  split; [unfold SRX_F; lia|].
  split; [exact DFm8|].
  split; [exact Hfjl|].
  split; [exact Hfb|].
  split.
  { exists SRX_CID, pos. split; [rewrite Hfrs; left; reflexivity|].
    assert (EFA : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
    rewrite EFA. change (fs_frame_bytes SRX_CID) with 128. unfold SRX_F, FRAME_F_SIZE. lia. }
  split; [exact HDF|].
  left. rewrite Hsp. unfold SRX_F, FRAME_F_SIZE. lia.
Qed.

(* The heap frame TF at a callee's window that lies inside the caller's. *)
Lemma srxa_tframe_call : forall ly2 S2 (W2 : world segs) mem2 (regs regsC : bvmap 5 word) K K' (TF : option TI.tframe),
  trans_tframe_at B ly2 S2 W2 mem2 regs K TF ->
  spZ regs - K <= spZ regsC - K' -> spZ regsC <= spZ regs ->
  trans_tframe_at B ly2 S2 W2 mem2 regsC K' TF.
Proof.
  intros ly2 S2 W2 mem2 regs regsC K K' TF HT H1 H2. destruct TF as [fr|]; [|exact I].
  destruct HT as (A0 & A1 & A2 & A3). split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
  unfold decode_off_win in *. destruct A3 as [A3 | A3]; [left | right]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Across the callee                                                *)
(* ------------------------------------------------------------------ *)

(* TF across a callee whose written range Eo is bytes of G: TF's bytes are outside G (trans_tf_off_g) and outside
   the callee's window, and the caller's frames' shadow bytes lie above G; so its placement and its bytes are kept
   (trans_src_ok_kept_ge0). *)
Lemma srxa_tframe : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall ly2 S2 (W2 : world segs) mem2 md2 ly3 S3 (W3 : world segs) mem3 md3 (regs : bvmap 5 word) K slo shi
    (Eo : Z -> Prop) (TF : option TI.tframe),
  @AR rc segs B ly2 S2 W2 mem2 md2 -> @AR rc segs B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> frames S3 = frames S2 ->
  (forall cid pos, frame_addr ly3 cid pos = frame_addr ly2 cid pos) ->
  ly_stk_lo ly3 = ly_stk_lo ly2 -> ly_stk_hi ly3 = ly_stk_hi ly2 ->
  acall_kept_g segs B TG.G_HARNESS ly2 S2 W2 mem2 W3 mem3 slo shi Eo ->
  (forall a, Eo a -> inG TG.G_HARNESS a) ->
  spZ regs - K <= slo -> shi <= spZ regs ->
  trans_tf_off_g TF ->
  trans_tframe_at B ly2 S2 W2 mem2 regs K TF ->
  trans_tframe_at B ly3 S3 W3 mem3 regs K TF.
Proof.
  intros LAWS HRU HRE ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 regs K slo shi Eo TF HAR2 HAR3 Hperm Hfr Hfa Elo Ehi
    (K1 & K2 & K3 & K4 & K5 & K6) HEo Hslo Hshi Hoff HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hwin).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HnG : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
    ~ inG TG.G_HARNESS a) by (intros a Ha; exact (Hoff fr eq_refl a Ha)).
  set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (HnE : forall a, q <= a < q + n -> ~ Eo a) by (intros a Ha He; exact (HnG a Ha (HEo a He))).
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha. destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 bA nA HAR2 HinA) as (_ & _ & _ & _ & _ & _ & Hn1).
      pose proof (req_size_pos nA (proj1 Hn1)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) HinA ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(c & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3') | (HR & _)]]].
      + apply (K4 c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exfalso. exact (HnG a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B ly2 S2 W2 mem2 md2 HAR2) as [T1 T2].
        apply K1; [lia|]. intros Hx. unfold decode_off_win in Hwin. destruct Hwin as [Hw | Hw]; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
        intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
        unfold TG.G_HARNESS_LO in Gh. lia. }
  assert (KS : forall c p s, In (c, p) (frames S2) ->
     in_zr s (shadow_addr (frame_addr ly2 c p), fs_frame_bytes c / 8) ->
     aview segs (w_H W3) mem3 s = aview segs (w_H W2) mem2 s).
  { intros c p s Hin Hs. apply (K4 c p s Hin (or_intror Hs)). intros He.
    pose proof (inG_G_HARNESS_hull s (HEo s He)) as Gh.
    destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 c p HAR2 Hin) as (F1 & F2 & _).
    pose proof (Z.div_pos (frame_addr ly2 c p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs. cbn [fst snd] in Hs. unfold shadow_addr, SHADOW_OFF, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *.
    lia. }
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview segs). apply KV.
    exact Ha. }
  split; [|exact Hwin].
  exact (trans_src_ok_kept_ge0 B LAWS ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 q n HAR2 HAR3 Hperm Hfr Hfa Elo Ehi KV KS
    Hsrc Hn0).
Qed.

(* After the switch callee: its post (the G journal at (ly3, S3, W3, mem3), the call state's frames and blocks, its
   acall_kept_g over its window [sp1 - Kc, sp1) and its written range Wr, the meter) folds into srx_cur at the state it
   returns: what the call kept so far (dk_kept_trans_nf_g, Wr a row of srx_wr b), the saved words above sp1 and the
   flag word in the own frame (Wr is bytes of G, the frame is not image). TF and the read-only bytes are carried
   too. *)
Lemma srxa_after : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B -> ameter_laws MT ->
  frame_flag_lawP segs B ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 (W2 : world segs) mem2 md2 e ly3 S3 (W3 : world segs) mem3 md3 e3 Kc (Wr : Z -> Prop),
  srx_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
  trans_tframe_at B ly2 S2 W2 mem2 regs SRX_STK TF -> trans_rom_view_rd W2 mem2 ->
  0 <= e3 -> e + e3 <= SRX_EV ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly3 S3 W3 mem3 md3 (k + e + e3) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  acall_kept_g segs B TG.G_HARNESS ly2 S2 W2 mem2 W3 mem3 (sp1 - Kc) sp1 Wr ->
  mo_le MT S2 S3 0 ->
  (forall a, Wr a -> srx_wr b a) -> (forall a, Wr a -> inG TG.G_HARNESS a) ->
  spZ regs - SRX_STK <= sp1 - Kc ->
  srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md3 (e + e3) /\
  trans_tframe_at B ly3 S3 W3 mem3 regs SRX_STK TF /\ trans_rom_view_rd W3 mem3.
Proof.
  intros LAWS HRU HRE MTL FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e ly3 S3 W3 mem3 md3 e3 Kc Wr HFIX HCUR HTF2 Hrom2 He30 He3 HJ3 Hfr3 Hperm3 HK3 Hmo3 HWs HWg
    Hwin.
  pose proof (srxa_win STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX)
    as (Wm & Wa & Wb & Wc & Wd & We & Wf & Wg).
  destruct HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hwin0 & Hhi0 & Hnow & Hbuf & Hgb
    & Hsrcb & Howb & Hboff & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hapart & Hinv0 & Hnd0 & Hc1 & Hc4 & Hc5 & Hc0
    & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  destruct HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
  pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
  pose proof HJi2 as (HAR2 & Hly2 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (HAR3 & Hly3 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & ELF2 & _ & _ & _ & Elo2 & Ehi2 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & ELF3 & _ & _ & _ & Elo3 & Ehi3 & _).
  clear HJi0 HJi2 HJi3 memS0 memS2 memS3.
  assert (Hfa32 : forall c p, frame_addr ly3 c p = frame_addr ly2 c p)
    by (intros c p; unfold frame_addr; rewrite ELF3, ELF2; reflexivity).
  assert (EFA2 : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  pose proof HK3 as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (HTF3 : trans_tframe_at B ly3 S3 W3 mem3 regs SRX_STK TF).
  { apply (srxa_tframe LAWS HRU HRE ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 regs SRX_STK (sp1 - Kc) sp1 Wr TF HAR2 HAR3
      Hperm3 Hfr3 Hfa32); [rewrite Elo3, Elo2; reflexivity | rewrite Ehi3, Ehi2; reflexivity | exact HK3 | exact HWg
      | lia | lia | exact Htfg | exact HTF2]. }
  assert (Hrom3 : trans_rom_view_rd W3 mem3).
  { intros a Ha. rewrite <- (Hrom2 a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He'].
    apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He'].
    intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
    unfold TG.G_HARNESS_LO in Gh. lia. }
  split; [|split; [exact HTF3 | exact Hrom3]].
  set (FL := flag_addr lyc SRX_CID pos) in *.
  destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 SRX_CID pos F FL HAR2 Hfrs Hbl
    HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  assert (HSo : forall o, In o SRX_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold SRX_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  split; [replace (k + (e + e3)) with (k + e + e3) by lia; exact HJ3|].
  split; [lia|].
  split; [rewrite Hfr3; exact Hfrs|].
  split; [exact (Permutation_trans Hperm3 Hperm)|].
  split; [rewrite ELF3, <- ELF2; exact HlyF|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
  split.
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 mem2 W3 mem3 (spZ regs - SRX_STK)
      (spZ regs) (sp1 - Kc) sp1 (srx_wr b) Wr (dkg_nf SRX_CID F FL)).
    - lia.
    - lia.
    - intros c p. unfold frame_addr. rewrite HlyF. reflexivity.
    - intros f Hf. rewrite Hfrs. right. exact Hf.
    - exact Hbl.
    - exact N1.
    - exact N3.
    - exact HK.
    - exact HK3.
    - lia.
    - lia.
    - intros a Ha. left. exact (HWs a Ha). }
  split.
  { rewrite Forall_forall in Hsaved |- *. cbv beta in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    pose proof (HSo o Ho) as Hob. apply srxa_rdword. intros i Hi.
    apply K1; lia. }
  transitivity (rdword (aview segs (w_H W2) mem2) (F + SRX_FBYTES - 8)); [|exact HFLw].
  apply srxa_rdword. intros i Hi.
  apply (K4 SRX_CID pos _ Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes SRX_CID) with 128.
    unfold SRX_FBYTES. lia.
  - intros Hw. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos (F + SRX_FBYTES - 8 + i) HAR2 Hin2);
      [rewrite EFA2; change (fs_frame_bytes SRX_CID) with 128; unfold SRX_FBYTES; lia|].
    exact (trans_g_img _ (HWg _ Hw)).
Qed.

End kit.

(* The bytes on_announce and on_data store are bytes of G. *)
Lemma srxa_onann_G : forall Bw b a, onann_wr Bw b a -> inG TG.G_HARNESS a.
Proof.
  intros Bw b a H.
  unfold onann_wr in H. unfold slost_wr in H. unfold wake_wr in H. unfold maybeon_wr in H. unfold iosend_wr in H.
  unfold notice_wr in H.
  srxa_split H.
Qed.

Lemma srxa_ondata_G : forall Bw b a, ondata_wr Bw b a -> inG TG.G_HARNESS a.
Proof.
  intros Bw b a H.
  unfold ondata_wr in H. unfold iosend_wr in H. unfold notice_wr in H.
  srxa_split H.
Qed.
