(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 613 of its 658 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/SlotPass9G.v, with its module paths, module names, addresses and numbers changed; 521 of its 718 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass1.v, with its module names changed; 287 of its 331 lines of code are new or changed and 674 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass2.v, with its module paths and addresses changed; 1518 of its 1667 lines of code are new or changed and 182 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessGlue HarnessFrame SlotReads SlotEntryRun SlotEntry.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotPass1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c pthread_mutex_lock_ro_c pthread_mutex_unlock_ro_c pthread_mutex_lock_ro pthread_mutex_unlock_ro.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass9G SlotPass2Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_no_loss_read_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import check_no_loss_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass2Check SlotPass2Aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require RelayCap relay_remove_b_aux SlotPass4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotMove SlotWalk SlotPass2Mv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require SlotRI3 SlotNcWt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Cells.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition p2_dregs (E : sstart) (t K SA HA : Z) (R : bvmap 5 word) : Prop :=
  YK11.getr R 1 = Z_to_bv 64 0x1402c /\ YK11.getr R 2 = Z_to_bv 64 (slot_sp E) /\
  YK11.getr R 3 = YK11.getr (ss_regs E) 3 /\ YK11.getr R 4 = YK11.getr (ss_regs E) 4 /\
  YK11.getr R 8 = Z_to_bv 64 (ss_p E + K) /\ YK11.getr R 9 = Z_to_bv 64 HA /\
  YK11.getr R 10 = Z_to_bv 64 SA /\ YK11.getr R 18 = Z_to_bv 64 SA /\ YK11.getr R 19 = Z_to_bv 64 0x31018 /\
  YK11.getr R 20 = Z_to_bv 64 G_RELAY_LO /\ YK11.getr R 21 = Z_to_bv 64 DIV10 /\ YK11.getr R 22 = Z_to_bv 64 t /\
  YK11.getr R 23 = Z_to_bv 64 (ss_n E - K) /\ YK11.getr R 24 = Z_to_bv 64 (slot_sp E + 16) /\
  YK11.getr R 25 = Z_to_bv 64 4 /\ YK11.getr R 26 = Z_to_bv 64 (G_S + 4) /\
  YK11.getr R 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4).

Definition p2_drain_st (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (rc : RunCeil) (E : sstart)
    (RI : res_inv) (t K : Z) (c : config) : Prop :=
  exists (fx' : FPState) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
         (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat))
         (i : nat) (e : rentry) (h : hsrc) (jj : nat) (R : bvmap 5 word) (m1 : word -> option byte),
    c = mkCfg (@YK11.mkst fx' R (Z_to_bv 64 DRAIN) m1 (seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\ 0 <= t < OPS_MAX /\ 0 <= K <= ss_n E /\ ss_n E < INPUT_MAX /\
    aa_MR (API rc) L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
    (exists vm, md = with_vmmaps vm (ss_md E)) /\ ro_agree (ms_segs B) mem /\
    image_kept (rc := rc) B E mem /\ stack_mid B E mem /\
    driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem /\
    globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out /\ 0 <= nfd <= t + 1 /\
    output_at (rc := rc) B L A mem nout cap out /\ relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj /\
    (length es <= 4)%nat /\ slot_cost es hj <= K /\ RI E K (view_of G (bv_unsigned out) es hj) L A /\
    bv_unsigned nout = 0 /\
    nth_error es i = Some e /\ nth_error hj i = Some (h, jj) /\ re_eof e = 0 /\
    p2_dregs E t K (G + 56 * Z.of_nat i) (G_S + SRC_SIZE * Z.of_nat jj) R /\
    munch [(slot_sp E + 40, slot_sp E + 48); (0x3101c, 0x31020)] mem m1 /\ wmono (ms_segs B) mem m1 /\
    ro_agree (ms_segs B) m1 /\
    rw_cells (ms_segs B) m1 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] /\
    rw_cells (ms_segs B) m1 (slot_sp E + 40) [C8 (Z_to_bv 64 0)].

Lemma MI_op2_scan : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract -> pthread_mutex_lock_contract ->
  walk_at (ss_pl E) (t + 1) K ->
  MI (rc := rc) B (API rc) E RI t K 0x13d90 (fun _ hj no regs => no = 0 /\ disp_src 2 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => LI (rc := rc) B (API rc) E RI (t + 1) K c' \/ p2_drain_st B API rc E RI t K c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF CB LCK HWK HM.
  pose proof (pthread_mutex_lock_ro_of LCK) as LCKR.
  destruct (p2_ff B API LS SH SK ra empty rc fx j E CS HF)
    as (SEG & ERR & ETP & FA & PL & SPLO & SPHI & ALIGN & TP & MR0 & PIN & NI).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x13d90 =? TAIL_CHECK) || (0x13d90 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (HNO & DS & (B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22 & R9 & R15).
  destruct DS as [(_ & jj & HJJ & OJ & ->)|([HPF|HO1] & _)]; [|vm_compute in HPF; discriminate|discriminate].
  set (HA := G_S + SRC_SIZE * Z.of_nat jj) in *.
  pose proof HREL as ((tail & TL & TB) & GIN & GFR & HES & NDF & FDR & PA & NDH & ZH & NDA).
  assert (SRCI : exists h, In (h, jj) hj /\ src_at (rc := rc) B L A mem HA h).
  { pose proof OJ as OI'. unfold slot_open in OI'. apply existsb_exists in OI'. destruct OI' as (q & HQ & HE).
    apply Nat.eqb_eq in HE. subst q. apply in_map_iff in HQ. destruct HQ as ([h q] & EQ & HQ). cbn in EQ. subst q.
    destruct (pair_find _ _ _ _ _ (h, jj) PA HQ) as [e HP0]. exists h. split; [exact HQ|].
    destruct HP0 as (SRC & _). cbv zeta in SRC. cbn [fst snd] in SRC. exact SRC. }
  destruct SRCI as (h & HIN & SRC). pose proof SRC as (SC1 & _ & _ & _ & FDH & _).
  set (SP := slot_sp E) in *.
  assert (SPB1 : 2 ^ 20 <= SP) by (unfold SP, slot_sp, SLOT_FRAME; unfold SLOT_STACK in SPLO; lia).
  assert (SPB2 : SP + 192 <= 2 ^ 63) by (unfold SP, slot_sp, SLOT_FRAME; lia).
  assert (HAB : 0x31040 <= HA /\ HA + 96 <= 0x311c0) by (unfold HA, G_S, SRC_SIZE; lia).
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GER & GRG).
  assert (RN : ov_read_bytes rsegs mem (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length es))))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C4 (Z_to_bv 64 (Z.of_nat (length es)))) G8 eq_refl) as X.
    rewrite SEG in X. exact X. }
  assert (RF : ov_read_bytes rsegs mem (Z_to_bv 64 HA) 4 = Some (le4 (Z_to_bv 64 (hs_fd h)))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C4 (Z_to_bv 64 (hs_fd h))) SC1 eq_refl) as X.
    rewrite SEG in X. change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
  assert (RG : ov_read_bytes rsegs mem (Z_to_bv 64 0x30ff0) 8 = Some (le8 (Z_to_bv 64 G))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C8 (Z_to_bv 64 G)) G10 eq_refl) as X. rewrite SEG in X. exact X. }
  assert (HW : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es).
  { eapply Forall_impl; [|exact HES]. intros e0 He0. exact (p2_entry_scan rc B L A mem e0 He0). }
  assert (WSP : forall a, SP + 16 <= a < SP + 88 -> writable_at rsegs mem a).
  { intros a Ha. rewrite <- SEG. apply (proj2 (proj2 (proj2 HIK))). left. unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (PJ : forall i, 0 <= i < Z.of_nat 8 -> present mem (SP + 40 + i)).
  { intros i Hi. cbn in Hi. apply writable_hi_present; [lia|]. apply WSP. lia. }
  destruct (present_rw_cells rsegs mem (SP + 40) 8 ltac:(lia) ltac:(cbn; lia) PJ) as [junk HJ].
  rewrite SEG in TB, G12, HRO.
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 SP) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 HA) by exact R9.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (SP + 32)) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 DIV10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (ss_n E - K)) by exact R23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 (SP + 16)) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 4) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (G_S + 4)) by exact F26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E9, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    exact (op2_pre LCKR es tail junk G SP HA (hs_fd h) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem
      RN RF RG TB HW Hes FDH HJ SPB1 ltac:(lia) G12 HRO). }
  intros ms1 (can1 & HQ & EQ1).
  destruct HQ as [(HN & a0 & a1 & a2 & s2 & ->)|(i & e & Hi & Hfe & Hpre & [(E1 & a0 & a1 & a2 & ->)|
    (E0 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & RO1 &
     CK1 & C401)])].
  - destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    rewrite <- SEG.
    eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail_regs E t K r));
      [exact HF|exact CB|intros; assumption|exact HWK|]|intros c' HC; left; exact HC].
    exists fx', L, A, R1, mem, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj.
    split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
    split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
    split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
    split; [rewrite SEG; exact HRO|]. split; [exact HIK|]. split; [exact HST|]. split; [exact HDK|].
    split; [exact HGL|]. split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|]. split; [exact HOUT|].
    split; [eapply relay_at_t; [exact HREL|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
    split; [exact Hes|]. split; [exact Hcost|exact HRI].
  - destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    set (m' := write_to_mem mem (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))).
    assert (MU : munch [(SP + 40, SP + 48)] mem m').
    { unfold m'. change (Z_to_bv 64 (SP + 40)) with (wa (SP + 40)).
      eapply munch_write; [apply munch_refl|lia|rewrite length_le8; lia|cbn [inside]; left; rewrite length_le8; lia]. }
    assert (WM : wmono rsegs mem m') by (unfold m'; apply wmono_write, wmono_refl).
    assert (MU16 : munch [(SP + 32, SP + 32 + 16)] mem m').
    { eapply munch_weaken; [|exact MU]. intros x HX. cbn [outside] in HX |- *. destruct HX as (H1 & _).
      split; [lia|exact I]. }
    assert (HKc : @YM05.alloc_ceiling rc <= SP - (SLOT_STACK - SLOT_FRAME))
      by (unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
    assert (HKc' : @YM05.alloc_ceiling rc + 65344 <= SP) by (unfold SLOT_STACK, SLOT_FRAME in HKc; lia).
    assert (RM : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) SP (fun a => SP + 40 <= a < SP + 48) (fun _ => False)
        L A mem md L A m' md).
    { apply (rmid_A B (API rc) _ _ _ _ L A mem md m' [(SP + 40, SP + 48)] HMR HWF HBD (hg_img_low B SEG) HKc).
      - intros a Ha. destruct Ha as [Ha|Ha]; apply (proj2 (proj2 (proj2 HIK))); unfold lib_scratch;
          [left; unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|right; exact Ha].
      - exact MU.
      - rewrite SEG. exact WM.
      - intros x Hx HO. right. cbn [outside] in HO. lia.
      - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO). cbn [outside]. split; [lia|exact I].
      - intros p n k HP Hk0 HO. exfalso. apply HO. cbn [outside].
        destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n k HMR HP Hk0) as (_ & _ & X & _). split; [lia|exact I]. }
    destruct (p2_kept B API LS SH SK ra empty rc fx j E CS L A mem md L A m' md _ _ (target_addrs G (bv_unsigned out) es hj)
      (target_addrs G (bv_unsigned out) (map short_entry es) hj) HF HMR HWF HIK HST HDK RM)
      as (IK' & ST' & DK').
    + intros a Ha. right. left. lia.
    + intros a Ha. destruct (Z_lt_le_dec a (SP + 40)) as [L1|L1]; [left; lia|].
      destruct (Z_lt_le_dec a (SP + 48)) as [L2|L2]; [right|left; lia].
      rewrite SEG. apply WM. apply WSP. lia.
    + intros q [].
    + intros x Hx. left. rewrite short_target in Hx. exact Hx.
    + intros q m Hq. rewrite short_target. destruct (in_dec Z.eq_dec q (target_addrs G (bv_unsigned out) es hj)) as [X|X];
        [right; exact X|left; split; [exact Hq|exact X]].
    + pose proof RM as (MR' & _).
      assert (RO' : ro_agree (ms_segs B) m').
      { rewrite SEG. apply (g9_ro_munch [(SP + 40, SP + 48)] mem m' MU); [|exact HRO].
        intros a HA0. cbn [outside]. split; [|exact I].
        destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 20)) as [L1|L1]; [lia|].
        pose proof (bv_unsigned_in_range 64 a) as AR. change (bv_modulus 64) with (2 ^ 64) in AR.
        pose proof (ro_addr_hi (bv_unsigned a) ltac:(lia)) as X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
      assert (S16 : @YM05.alloc_ceiling rc + 8 <= SP + 32) by lia.
      rewrite <- SEG.
      eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail_regs E t K r));
        [exact HF|exact CB|intros; assumption|exact HWK|]|intros c' HC; left; exact HC].
      exists fx', L, A, R1, m', md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, (map short_entry es), hj.
      split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
      split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
      split; [exact MR'|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
      split; [exact RO'|]. split; [exact IK'|]. split; [exact ST'|]. split; [exact DK'|].
      split; [rewrite length_map; eapply tail_globals; [exact S16|unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia
        |rewrite ERR; lia|exact MU16|rewrite SEG; exact WM|exact HGL]|].
      split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|]. split; [eapply tail_output; [exact S16|exact MU16|exact HOUT]|].
      split; [eapply relay_at_t; [eapply tail_relay; [exact S16|unfold G_S; lia|exact MU16|rewrite SEG; exact WM|exact HREL]
        |cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
      split; [rewrite length_map; exact Hes|]. split; [rewrite short_cost; exact Hcost|rewrite short_view; exact HRI].
  - destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    apply SR_ret. right. unfold p2_drain_st.
    exists fx', L, A, mem, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj, i, e, h, jj, R1, m1.
    split; [rewrite SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
    split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
    split; [rewrite SEG; exact HRO|]. split; [exact HIK|]. split; [exact HST|]. split; [exact HDK|].
    split; [exact HGL|]. split; [exact Hnfd|]. split; [exact HOUT|]. split; [exact HREL|].
    split; [exact Hes|]. split; [exact Hcost|]. split; [exact HRI|]. split; [exact HNO|].
    split; [exact Hi|]. split; [exact (p2_pair_idx rc B L A mem t es hj i e h jj PA NDF Hi HIN (eq_sym Hfe))|].
    split; [exact E0|].
    split; [unfold p2_dregs; repeat split; geq X1|].
    split; [exact MU1|]. split; [rewrite SEG; exact WM1|]. split; [rewrite SEG; exact RO1|].
    split; rewrite SEG; assumption.
Qed.

Definition p2_drain_RV_s (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z)
    (es : list rentry) (hj : list (hsrc * nat)) (e : rentry) (h : hsrc) (CAP : Z) (live : bool) (fin : dstate)
    (fa : dadr) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall (e' : rentry) (h' : hsrc) (OUT' : Z),
    (live = true -> live_at L' A' (resolveF qs (da_out fa)) OUT' (ds_ocap fin)) ->
    (live = false -> OUT' = out /\ ds_ocap fin = CAP) ->
    entry_links L' A' qs fa e' -> src_links L' A' qs (known_at L A) fa h' ->
    re_cap e' = ds_cap fin -> ent_ka e' = ds_ka fin -> hl_cap (hs_expected h') = ds_ecap fin ->
    forall G' out' es' hj',
      (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
      (exists p1 p2, pend_view hj = p1 ++ map snd (hl_recs (hs_pending h)) :: p2 /\ pend_view hj' = p1 ++ [] :: p2) ->
      (exists k1 k2, ek_view hj = k1 ++ ekeys_hl (hs_expected h) ++ k2 /\
         ek_view hj' = k1 ++ ekeys_hl (hs_expected h) ++ ekeys (lines (hs_state h) (bzs (pending_stream h))) ++ k2) ->
      (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
      nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A'
        (p2_dr_dels out CAP OUT' (ds_ocap fin) e e' (hs_expected h) (hs_expected h'))
        (p2_dr_adds out CAP OUT' (ds_ocap fin) e e' (hs_expected h) (hs_expected h')) ->
      List.NoDup (map fst (blocks L' A')) ->
      (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
         In (ptr_addr L p) (rv_nc (view_of G out es hj)) ->
         ~ In (ptr_addr L p) (map fst (p2_dr_dels out CAP OUT' (ds_ocap fin) e e' (hs_expected h) (hs_expected h'))) ->
         In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
      CF.SlotRI3.ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= drain_wt es hj e h fin ->
      RI E k (view_of G' out' es' hj') L' A'.

Definition p2_drain_res_s (F : ResFormT) (RI : res_inv) : Prop :=
  forall E k L A G out es hj i e h j live mx NO CAP,
    RI E k (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> 0 <= k <= ss_n E ->
    slot_cost es hj <= k -> pair_cost e (h, j) <= k ->
    NoDup (target_addrs G out es hj) -> nth_error es i = Some e -> nth_error hj i = Some (h, j) -> re_eof e = 0 ->
    CF.SlotPass4.p4_ent_blk L A e -> CF.SlotPass4.p4_src_blk L A h -> (CAP = 0 \/ In (out, CAP) (blocks L A)) ->
    0 <= mx <= 255 -> 0 <= NO <= CAP -> CAP <= TBBYTES ->
    hl_recs (hs_expected h) = [] -> ecap_ok (hl_cap (hs_expected h)) ->
    Z.of_nat (length (pending_stream h)) < WRITE_MAX * OPS_MAX ->
    0 <= re_cap e -> 0 <= ent_ka e -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
    re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 -> Z.of_nat (length (re_U e)) <= re_used e ->
    (re_hp e <> 0 -> re_kh e <> 0) -> ds_ocap (drain_fin live mx NO CAP e h) <= SlotCaps3.NMAX ->
    (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) -> (length es <= 4)%nat -> (length hj <= 4)%nat ->
    ecap_ok (ds_ecap (drain_fin live mx NO CAP e h)) /\
    res_tr F (p2_drain_RV_s RI E k L A G out es hj e h CAP live (drain_fin live mx NO CAP e h)
        (drain_adr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h))) A
      (drain_tr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)).

Definition p2_cnl_RV_s (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z)
    (es : list rentry) (hj : list (hsrc * nat)) (h : hsrc) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall (E' H' : hlist),
    sh_real L' qs (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
      (map (shr (known_at L A)) (hl_recs (hs_expected h)))) H' ->
    sh_live A' qs (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
      (map (shr (known_at L A)) (hl_recs (hs_expected h)))) ->
    hl_recs E' = [] -> hl_v E' = hl_v (hs_expected h) -> hl_cap E' = hl_cap (hs_expected h) ->
    NoDup (texts H') -> texts H' = upds (texts (hs_held h)) (texts (hs_expected h)) ->
    (forall x m, In (x, m) (blocks L' A') ->
       (In (x, m) (blocks L A) /\ (0 < m -> ~ In x (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)))) \/
       In x (list_blocks H')) ->
    (forall x m, In (x, m) (blocks L A) -> 0 < m ->
       ~ In x (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)) -> ~ In x (list_blocks H')) ->
    (forall x m, In (x, m) (blocks L A) -> ~ In x (hs_blocks h) -> In (x, m) (blocks L' A')) ->
    CF.SlotPass4.p4_src_blk L' A' (set_exp_held h E' H') ->
    forall G' out' es' hj',
      (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
      pend_view hj' = pend_view hj ->
      (exists k1 k2, ek_view hj = k1 ++ ekeys_hl (hs_expected h) ++ k2 /\ ek_view hj' = k1 ++ k2) ->
      (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
      nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A'
        (p2_arr_dels (hs_held h) H') (p2_arr_adds (hs_held h) H') ->
      List.NoDup (map fst (blocks L' A')) ->
      (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
         In (ptr_addr L p) (rv_nc (view_of G out es hj)) ->
         ~ In (ptr_addr L p) (map fst (p2_arr_dels (hs_held h) H')) ->
         In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
      CF.SlotRI3.ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= cnl_wt es hj h ->
      RI E k (view_of G' out' es' hj') L' A'.

Definition p2_cnl_res_s (F : ResFormT) (RI : res_inv) : Prop :=
  forall E k L A G out es hj i e h j,
    RI E k (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> 0 <= k <= ss_n E ->
    slot_cost es hj <= k ->
    NoDup (target_addrs G out es hj) -> nth_error es i = Some e -> nth_error hj i = Some (h, j) ->
    CF.SlotPass4.p4_src_blk L A h ->
    hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
    res_tr F (p2_cnl_RV_s RI E k L A G out es hj h) A
      (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h)))).

Lemma p2_bzs_map : forall Ls, Forall zrange Ls -> map bzs (map (map (Z_to_bv 8)) Ls) = Ls.
Proof. induction 1 as [|l Ls Hl _ IH]; [reflexivity|]. cbn [map]. rewrite bzs_lits by exact Hl. f_equal. exact IH. Qed.

Lemma p2_ekeys_app : forall (l l' : hlist) Ls,
  map snd (hl_recs l') = map snd (hl_recs l) ++ map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  ekeys_hl l' = ekeys_hl l ++ ekeys Ls.
Proof.
  intros l l' Ls H Z. unfold ekeys_hl, ekeys.
  rewrite <- (map_map snd bzs (hl_recs l')), H, map_app, (map_map snd bzs), (p2_bzs_map Ls Z), map_app, concat_app.
  reflexivity.
Qed.

Lemma p2_ek_split : forall (hj : list (hsrc * nat)) i p,
  ek_view (firstn i hj ++ p :: skipn (S i) hj) =
    ek_view (firstn i hj) ++ ekeys_hl (hs_expected (fst p)) ++ ek_view (skipn (S i) hj).
Proof. intros hj i p. unfold ek_view. rewrite map_app, concat_app. reflexivity. Qed.

Lemma p2_sbs_enc : forall e e', p2_sbs e e' -> entry_nc e' = entry_nc e.
Proof. intros e e' (_ & _ & _ & _ & A5 & _ & A7 & A8 & _). unfold entry_nc. rewrite A5, A7, A8. reflexivity. Qed.

Lemma p2_sbs_cnc : forall l l', Forall2 p2_sbs l l' -> concat (map entry_nc l') = concat (map entry_nc l).
Proof.
  intros l l' H. induction H as [|a b l l' Hab H IH]; [reflexivity|]. cbn [map concat].
  rewrite (p2_sbs_enc a b Hab), IH. reflexivity.
Qed.

Ltac p2g ha :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn in Hk;
  unfold CF.relay_finish_b_c.G_THREAD_UP, CF.SlotInv.G_WAKE0, CheckRep.G_GONE, send_line_c.G_DEAD, CF.relay_add_b_c.G_NSRC,
    CF.op_add_c.G_NFD, CF.relay_add_b_c.G_SRC, relay_event_c.G_LOCK, send_line_c.G_BROKEN, send_line_c.G_EINTR,
    send_line_c.G_OUTV, ha, HarnessRep.G_S, SRC_SIZE;
  split; [first [apply in_G_bss; clear - Hk; lia|apply g9_in_listen; clear - Hk; lia]|repeat split; clear - Hk; lia].

Ltac p2_chain X5 PRc X3 k :=
  etransitivity; [apply (getr_of_eqv _ _ _ X5); reflexivity|];
  etransitivity; [exact (PRc k (p2_cs k eq_refl))|];
  etransitivity; [apply (getr_of_eqv _ _ _ X3); reflexivity|].

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
  pose proof (pthread_mutex_unlock_ro_of ULK) as ULKR.
  destruct (p2_ff B API LS SH SK ra empty rc fx j E CS HF)
    as (SEG & ERR & ETP & FA & PL & SPLO & SPHI & ALIGN & TP & MR0 & PIN & NI).
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (GNO : forall L0 A0 m0 md0 a, aa_MR (API rc) L0 A0 m0 md0 -> in_globals frame_G a -> ~ owned B L0 A0 a)
    by (unfold frame_allocator in FA; tauto).
  pose proof (@YM05.alloc_ceiling_value rc) as (AC & ACmod). pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (EOFF : ms_errno_off B = -164) by (unfold errno_addr in ERR; lia).
  set (SP := slot_sp E) in *. set (SA := G + 56 * Z.of_nat i) in *. set (HA := G_S + SRC_SIZE * Z.of_nat jj) in *.
  assert (SPB1 : @YM05.alloc_ceiling rc + 65344 <= SP) by (unfold SP, slot_sp, SLOT_FRAME; unfold SLOT_STACK in SPLO; lia).
  assert (SPB2 : SP + 192 <= 2 ^ 63) by (unfold SP, slot_sp, SLOT_FRAME; lia).
  assert (SPA : SP mod 16 = 0) by (unfold SP, slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia).
  assert (HKc : @YM05.alloc_ceiling rc <= SP - (SLOT_STACK - SLOT_FRAME)) by (unfold SLOT_STACK, SLOT_FRAME; lia).
  pose proof HREL as ((tail & TL & TB) & GIN & GFR & HES & NDF & FDR & PA & NDH & ZH & NDA).
  destruct (p2_f2_nth_l _ _ _ _ _ PA Hi) as ([h0 jj0] & Hh0 & PO). rewrite Hh in Hh0. injection Hh0 as <- <-.
  destruct PO as (SRC & JJ4 & FDH & EOFC & SSK & NDT & EXP0 & PN & PC & PS & EC & HC). cbv zeta in *. cbn [fst snd] in *.
  destruct (EOFC EOF) as (SKO & WU).
  pose proof (p2_nth_forall _ _ _ _ HES Hi) as EOK.
  assert (GB : 4096 <= G /\ G + 896 <= @YM05.alloc_ceiling rc) by (destruct GFR as (G0 & G1 & _); unfold SRC_TABLE, SRC_ENTRY in G1; lia).
  assert (IL : (i < length es)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  assert (HAB : 0x31040 <= HA /\ HA + 96 <= 0x311c0) by (unfold HA, G_S, SRC_SIZE; lia).
  destruct DR as (D1 & D2 & D3 & D4 & D8 & D9 & D10 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
  set (Es0 := fun a => SP + 40 <= a < SP + 48 \/ 0x3101c <= a < 0x31020).
  assert (R0 : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) SP Es0 (fun _ => False) L A mem md L A m1 md).
  { apply (rmid_A B (API rc) _ _ _ _ L A mem md m1 [(SP + 40, SP + 48); (0x3101c, 0x31020)] HMR HWF HBD
      (hg_img_low B SEG) HKc).
    - intros a Ha. destruct Ha as [Ha|Ha]; apply (proj2 (proj2 (proj2 HIK))); unfold lib_scratch;
        [left; unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|right; exact Ha].
    - exact MU1.
    - exact WM1.
    - intros x Hx HO. right. unfold Es0. cbn [outside] in HO. lia.
    - intros a HO. cbn [outside].
      pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO).
      split; [lia|]. split; [|exact I].
      intros HX. exact (GNO _ _ _ _ a HMR (in_G_bss a ltac:(lia)) HO).
    - intros p n k HP Hk0 HO. exfalso. apply HO.
      destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n k HMR HP Hk0) as (_ & _ & X & _).
      pose proof (ax_blocks_img AX L A mem md p n k HMR HP Hk0) as NIm. cbn [outside].
      split; [lia|]. split; [|exact I].
      intros HX. apply NIm. exact (proj1 (PL _ (in_G_bss (ptr_addr L p + k) ltac:(lia)))). }
  assert (KB : forall q, kept_block Es0 (fun _ => False) L A q).
  { intros q. split; [intros []|]. intros k a Hq Ha HE. unfold Es0 in HE.
    destruct (p2_blk rc fx B (API rc) L A mem md q k a FA HMR Hq Ha) as (NIm & _ & X2).
    destruct HE as [HE|HE]; [lia|]. apply NIm. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(lia)))). }
  destruct (p2_entry_rmid rc fx B (API rc) _ _ _ _ L A mem md L A m1 md e FA HMR R0 EOK (fun q _ => KB q))
    as (e1 & SB1 & EOK1).
  assert (SRC1 : src_at (rc := rc) B L A m1 HA h).
  { apply (p2_src_rmid rc fx B (API rc) _ _ _ _ L A mem md L A m1 md HA h FA SEG HKc HMR R0 SRC); [|intros q _; apply KB].
    intros k Hk0. split; [apply PL; apply in_G_bss; unfold HA, G_S, SRC_SIZE in *; lia|unfold Es0; lia]. }
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GER & HCL & HBR & HGN &
    HDD & HEI & HGG & HMX).
  assert (TW : forall a cs, rw_cells (ms_segs B) mem a cs ->
    disjoint_from [(SP + 40, SP + 48); (0x3101c, 0x31020)] a (Z.of_nat (cells_size cs)) -> rw_cells (ms_segs B) m1 a cs).
  { intros a cs H D. eapply rw_cells_transport; [exact H|exact MU1|exact WM1|exact D]. }
  assert (GCL1 : rw_cells (ms_segs B) m1 G_CLIENT [C4 (Z_to_bv 64 cl)]).
  { apply TW; [exact (proj2 (hg_cut _ _ _ [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 cl)] G1))|cbn; unfold G_CLIENT; lia]. }
  assert (GBR1 : rw_cells (ms_segs B) m1 G_BROKEN [C1 (Z_to_bv 8 br)]) by (apply TW; [exact G4|cbn; unfold G_BROKEN; lia]).
  assert (GDD1 : rw_cells (ms_segs B) m1 G_DEAD [C1 (Z_to_bv 8 dd)]) by (apply TW; [exact G6|cbn; unfold G_DEAD; lia]).
  assert (GEI1 : rw_cells (ms_segs B) m1 G_EINTR [C1 (Z_to_bv 8 ei)]) by (apply TW; [exact G7|cbn; unfold G_EINTR; lia]).
  assert (GOV1 : rw_cells (ms_segs B) m1 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out])
    by (apply TW; [exact G11|cbn; unfold G_OUTV; lia]).
  assert (GER1 : exists ev, rw_cells (ms_segs B) m1 (errno_addr B) [C4 ev]).
  { destruct GER as [ev GE]. exists ev. apply TW; [exact GE|rewrite ERR; cbn; lia]. }
  destruct HOUT as ((O & junk & OC) & CAPB).
  assert (OC1 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ O = []) \/
    (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L A) /\
     fresh_block B (bv_unsigned out) (bv_unsigned cap) /\ bytes_at (ms_segs B) m1 (bv_unsigned out) (O ++ junk) /\
     Z.of_nat (length O) = bv_unsigned nout /\ Z.of_nat (length junk) = bv_unsigned cap - bv_unsigned nout)).
  { destruct OC as [OC|(C0 & C1 & C2 & C3 & C4' & C5 & C6)]; [left; exact OC|right].
    split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [|split; assumption].
    eapply bytes_at_transport; [exact C4'|exact MU1|].
    apply entry_disjoint_pts; [repeat constructor; cbn; lia|rewrite length_app; lia|].
    intros x Hx. rewrite length_app in Hx.
    destruct (p2_blk rc fx B (API rc) L A mem md _ _ (x - bv_unsigned out) FA HMR C2 ltac:(lia)) as (NIm & _ & X2).
    replace (bv_unsigned out + (x - bv_unsigned out)) with x in NIm by lia.
    cbn [outside]. split; [lia|]. split; [|exact I]. intros HX. apply NIm.
    exact (proj1 (PL _ (in_G_bss x ltac:(lia)))). }
  destruct (p2_others rc B L A mem t nfd G (bv_unsigned out) es hj i e h jj HREL Hi Hh) as (fs & os & OTH).
  assert (OTH1 : others_at B m1 jj (re_fd e1) fs os).
  { destruct SB1 as (SF & _). rewrite SF. destruct OTH as (OL1 & OL2 & OT). split; [exact OL1|]. split; [exact OL2|].
    intros k Hk0 NK. destruct (OT k Hk0 NK) as (OC0 & OR). split; [|exact OR].
    apply TW; [exact OC0|cbn; unfold G_S, SRC_SIZE; lia]. }
  assert (HSA : bv_unsigned (YK11.getr R 10) = SA) by (rewrite D10; apply unsigned_lit; unfold SA; lia).
  pose proof (p2_table_split rc B L A mem es tail G i e HES Hi TL TB) as TS.
  pose proof (proj2 (hg_cut _ _ _ [_] [_; _] TS)) as TS2.
  pose proof (proj1 (hg_cut _ _ _ [_] [_] TS2)) as TSE.
  cbn [cells_size csize] in TSE. replace (G + Z.of_nat (56 * i + 0)) with SA in TSE by (unfold SA; lia).
  assert (TSE1 : rw_cells (ms_segs B) m1 SA [CB 56 (entry_bytes e1)]).
  { rewrite (p2_sbs_bytes e e1 SB1).
    apply (rmid_rw_block B (API rc) BW _ _ _ _ L A mem md L A m1 md G 896 SA _ R0 GIN ltac:(lia) (fun X => X) TSE);
      [unfold SA; lia|cbn; unfold SA; lia|].
    intros k Hk0. cbn in Hk0. replace (SA + k) with (G + (SA - G + k)) by lia.
    destruct (KB G) as (_ & KE). apply (KE 896 (SA - G + k) GIN). unfold SA. lia. }
  pose proof EOK as (EH1 & EH2 & EP1 & EP2 & EFD & ECAP & EUL & EU6 & EUZ & EBUF & ENH & EHP & END1 & END2 & EKS).
  assert (PCB : pair_cost e (h, jj) < 2 ^ 26)
    by exact (dc_cost B L A mem es hj e (h, jj) K (ss_n E) HES (p2_combine_nth es hj i e (h, jj) Hi Hh) Hcost
      (proj2 Hk) Hn).
  assert (NH19 : 19 * Z.of_nat (length (re_keys e)) <= keys_total (re_keys e)).
  { apply keys_total_count. eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & _ & (L14 & _) & _). exact L14. }
  assert (PCK : pair_cost e (h, jj) <= K).
  { eapply Z.le_trans; [|exact Hcost]. apply (pair_cost_le_slot es hj e (h, jj) (p2_combine_nth es hj i e (h, jj) Hi Hh)).
    eapply Forall_impl; [|exact HES]. intros e0 (_ & _ & _ & _ & _ & _ & U0 & _). lia2. }
  pose proof (p2_sbs_cost e e1 (h, jj) SB1) as PC1.
  pose proof SB1 as (SF1 & SE1 & SS1 & SP1 & SBU1 & SU1 & SC1' & SH1 & SKH1 & SP2 & SK1 & SUU1 & SJ1).
  set (Ls := lines (hs_state h) (bzs (pending_stream h))) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))) in *.
  set (live := send_live cl br dd TOT) in *.
  assert (DI : drain_init (bv_unsigned nout) (bv_unsigned cap) e1 h = drain_init (bv_unsigned nout) (bv_unsigned cap) e h).
  { unfold drain_init, ent_ka. rewrite SC1', SUU1, SS1, SH1, SKH1, (p2_sbs_texts e e1 SB1). reflexivity. }
  assert (MKA : forall f : Z -> adrF,
      map (fun k => f (key_addr k)) (re_keys e1) = map (fun k => f (key_addr k)) (re_keys e)).
  { intros f. pose proof (f_equal (map (fun x : Z * list byte => f (fst x))) SK1) as X. rewrite !map_map in X.
    exact X. }
  assert (DSA : drain_start (known_at L A) (known_at L A (bv_unsigned out)) e1 h =
      drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h).
  { unfold drain_start. rewrite SBU1, SH1, (MKA (known_at L A)). reflexivity. }
  assert (DTR : drain_tr live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e1 h 0
      (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e1 h) =
      drain_tr live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h 0
      (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h))
    by (unfold drain_tr, drain_go; rewrite DI, DSA; reflexivity).
  assert (DFN : drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e1 h =
      drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)
    by (unfold drain_fin, drain_go; rewrite DI; reflexivity).
  assert (DFA : drain_adr live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e1 h 0
      (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e1 h) =
      drain_adr live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h 0
      (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h))
    by (unfold drain_adr, drain_go; rewrite DI, DSA; reflexivity).
  assert (OCX : bv_unsigned cap = 0 \/ In (bv_unsigned out, bv_unsigned cap) (blocks L A))
    by (destruct OC1 as [(C0 & _)|(_ & _ & IN & _)]; [left; exact C0|right; exact IN]).
  pose proof (bv_unsigned_in_range 64 mx) as MXR. pose proof (bv_unsigned_in_range 64 cap) as CPR.
  assert (NB0 : List.NoDup (map fst (blocks L A))).
  { pose proof (NDB L A mem md HMR) as X. first [exact X|exact (proj1 (NoDup_ListNoDup _) X)]. }
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
  assert (SPR : spZ R = SP) by (unfold spZ; rewrite D2; apply unsigned_lit; lia2).
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
    - rewrite ERR. unfold G_LOCK_HI. lia2.
    - exact RO1.
    - intros a Ha. apply PL. apply in_G_bss. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in Ha. lia2.
    - intros a Ha. apply PL, g9_in_listen. unfold G_CLIENT in Ha. lia2.
    - intros a Ha. exact (proj1 (entry_errno_image B SEG ETP EOFF a Ha)).
    - exact JJ4.
    - match goal with |- context [bv_unsigned (getr R ?r)] => replace (bv_unsigned (getr R r)) with SA by (symmetry; exact HSA) end.
      split; [exact GIN|]. split; [exact GFR|]. unfold SA, SRC_TABLE, SRC_ENTRY.
      split; [lia2|]. split; [lia2|]. replace (G + 56 * Z.of_nat i - G) with (Z.of_nat i * 56) by lia2. apply Z_mod_mult.
    - match goal with |- context [bv_unsigned (getr R ?r)] => replace (bv_unsigned (getr R r)) with SA by (symmetry; exact HSA) end.
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
  rewrite DFN in DC1, DC5, DC6. rewrite DTR in LQ2, RF2. rewrite DFA in OLK, ELK, SLK.
  pose proof R0 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC0).
  set (TA0 := bv_unsigned out :: G :: entry_blocks e ++ hs_blocks h) in *.
  set (TF0 := bv_unsigned out :: entry_blocks e ++ hs_blocks h) in *.
  set (Ed := fun a => G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32 \/
    HA + 12 <= a < HA + SRC_SIZE \/ SA <= a < SA + SRC_ENTRY \/
    (exists v n, In (v, n) (blocks L A) /\ In v TF0 /\ v <= a < v + n)).
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RD0 PRd]. rewrite SPR in RD0.
  assert (RD1 : rmid B (API rc) DRAIN_K SP Ed (fun q => In q TF0) L A m1 md L2 A2 mem2 md2).
  { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ RD0).
    - intros a [SW|[SR0|[HR0|(q & m & Hq & Hm & Ha)]]].
      + destruct SW as [X|[X|[X|(LT & X)]]]; [left; exact X|right; left; exact X|right; right; left; exact X|].
        right; right; right; right; right. destruct OC1 as [(C0 & _)|(C0 & _ & IN & _)]; [lia2|].
        exists (bv_unsigned out), (bv_unsigned cap). split; [exact IN|]. split; [left; reflexivity|lia2].
      + replace (bv_unsigned (PropExec.getr R 10)) with SA in SR0 by (symmetry; exact HSA).
        right; right; right; right; left. exact SR0.
      + right; right; right; left. exact HR0.
      + right; right; right; right; right. exists q, m. split; [exact Hm|]. split; [|exact Ha].
        rewrite (p2_sbs_blocks e e1 SB1) in Hq. right. exact Hq.
    - intros q [(_ & ->)|Hq]; [left; reflexivity|]. rewrite (p2_sbs_blocks e e1 SB1) in Hq. right. exact Hq. }
  assert (EDB : forall a, Ed a -> in_img B a \/ (0 <= a < @YM05.alloc_ceiling rc /\ ~ in_img B a /\
      exists v n, In (v, n) (blocks L A) /\ In v TA0 /\ v <= a < v + n)).
  { intros a [X|[X|[X|[X|[X|(v & n & Hv & Hvt & Ha)]]]]];
      try (left; apply (proj1 (PL a ltac:(apply in_G_bss; unfold G_BROKEN, G_EINTR, G_OUTV, HA, G_S, SRC_SIZE in *; lia2)))).
    - unfold SA, SRC_ENTRY in X. right.
      destruct (p2_blk rc fx B (API rc) L A mem md G 896 (a - G) FA HMR GIN ltac:(lia2)) as (NIa & B0 & B1).
      replace (G + (a - G)) with a in NIa by lia2.
      split; [lia2|]. split; [exact NIa|]. exists G, 896. split; [exact GIN|]. split; [right; left; reflexivity|].
      lia2.
    - right. destruct (p2_blk rc fx B (API rc) L A mem md v n (a - v) FA HMR Hv ltac:(lia2)) as (NIa & B0 & B1).
      replace (v + (a - v)) with a in NIa by lia2. split; [lia2|]. split; [exact NIa|]. exists v, n.
      split; [exact Hv|]. split; [|exact Ha]. destruct Hvt as [<-|Hvt]; [left; reflexivity|right; right; exact Hvt]. }
  assert (EDI : forall a, Ed a -> in_img B a -> G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/
      G_OUTV + 8 <= a < G_OUTV + 32 \/ HA + 12 <= a < HA + SRC_SIZE).
  { intros a HE HI. destruct HE as [X|[X|[X|[X|HE]]]]; [left; exact X|right; left; exact X|right; right; left; exact X
      |right; right; right; exact X|].
    destruct (EDB a (or_intror (or_intror (or_intror (or_intror HE))))) as [_|(_ & NIa & _)]; [|contradiction].
    exfalso. destruct HE as [X|(v & n & Hv & _ & Ha)].
    - unfold SA, SRC_ENTRY in X.
      destruct (p2_blk rc fx B (API rc) L A mem md G 896 (a - G) FA HMR GIN ltac:(lia2)) as (NIa & _).
      replace (G + (a - G)) with a in NIa by lia2. contradiction.
    - destruct (p2_blk rc fx B (API rc) L A mem md v n (a - v) FA HMR Hv ltac:(lia2)) as (NIa & _).
      replace (v + (a - v)) with a in NIa by lia2. contradiction. }
  assert (EDH : forall a, Ed a -> a < @YM05.alloc_ceiling rc).
  { intros a HE. destruct (EDB a HE) as [HI|(X & _)]; [exact (proj2 (hg_img_low B SEG a HI))|lia2]. }
  assert (RDw : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) SP Ed (fun q => In q TF0) L A m1 md L2 A2 mem2 md2).
  { apply (rmid_widen B (API rc) DRAIN_K SP); [exact HM1|rewrite p2_drain_k; unfold SLOT_STACK, SLOT_FRAME; lia2|lia2
      |exact HKc|lia2| | |exact RD1].
    - intros a Ha. apply SC0. unfold sk. left. exact Ha.
    - intros a Ha HE. pose proof (EDH a HE). lia2. }
  pose proof RDw as (HM2 & HWF2 & HBD2 & LY2 & LN2 & PA2 & SV2 & Z02 & OW2 & MD2 & BY2 & BK2 & SC2).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  assert (ST2 : stk rsegs mem2 (SP - 96) SP).
  { split; [lia2|]. split; [lia2|]. intros a Ha.
    assert (WA : writable_at rsegs mem2 a) by (rewrite <- SEG; apply SC2; unfold sk; left; unfold SLOT_STACK, SLOT_FRAME; lia2).
    split; [exact WA|]. destruct (writable_hi_present mem2 a ltac:(lia2) WA) as [b HB].
    exists b. unfold mrd, wa. rewrite HB. reflexivity. }
  assert (NRO : RoAdapt.not_ro rsegs (SP - 96) 96).
  { intros k Hk1. unfold wa. apply ro_addr_hi. lia2. }
  assert (CK2 : rw_cells (ms_segs B) mem2 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]).
  { apply (rmid_rw_img B (API rc) AX _ _ _ _ L A m1 md L2 A2 mem2 md2 0x31018 _ (hg_img_low B SEG) HKc HM1 RDw CK1).
    intros k Hk1. cbn in Hk1. assert (HG : in_globals G_reply (0x31018 + k)) by (apply in_G_bss; lia2).
    split; [exact (PL _ HG)|]. intros HE. destruct (EDI _ HE (proj1 (PL _ HG))) as [X|[X|[X|X]]];
      unfold G_BROKEN, G_EINTR, G_OUTV, HA, G_S, SRC_SIZE in X; lia2. }
  pose proof (dc_read B L2 A2 mem2 HA h2 SRC2 HPR2) as RD24.
  match goal with |- context [PropExec.getr R ?r] => replace (PropExec.getr R r) with (Z_to_bv 64 0x1402c) by (symmetry; exact D1) end.
  assert (P2 : reg_get regs2 2 = Z_to_bv 64 SP) by exact (eq_trans (PRd 2 ltac:(unfold callee_saved; lia2)) D2).
  assert (P9 : reg_get regs2 9 = Z_to_bv 64 HA) by exact (eq_trans (PRd 9 ltac:(unfold callee_saved; lia2)) D9).
  assert (P19 : reg_get regs2 19 = Z_to_bv 64 0x31018) by exact (eq_trans (PRd 19 ltac:(unfold callee_saved; lia2)) D19).
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh2|exact Hl2|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite P2, P9, P19.
    rewrite SEG in RD24, CK2, RO2.
    apply (op2_mid ULKR CNR SP HA); [lia2|lia2|unfold HA, G_S in *; lia2|unfold HA, G_S, SRC_SIZE in *; lia2
      |exact ST2|exact NRO|exact CK2|exact RD24|exact RO2]. }
  intros ms1 (can1 & (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MU3 & WM3 &
    RO3 & ST3 & CK3) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R3 & -> & X3).
  assert (KU : forall q, kept_block (fun a => 0x3101c <= a < 0x31020) (fun _ => False) L2 A2 q).
  { intros q. split; [intros []|]. intros k a Hq Ha HE.
    destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 q k a FA HM2 Hq Ha) as (NIa & _).
    apply NIa. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(lia2)))). }
  assert (Ru : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) SP (fun a => 0x3101c <= a < 0x31020) (fun _ => False)
      L2 A2 mem2 md2 L2 A2 m3 md2).
  { apply (rmid_A B (API rc) _ _ _ _ L2 A2 mem2 md2 m3 [(SP - 96, SP); (0x3101c, 0x31020)] HM2 HWF2 HBD2
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
      intros HX. apply NIm. exact (proj1 (PL _ (in_G_bss (ptr_addr L2 p + k) ltac:(lia2)))). }
  assert (SRC3 : src_at (rc := rc) B L2 A2 m3 HA h2).
  { apply (p2_src_rmid rc fx B (API rc) _ _ _ _ L2 A2 mem2 md2 L2 A2 m3 md2 HA h2 FA SEG HKc HM2 Ru SRC2);
      [|intros q _; apply KU].
    intros k Hk1. split; [apply PL; apply in_G_bss; unfold HA, G_S, SRC_SIZE in *; lia2|unfold HA, G_S, SRC_SIZE; lia2]. }
  assert (TM3 : forall a cs, rw_cells (ms_segs B) mem2 a cs ->
      disjoint_from [(SP - 96, SP); (0x3101c, 0x31020)] a (Z.of_nat (cells_size cs)) -> rw_cells (ms_segs B) m3 a cs).
  { intros a cs H D. rewrite SEG in H |- *. eapply rw_cells_transport; [exact H|exact MU3|exact WM3|exact D]. }
  assert (TD2 : forall a cs, rw_cells (ms_segs B) m1 a cs -> in_globals G_reply a ->
      (forall k, 0 <= k < Z.of_nat (cells_size cs) -> in_globals G_reply (a + k) /\ ~ Ed (a + k)) ->
      rw_cells (ms_segs B) mem2 a cs).
  { intros a cs H _ D. apply (rmid_rw_img B (API rc) AX _ _ _ _ L A m1 md L2 A2 mem2 md2 a cs (hg_img_low B SEG)
      HKc HM1 RDw H). intros k Hk1. destruct (D k Hk1) as [D1' D2']. split; [exact (PL _ D1')|exact D2']. }
  assert (NEDG : forall a, in_globals G_reply a -> ~ (G_BROKEN <= a < G_BROKEN + 1) -> ~ (G_EINTR <= a < G_EINTR + 1) ->
      ~ (G_OUTV + 8 <= a < G_OUTV + 32) -> ~ (HA + 12 <= a < HA + SRC_SIZE) -> ~ Ed a).
  { intros a HG N1 N2 N3 N4 HE. destruct (EDI a HE (proj1 (PL a HG))) as [X|[X|[X|X]]]; contradiction. }
  assert (GOV2 : rw_cells (ms_segs B) mem2 G_OUTV [C8 mx; C8 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout);
      C8 (if live then Z_to_bv 64 CAP2 else cap); C8 (if live then Z_to_bv 64 OUT2 else out)]).
  { destruct live; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (LV1 eq_refl)))))))|exact (proj1 (LV0 eq_refl))]. }
  assert (GOV3 := TM3 _ _ GOV2 ltac:(cbn; unfold G_OUTV; lia2)).
  destruct (outv_bytes _ _ _ _ _ _ GOV3) as (BNO3 & BOU3).
  assert (GG3 : bytes_at (ms_segs B) m3 G_GONE [Z_to_bv 8 gn]).
  { apply p2_rw_bytes1. apply TM3; [|cbn; unfold G_GONE; lia2].
    apply TD2; [apply TW; [exact G5|cbn; unfold G_GONE; lia2]|apply in_G_bss; unfold G_GONE; lia2|].
    intros k Hk1. cbn in Hk1. assert (HG : in_globals G_reply (G_GONE + k)) by (apply in_G_bss; unfold G_GONE; lia2).
    split; [exact HG|]. apply NEDG; [exact HG|unfold G_GONE, G_BROKEN; lia2|unfold G_GONE, G_EINTR; lia2
      |unfold G_GONE, G_OUTV; lia2|unfold G_GONE, HA, G_S, SRC_SIZE; lia2]. }
  assert (C403 : rw_cells (ms_segs B) m3 (SP + 40) [C8 (Z_to_bv 64 0)]).
  { apply TM3; [|cbn; lia2].
    apply (rmid_rw_hi B (API rc) (SLOT_STACK - SLOT_FRAME) SP Ed (fun q => In q TF0) L A m1 md L2 A2 mem2 md2 (SP + 40) _);
      [lia2|rewrite ERR; lia2|exact HM1
      |exact RDw|exact C401|lia2|cbn; lia2|]. intros k Hk1 HE. pose proof (EDH _ HE). lia2. }
  pose proof (dc_O_nil B L A m1 _ _ _ O junk OC1 HNO) as O0.
  assert (BOB2 : bytes_at (ms_segs B) mem2 OUT2 (if live then LB else [])).
  { apply (dc_ob_bytes B mem2 live LB O junk2 out OUT2); [|exact O0|].
    - intros LT. exact (proj1 (proj2 (proj2 (proj2 (proj2 (LV1 LT)))))).
    - intros LF. exact (proj2 (proj2 (LV0 LF))). }
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV & _).
  destruct (dc_counts B L A mem es hj e h h2 jj K (ss_n E) HES (p2_combine_nth es hj i e (h, jj) Hi Hh) Hcost
    (proj2 Hk) Hn SSK NDT EXP0 HOV SKO WU HEX2 HHL2) as (PL26 & TOT26 & NDH2 & EN26 & HB22).
  assert (TOT26' : TOT < 2 ^ 26) by exact TOT26.
  destruct (dc_no_loss B gn cl br dd live h h2 e2 Ls LB nout out OUT2 CAP2 G L2 A2 HGN (proj1 HGG) (proj2 HGG) LVD
    EXP0 HEX2 (dc_lines_range h) LBE HNO (fun LF => proj2 (proj2 (LV0 LF)))
    (fun LT => let X := LV1 LT in conj (proj1 X) (conj (proj1 (proj2 (proj2 X))) (proj1 (proj2 (proj2 (proj2 X)))))) NDB2)
    as (DN1 & DN2 & DN3 & DN4 & DN5 & DN6).
  assert (BOB3 : bytes_at (ms_segs B) m3 (bv_unsigned (if live then Z_to_bv 64 OUT2 else out)) (if live then LB else [])).
  { rewrite DN2. destruct live eqn:LV.
    - pose proof (LV1 eq_refl) as (TL1 & _ & INO & FRO & _). rewrite SEG in BOB2 |- *.
      assert (TOTP : 0 < TOT).
      { pose proof (dc_live gn cl br dd TOT HGN (proj1 HGG) (proj2 HGG)) as DL. rewrite <- LVD in DL.
        assert (TN : 0 <= TOT) by (unfold TOT; lia2).
        destruct (Z.eqb_spec TOT 0) as [X|X]; [rewrite andb_false_r in DL; discriminate|lia2]. }
      eapply bytes_at_transport; [exact BOB2|exact MU3|].
      pose proof (with_nul_bzs Ls LB LBE) as LBL. pose proof FRO as (FR1 & FR2 & FR3).
      apply (entry_disjoint_pts [(SP - 96, SP); (0x3101c, 0x31020)]);
        [apply Forall_forall; intros iv Hiv; destruct Hiv as [<-|[<-|[]]]; cbn; lia2|rewrite LBL; change (0 < TOT); exact TOTP|].
      intros x Hx. cbn [outside]. split; [intros HX; lia2|]. split; [|exact I].
      intros HX. apply (FR3 (x - OUT2) ltac:(lia2)). replace (OUT2 + (x - OUT2)) with x by lia2.
      exact (proj1 (PL _ (in_G_bss x ltac:(lia2)))).
    - apply p2_bytes_nil. pose proof (bv_unsigned_in_range 64 out) as OR. change (bv_modulus 64) with (2 ^ 64) in OR.
      rewrite (proj2 (proj2 (LV0 eq_refl))). lia2. }
  pose proof (split_at es i e IL) as ESP. rewrite (nth_error_nth es i e Hi) in ESP.
  assert (IHJ : (i < length hj)%nat) by (apply nth_error_Some; rewrite Hh; discriminate).
  pose proof (split_at hj i (h, jj) IHJ) as HJP. rewrite (nth_error_nth hj i (h, jj) Hh) in HJP.
  pose proof (Forall2_firstn' _ i es hj PA) as PApre. pose proof (Forall2_skipn' _ (S i) es hj PA) as PApost.
  destruct (p2_forall_sub _ i es HES) as [ESpre _]. destruct (p2_forall_sub _ (S i) es HES) as [_ ESpost].
  assert (OLD : forall x m, In (x, m) (blocks L A) -> 0 < m -> ~ In x TA0 ->
      In (x, m) (blocks L2 A2) /\ ~ In x (hs_blocks h2) /\ ~ In x (entry_blocks e2) /\ x <> OUT2).
  { intros x m Hx Hm NT.
    assert (N1 : x <> bv_unsigned out) by (intros ->; apply NT; left; reflexivity).
    assert (N2 : ~ In x (entry_blocks e1 ++ hs_blocks h)).
    { rewrite (p2_sbs_blocks e e1 SB1). intros X. apply NT. right. right. exact X. }
    destruct (NEW2 x m Hx Hm N1 N2) as (Y1 & Y2 & Y3).
    split; [exact (SURV2 x m Hx N1 N2)|]. split; [exact Y3|]. split; [exact Y2|exact Y1]. }
  assert (OTX : forall x, In x (p2_oth es hj i) -> ~ In x TA0 /\ In x (target_addrs G (bv_unsigned out) es hj)).
  { intros x Hx. destruct (p2_oth_out G (bv_unsigned out) es hj i e h jj x NDA Hi Hh Hx) as (N0 & I0).
    split; [|exact I0]. intros X. apply N0. destruct X as [<-|[<-|X]]; [right; left; reflexivity|left; reflexivity|].
    right; right; exact X. }
  assert (OTHP : forall x, In x (p2_oth es hj i) -> exists m, 0 < m /\ In (x, m) (blocks L A)).
  { intros x Hx. unfold p2_oth in Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
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
          exact (p2_hb_pos rc B L A mem _ (fst p) S0 x Hxl). }
  assert (FR : forall l, Forall2 p2_sbs l l) by (induction l as [|a l IHl]; constructor; [apply p2_sbs_refl|exact IHl]).
  destruct (p2_repl_facts (skipn (S i) es) (firstn i es) i e2 (p2_len_firstn es i IL)) as (_ & _ & NE2i).
  destruct (p2_repl_facts (skipn (S i) hj) (firstn i hj) i (h2, jj) (p2_len_firstn hj i IHJ)) as (_ & _ & NH2i).
  pose proof (p2_oth_repl es hj i (firstn i es) (skipn (S i) es) e2 (h2, jj) IL IHJ (FR _) (FR _)) as OTHEQ2.
  set (es2 := firstn i es ++ e2 :: skipn (S i) es) in *.
  set (hj2 := firstn i hj ++ (h2, jj) :: skipn (S i) hj) in *.
  assert (LEN2 : length es2 = length es).
  { unfold es2. rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. clear - IL. lia. }
  assert (LHJ : length hj = length es) by (symmetry; exact (Forall2_length PA)).
  assert (LHJ2 : length hj2 = length hj).
  { unfold hj2. rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. clear - IHJ. lia. }
  assert (ND2T : NoDup (target_addrs G OUT2 es2 hj2)).
  { apply (p2_nd_join G OUT2 es2 hj2 i e2 h2 jj NE2i NH2i NDB2);
      [rewrite OTHEQ2; exact (p2_oth_nd G (bv_unsigned out) es hj i e h jj NDA Hi Hh)|].
    intros x Hx. rewrite OTHEQ2 in Hx. destruct (OTX x Hx) as (NT & _). destruct (OTHP x Hx) as (m & Hm & Hxm).
    destruct (OLD x m Hxm Hm NT) as (Hx2 & NH2x & NE2x & NOx). intros [EQ|[EQ|X]].
    - apply NT. rewrite <- EQ. right; left; reflexivity.
    - exact (NOx (eq_sym EQ)).
    - apply in_app_or in X. destruct X as [X|X]; [exact (NE2x X)|exact (NH2x X)]. }
  pose proof (proj1 (NoDup_ListNoDup _) NDA) as NDAl.
  pose proof (proj1 (NoDup_ListNoDup _) ND2T) as ND2Tl.
  destruct (p2_ta_nd _ _ _ _ NDAl) as (NV0 & _).
  destruct (p2_ta_nd _ _ _ _ ND2Tl) as (NV2 & NR2).
  assert (NB2 : List.NoDup (map fst (blocks L2 A2))).
  { pose proof (NDB L2 A2 mem2 md2 HM2) as X. first [exact X|exact (proj1 (NoDup_ListNoDup _) X)]. }
  pose proof (CF.SlotPass4.p4_src_blk_of B L A mem HA h SRC) as (P0P & P0T & P0E & P0H & _).
  pose proof (CF.SlotPass4.p4_src_blk_of B L2 A2 mem2 HA h2 SRC2) as (P2P & P2T & P2E & P2H & _).
  pose proof EOK2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EBUF2 & _ & EHP2 & _).
  assert (CPF : live = false -> ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h) =
      bv_unsigned cap).
  { intros LF. rewrite LF. unfold drain_fin, drain_go. rewrite CF.RelayCap.drain_run_dead. reflexivity. }
  assert (CPT : live = true -> CAP2 = ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)).
  { intros LT. rewrite <- DFN. exact (proj1 (proj2 (LV1 LT))). }
  assert (MV2 : nc_move (view_of G (bv_unsigned out) es hj) L A (view_of G OUT2 es2 hj2) L2 A2
      (p2_dr_dels (bv_unsigned out) (bv_unsigned cap) OUT2
         (ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)) e e2
         (hs_expected h) (hs_expected h2))
      (p2_dr_adds (bv_unsigned out) (bv_unsigned cap) OUT2
         (ds_ocap (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)) e e2
         (hs_expected h) (hs_expected h2))).
  { apply (p2_drain_mv L A L2 A2 G (bv_unsigned out) (bv_unsigned cap) OUT2 _ es es2 hj hj2 (firstn i es)
        (skipn (S i) es) (firstn i hj) (skipn (S i) hj) e e2 h h2 jj ESP HJP eq_refl eq_refl NB0 NB2 NV0 NV2
        HPV2 HPC2 HPA2 HHL2).
      + intros x m Hx Hin.
        destruct (p2_nd_split _ _ _ _ (p2_nodup_sub G (bv_unsigned out) es hj i e h jj NDA Hi Hh)) as (GO0 & GN0 & _).
        assert (NXT : x <> bv_unsigned out /\ ~ In x (entry_blocks e1 ++ hs_blocks h)).
        { rewrite (p2_sbs_blocks e e1 SB1). destruct Hin as [<-|Ho].
          - split; [exact GO0|exact GN0].
          - destruct (p2_oth_out G (bv_unsigned out) es hj i e h jj x NDA Hi Hh Ho) as (N0 & _).
            split; [intros EQ; apply N0; right; left; symmetry; exact EQ|intros X; apply N0; right; right; exact X]. }
        exact (SURV2 x m Hx (proj1 NXT) (proj2 NXT)).
      + exact (proj1 P0P).
      + exact (proj1 P2P).
      + exact P0T.
      + exact P2T.
      + exact (proj1 P0H).
      + exact (proj1 P2H).
      + exact (proj1 P0E).
      + exact (proj1 P2E).
      + intros S m Hm. unfold out_same in S. apply andb_true_iff in S as [S1 S2]. apply Z.eqb_eq in S1, S2.
        destruct OC1 as [(CZ0 & OZ0 & _)|(CZ0 & _ & INq & _)].
        { exfalso. pose proof (p2_low rc B (API rc) L A mem md _ _ HMR Hm) as LW. clear - OZ0 LW. lia. }
        rewrite (p2_uniq L A _ _ _ NB0 Hm INq). destruct live eqn:LV.
        * pose proof (LV1 eq_refl) as (_ & _ & INO & _). rewrite (CPT eq_refl), S2, S1 in INO. exact INO.
        * exact (proj1 (proj1 (proj2 (LV0 eq_refl)) CZ0)).
      + intros tt Hu. unfold out_move_dels in Hu.
        match type of Hu with In _ (if ?b then _ else _) => destruct b eqn:C end; [destruct Hu|].
        destruct Hu as [<-|[]]. apply orb_false_iff in C as [_ C]. apply Z.eqb_neq in C.
        destruct OC1 as [(CZ0 & _)|(_ & _ & INq & _)]; [contradiction|exact INq].
      + intros tt Hu. unfold out_move_adds in Hu.
        match type of Hu with In _ (if ?b then _ else _) => destruct b eqn:C end; [destruct Hu|].
        destruct Hu as [<-|[]]. destruct live eqn:LV.
        * pose proof (LV1 eq_refl) as (_ & _ & INO & _). rewrite <- (CPT eq_refl). exact INO.
        * exfalso. unfold out_same in C. rewrite (CPF eq_refl), (proj2 (proj2 (LV0 eq_refl))), !Z.eqb_refl in C.
          cbn [andb] in C. discriminate.
      + intros CZ0 m Hm. destruct OC1 as [(_ & OZ0 & _)|(CZ1 & _)]; [|clear - CZ0 CZ1; lia].
        pose proof (p2_low rc B (API rc) L A mem md _ _ HMR Hm) as LW. clear - OZ0 LW. lia.
      + intros C. destruct EBUF as [(X & _)|(_ & X & _)]; [contradiction|exact X].
      + intros C. destruct EHP as [(X & _)|(X & _)]; [contradiction|exact X].
      + intros C. destruct EBUF2 as [(X & _)|(_ & X & _)]; [contradiction|exact X].
      + intros C. destruct EHP2 as [(X & _)|(X & _)]; [contradiction|exact X].
      + intros q m Hq. exact (p2_pos rc B (API rc) L A mem md q m HMR Hq).
      + intros q m Hq. exact (p2_pos rc B (API rc) L2 A2 mem2 md2 q m HM2 Hq). }
  assert (SV0 : forall x m, In (x, m) (blocks L A) -> In x (p2_oth es hj i) -> In (x, m) (blocks L2 A2)).
  { intros x m Hx Ho. destruct (OTX x Ho) as (NT & _). apply (SURV2 x m Hx).
    - intros ->. apply NT. left. reflexivity.
    - rewrite (p2_sbs_blocks e e1 SB1). intros X. apply NT. right. right. exact X. }
  assert (OB2 : CF.SlotRI3.nc_sz L2 A2 OUT2 <= TBBYTES).
  { destruct live eqn:LV.
    - pose proof (LV1 eq_refl) as (TL1 & CAPF & INO & _).
      pose proof (CF.RelayCap.drain_ocap_le_tot true (bv_unsigned mx) (bv_unsigned nout)
        (bv_unsigned cap) e1 h (p2_fin_no true (bv_unsigned mx) (bv_unsigned nout)
          (bv_unsigned cap) rc B L A m1 e1 h HA EOK1 SRC1 ltac:(rewrite SS1; exact SKO) ltac:(rewrite SS1, SUU1; exact WU)))
        as OCB.
      rewrite <- CAPF in OCB.
      change (Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h)))))) with TOT in OCB.
      rewrite (CF.SlotNcWt.nw_sz_at L2 A2 _ _ NB2 INO). clear - OCB CAPB HNO TOT26'. unfold TBBYTES in *.
      rewrite HNO in OCB. lia.
    - destruct (LV0 eq_refl) as (_ & LV02 & LV03). rewrite LV03.
      destruct OC1 as [(C0 & O0' & _)|(C0 & _)].
      + rewrite O0', (CF.SlotNcWt.nw_sz_none L2 A2 0); [unfold TBBYTES; lia|].
        intros m Hm. pose proof (p2_low rc B (API rc) L2 A2 mem2 md2 _ _ HM2 Hm) as LW. lia.
      + rewrite (CF.SlotNcWt.nw_sz_at L2 A2 _ _ NB2 (proj1 (LV02 C0))). exact CAPB. }
  assert (NCS2 : CF.SlotRI3.ncs (view_of G OUT2 es2 hj2) L2 A2 <= nc_wt es2 hj2).
  { apply (p2_ncs_wt L2 A2 G OUT2 es2 hj2 NB2); [rewrite (CF.SlotNcWt.nw_sz_at L2 A2 _ _ NB2 GIN2); lia|exact OB2| | |
      rewrite LEN2; exact Hes|rewrite LHJ2, LHJ; exact Hes].
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
        * exact (CF.SlotPass4.p4_blk_sb _ _ _ (CF.SlotPass4.p4_src_blk_of B L A mem _ (fst p) S0)). }
  assert (WT2 : nc_wt es2 hj2 <=
      drain_wt es hj e h (drain_fin live (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) e h)).
  { pose proof EOK2 as (_ & _ & _ & _ & _ & _ & EUL2 & _).
    pose proof DC2 as DC2'. pose proof DC4 as DC4'. rewrite ?DFN in DC2', DC4'.
    unfold es2, hj2.
    rewrite (drain_wt_post (firstn i es) (skipn (S i) es) (firstn i hj) (skipn (S i) hj) e e2 h h2 jj jj _
      DC1 EUL2 DC2' DC5 DC4' HPR2 HPC2 DC6 HEX2 HHL2).
    rewrite <- ESP, <- HJP. lia. }
  assert (RI2 : RI E K (view_of G OUT2 es2 hj2) L2 A2).
  { apply (RPOST L2 A2 qs2 LQ2 RF2 e2 h2 OUT2).
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
    - exact NCS2.
    - exact WT2. }
  assert (COST2 : slot_cost es2 hj2 <= K).
  { unfold es2, hj2. rewrite (p2_cost_app (firstn i es) (firstn i hj) e2 (h2, jj) (skipn (S i) es) (skipn (S i) hj)
      ltac:(rewrite (p2_len_firstn es i IL), (p2_len_firstn hj i IHJ); reflexivity)).
    pose proof (p2_cost_app (firstn i es) (firstn i hj) e (h, jj) (skipn (S i) es) (skipn (S i) hj)
      ltac:(rewrite (p2_len_firstn es i IL), (p2_len_firstn hj i IHJ); reflexivity)) as CO.
    rewrite <- ESP, <- HJP in CO.
    pose proof EOK2 as (_ & _ & _ & _ & _ & _ & EUL2 & _).
    pose proof SRC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV2 & _).
    pose proof SSK2 as SSK2e. rewrite (p2_sbs_texts e e1 SB1) in SSK2e.
    pose proof (p2_pair_cost e e2 h h2 jj SKO WU HOV EUL SKO2 WU2 HOV2 EUL2 HST2 HPR2 NDK2 SSK2e) as PCC.
    clear - CO PCC Hcost. lia. }
  destruct (CRES E K L2 A2 G OUT2 es2 hj2 i e2 h2 jj RI2 NB2 Hk COST2 ND2T NE2i NH2i
    (CF.SlotPass4.p4_src_blk_of B L2 A2 mem2 HA h2 SRC2) HB22) as (bnd2 & RFOK2 & ROOM2 & RPOST2).
  assert (Q1 : PropExec.getr R3 1 = Z_to_bv 64 0x1404c) by geq X3.
  assert (Q2 : PropExec.getr R3 2 = Z_to_bv 64 SP) by geq X3.
  assert (Q4 : PropExec.getr R3 4 = Z_to_bv 64 (ms_tp B)).
  { etransitivity; [apply (getr_of_eqv _ _ _ X3); reflexivity|].
    exact (eq_trans (eq_trans (PRd 4 ltac:(unfold callee_saved; lia2)) D4) TP). }
  assert (Q10 : PropExec.getr R3 10 = Z_to_bv 64 HA) by geq X3.
  assert (Q11 : PropExec.getr R3 11 = Z_to_bv 64 (SP + 40)) by geq X3.
  assert (SPR3 : spZ R3 = SP) by (unfold spZ; change (bv_unsigned (PropExec.getr R3 2) = SP); rewrite Q2; apply unsigned_lit; lia2).
  assert (AT3 : bv_unsigned (PropExec.getr R3 11) = SP + 40) by (rewrite Q11; apply unsigned_lit; lia2).
  assert (SPQ : SP = 16 * (SP / 16)) by (pose proof (Z.div_mod SP 16 ltac:(clear - IL; lia)) as DM; rewrite SPA in DM; clear - DM; lia).
  pose proof (CNL fx' L2 A2 R3 m3 md2 bnd2 h2 jj gn 0 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
    (if live then Z_to_bv 64 OUT2 else out) (if live then LB else [])) as CC. cbv zeta in CC.
  rewrite <- SEG. eapply SR_bind.
  { apply CC.
    - exact SEG.
    - apply (cpk_of_rmid B (API rc) _ _ _ _ L2 A2 mem2 md2 L2 A2 m3 md2 R3 CHECK_NO_LOSS_K Ru INIT2).
      + change (YK0s.ret_ok (PropExec.getr R3 1)). rewrite Q1. apply ret_ok_even. rewrite unsigned_lit by lia2. reflexivity.
      + exact Q4.
      + rewrite SPR3. exact SPA.
      + rewrite SPR3, p2_cnl_k. unfold SLOT_STACK, SLOT_FRAME. lia2.
      + rewrite SPR3. lia2.
      + rewrite p2_cnl_k. lia2.
      + rewrite SPR3, p2_cnl_k. lia2.
      + rewrite SPR3. lia2.
    - exact INIT2.
    - rewrite SEG. exact RO3.
    - intros a Ha. apply PL. apply in_G_bss. unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in Ha. lia2.
    - exact JJ4.
    - exact Q10.
    - exact SRC3.
    - rewrite HHL2. exact NDT.
    - exact EN26.
    - exact HB22.
    - rewrite AT3, SPQ. replace (16 * (SP / 16) + 40) with ((2 * (SP / 16) + 5) * 8) by ring. apply Z_mod_mult.
    - rewrite AT3, SPR3. lia2.
    - rewrite AT3. lia2.
    - rewrite AT3. exact C403.
    - destruct HGN as [-> | ->]; lia2.
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
  clear SPA SPQ.
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RPc) as [RC0 PRc]. rewrite SPR3 in RC0.
  set (Ec := fun a => HA + 64 <= a < HA + 96 \/ SP + 40 <= a < SP + 48 \/
    (exists v n, In (v, n) (blocks L2 A2) /\ In v (hs_blocks h2) /\ v <= a < v + n)) in *.
  pose proof SRC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE3 & LH3 & _).
  assert (RC1 : rmid B (API rc) CHECK_NO_LOSS_K SP Ec (fun q => In q (hs_blocks h2)) L2 A2 m3 md2 L3 A3 mem4 md4).
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
  assert (ECL : forall a, Ec a -> a < SP - (SLOT_STACK - SLOT_FRAME) \/ SP <= a).
  { intros a [X|[X|(v & n & Hv & _ & Ha)]].
    - left. unfold HA, G_S, SRC_SIZE, SLOT_STACK, SLOT_FRAME in *. lia2.
    - right. lia2.
    - left. destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a - v) FA HM2 Hv ltac:(lia2)) as (_ & _ & X2).
      unfold SLOT_STACK, SLOT_FRAME. lia2. }
  assert (Rcw : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) SP Ec (fun q => In q (hs_blocks h2)) L2 A2 m3 md2 L3 A3 mem4 md4).
  { apply (rmid_widen B (API rc) CHECK_NO_LOSS_K SP); [exact HM3|rewrite p2_cnl_k; unfold SLOT_STACK, SLOT_FRAME; lia2
      |lia2|exact HKc|lia2| | |exact RC1].
    - intros a Ha. apply SCu. unfold sk. left. exact Ha.
    - intros a Ha HE. destruct (ECL a HE); lia2. }
  pose proof Rcw as (HM4 & HWF4 & HBD4 & _ & _ & _ & _ & _ & _ & MD4 & _ & _ & SC4).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  assert (NV : (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout) =
      Z_to_bv 64 (if gn =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h2))) else 0))
    by exact (dc_nout_w gn cl br dd live (hs_expected h) (hs_expected h2) Ls LB nout HGN (proj1 HGG) (proj2 HGG) LVD
      EXP0 HEX2 (dc_lines_range h) LBE HNO).
  rewrite NV in BNO4. rewrite AT3 in AT4.
  assert (RDv : ov_read_bytes rsegs mem4 (Z_to_bv 64 (SP + 40)) 8 =
      Some (le8 (Z_to_bv 64 (if gn =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h2))) else 0)))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C8 _) AT4 eq_refl) as X. rewrite SEG in X.
    change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
  match goal with |- context [PropExec.getr R3 ?r] => replace (PropExec.getr R3 r) with (Z_to_bv 64 0x1404c) by (symmetry; exact Q1) end.
  assert (P42 : reg_get regs4 2 = Z_to_bv 64 SP) by exact (eq_trans (PRc 2 ltac:(unfold callee_saved; lia2)) Q2).
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh4|exact Hl4|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite P42.
    rewrite SEG in BNO4. apply (op2_end CSD SP); [exact RDv|exact BNO4]. }
  intros ms5 (can5 & (a1' & ->) & EQ5).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  rewrite <- SEG.
  eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail_regs E t K r));
    [exact HF|exact HCB|intros; assumption|exact HWK|]|intros c5 HC5; exists K; exact HC5].
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ L A mem md L A m1 md L2 A2 mem2 md2 HWF R0 RDw) as R01.
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ L A mem md L2 A2 mem2 md2 L2 A2 m3 md2 HWF R01 Ru) as R012.
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ L A mem md L2 A2 m3 md2 L3 A3 mem4 md4 HWF R012 Rcw) as Rt.
  assert (KX : forall x m a, In (x, m) (blocks L A) -> ~ In x TA0 -> x <= a < x + m ->
      ~ (((Es0 a \/ Ed a) \/ 0x3101c <= a < 0x31020) \/ Ec a)).
  { intros x m a Hx NT Ha.
    destruct (p2_blk rc fx B (API rc) L A mem md x m (a - x) FA HMR Hx ltac:(lia2)) as (NIa & B0 & B1).
    replace (x + (a - x)) with a in NIa by lia2.
    intros [[[X|X]|X]|X].
    - destruct X as [X|X]; [lia2|]. apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(lia2)))).
    - destruct (EDB a X) as [HI|(_ & _ & v & n & Hv & Hvt & Hva)]; [exact (NIa HI)|].
      assert (NE : x <> v) by (intros <-; exact (NT Hvt)).
      destruct (blocks_disjoint B (API rc) L A mem md x m v n HMR Hx Hv NE); lia2.
    - apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(lia2)))).
    - destruct X as [X|[X|(v & n & Hv & Hvh & Hva)]].
      + apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(unfold HA, G_S, SRC_SIZE in *; lia2)))).
      + lia2.
      + destruct (OLD x m Hx ltac:(lia2) NT) as (Hx2 & NH2 & _).
        assert (NE : x <> v) by (intros <-; exact (NH2 Hvh)).
        destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 x m v n HM2 Hx2 Hv NE); lia2. }
  assert (KF : forall x m, In (x, m) (blocks L A) -> 0 < m -> ~ In x TA0 ->
      ~ (((False \/ In x TF0) \/ False) \/ In x (hs_blocks h2))).
  { intros x m Hx Hm NT [[[[]|X]|[]]|X].
    - apply NT. destruct X as [<-|X]; [left; reflexivity|right; right; exact X].
    - exact (proj1 (proj2 (OLD x m Hx Hm NT)) X). }
  assert (KBt : forall q, ~ In q TA0 -> (exists m, 0 < m /\ In (q, m) (blocks L A)) ->
      kept_block (fun a => ((Es0 a \/ Ed a) \/ 0x3101c <= a < 0x31020) \/ Ec a)
        (fun q => ((False \/ In q TF0) \/ False) \/ In q (hs_blocks h2)) L A q).
  { intros q NT (m & Hm & Hq). split; [exact (KF q m Hq Hm NT)|]. intros k a Hkb Ha. exact (KX q k (q + a) Hkb NT ltac:(lia2)). }
  assert (NJ : forall p, In p (firstn i hj ++ skipn (S i) hj) -> snd p <> jj).
  { intros p Hp HE. apply NoDup_ListNoDup in NDH.
    assert (IH' : (i < length (map snd hj))%nat) by (rewrite length_map; apply nth_error_Some; rewrite Hh; discriminate).
    pose proof (proj1 (in_drop_split (map snd hj) i 0%nat (snd p) (proj2 (NoDup_ListNoDup _) NDH) IH')) as X.
    rewrite firstn_map, skipn_map, <- map_app in X. destruct (X (in_map snd _ p Hp)) as (_ & NX). apply NX. rewrite HE.
    rewrite (nth_error_nth (map snd hj) i 0%nat (eq_trans (nth_error_map snd i hj) (f_equal (option_map snd) Hh))).
    reflexivity. }
  assert (KSL : forall p k, In p (firstn i hj ++ skipn (S i) hj) -> (snd p < 4)%nat -> 0 <= k < 96 ->
      img_plain B (G_S + SRC_SIZE * Z.of_nat (snd p) + k) /\
      ~ (((Es0 (G_S + SRC_SIZE * Z.of_nat (snd p) + k) \/ Ed (G_S + SRC_SIZE * Z.of_nat (snd p) + k)) \/
          0x3101c <= G_S + SRC_SIZE * Z.of_nat (snd p) + k < 0x31020) \/ Ec (G_S + SRC_SIZE * Z.of_nat (snd p) + k))).
  { intros p k Hp H4 Hk1. pose proof (NJ p Hp) as NE.
    assert (HG : in_globals G_reply (G_S + SRC_SIZE * Z.of_nat (snd p) + k)) by (apply in_G_bss; unfold G_S, SRC_SIZE; lia2).
    split; [exact (PL _ HG)|]. intros [[[X|X]|X]|X].
    - destruct X as [X|X]; unfold G_S, SRC_SIZE in X; lia2.
    - destruct (EDI _ X (proj1 (PL _ HG))) as [Y|[Y|[Y|Y]]]; unfold G_BROKEN, G_EINTR, G_OUTV, HA, G_S, SRC_SIZE in Y;
        clear - Y NE H4 Hk1; lia.
    - unfold G_S, SRC_SIZE in X. lia2.
    - destruct X as [X|[X|(v & n & Hv & _ & Hva)]].
      + unfold HA, G_S, SRC_SIZE in X. clear - X NE H4 Hk1. lia.
      + unfold G_S, SRC_SIZE in X. lia2.
      + destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (G_S + SRC_SIZE * Z.of_nat (snd p) + k - v) FA HM2 Hv
          ltac:(lia2)) as (NIa & _). apply NIa. replace (v + (G_S + SRC_SIZE * Z.of_nat (snd p) + k - v))
          with (G_S + SRC_SIZE * Z.of_nat (snd p) + k) by lia2. exact (proj1 (PL _ HG)). }
  assert (KPE : forall l, (forall q, In q (concat (map entry_blocks l)) -> In q (p2_oth es hj i)) ->
      Forall (CF.RelayRep.entry_ok (rc := rc) B L A mem) l ->
      forall q, In q (concat (map entry_blocks l)) ->
      kept_block (fun a => ((Es0 a \/ Ed a) \/ 0x3101c <= a < 0x31020) \/ Ec a)
        (fun q => ((False \/ In q TF0) \/ False) \/ In q (hs_blocks h2)) L A q).
  { intros l HO EL q Hq. apply KBt; [exact (proj1 (OTX q (HO q Hq)))|].
    apply in_concat in Hq. destruct Hq as (l0 & Hl & Hql). apply in_map_iff in Hl. destruct Hl as (e0 & <- & He0).
    rewrite Forall_forall in EL. exact (p2_eb_pos rc B L A mem e0 (EL e0 He0) q Hql). }
  assert (KPH : forall l hl, (forall q, In q (concat (map (fun p => hs_blocks (fst p)) hl)) -> In q (p2_oth es hj i)) ->
      Forall2 (pair_ok (rc := rc) B L A mem t) l hl ->
      forall q, In q (concat (map (fun p => hs_blocks (fst p)) hl)) ->
      kept_block (fun a => ((Es0 a \/ Ed a) \/ 0x3101c <= a < 0x31020) \/ Ec a)
        (fun q => ((False \/ In q TF0) \/ False) \/ In q (hs_blocks h2)) L A q).
  { intros l hl HO PF2 q Hq. apply KBt; [exact (proj1 (OTX q (HO q Hq)))|].
    apply in_concat in Hq. destruct Hq as (l0 & Hl & Hql). apply in_map_iff in Hl. destruct Hl as (p & <- & Hp).
    destruct (pair_find _ _ _ _ _ p PF2 Hp) as [e0 (S0 & _)]. cbv zeta in S0.
    exact (p2_hb_pos rc B L A mem _ (fst p) S0 q Hql). }
  assert (KSP : forall l hl, (forall p, In p hl -> In p (firstn i hj ++ skipn (S i) hj)) ->
      Forall2 (pair_ok (rc := rc) B L A mem t) l hl ->
      forall p k, In p hl -> 0 <= k < 96 ->
      img_plain B (G_S + SRC_SIZE * Z.of_nat (snd p) + k) /\
      ~ (((Es0 (G_S + SRC_SIZE * Z.of_nat (snd p) + k) \/ Ed (G_S + SRC_SIZE * Z.of_nat (snd p) + k)) \/
          0x3101c <= G_S + SRC_SIZE * Z.of_nat (snd p) + k < 0x31020) \/ Ec (G_S + SRC_SIZE * Z.of_nat (snd p) + k))).
  { intros l hl HI PF2 p k Hp Hk1. destruct (pair_find _ _ _ _ _ p PF2 Hp) as [e0 (_ & J4 & _)].
    exact (KSL p k (HI p Hp) J4 Hk1). }
  destruct (p2_pairs_rmid rc fx B (API rc) _ _ _ _ L A mem md L3 A3 mem4 md4 t (firstn i es) (firstn i hj) FA SEG HKc
    HMR Rt PApre ESpre
    (KPE _ (fun q Hq => in_or_app _ _ _ (or_introl Hq)) ESpre)
    (KPH _ _ (fun q Hq => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hq)))))) PApre)
    (KSP _ _ (fun p Hp => in_or_app _ _ _ (or_introl Hp)) PApre)) as (pre' & SBpre & EOpre & PApre').
  destruct (p2_pairs_rmid rc fx B (API rc) _ _ _ _ L A mem md L3 A3 mem4 md4 t (skipn (S i) es) (skipn (S i) hj) FA SEG
    HKc HMR Rt PApost ESpost
    (KPE _ (fun q Hq => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hq)))) ESpost)
    (KPH _ _ (fun q Hq => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hq))))))
      PApost)
    (KSP _ _ (fun p Hp => in_or_app _ _ _ (or_intror Hp)) PApost)) as (post' & SBpost & EOpost & PApost').
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ L2 A2 mem2 md2 L2 A2 m3 md2 L3 A3 mem4 md4 HWF2 Ru Rcw) as Rum.
  destruct (p2_nd_split _ _ _ _ NDB2) as (NG2 & NGL & NOL & NDE2 & NDH2' & DEH).
  assert (KE2 : forall q, In q (entry_blocks e2) ->
      kept_block (fun a => 0x3101c <= a < 0x31020 \/ Ec a) (fun q => False \/ In q (hs_blocks h2)) L2 A2 q).
  { intros q Hq. split; [intros [[]|X]; exact (DEH q Hq X)|]. intros k a Hkb Ha HE.
    destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 q k a FA HM2 Hkb Ha) as (NIa & B0 & B1).
    destruct HE as [X|[X|[X|(v & n & Hv & Hvh & Hva)]]].
    - apply NIa. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(lia2)))).
    - apply NIa. exact (proj1 (PL _ (in_G_bss (q + a) ltac:(unfold HA, G_S, SRC_SIZE in *; lia2)))).
    - lia2.
    - assert (NE : q <> v) by (intros <-; exact (DEH q Hq Hvh)).
      destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 q k v n HM2 Hkb Hv NE); lia2. }
  destruct (p2_entry_rmid rc fx B (API rc) _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 e2 FA HM2 Rum EOK2 KE2)
    as (e3 & SB3 & EOK3).
  destruct (p2_sbs_maps _ _ SBpre) as (_ & _ & _ & LPRE0). rewrite (p2_len_firstn es i IL) in LPRE0.
  set (h3 := set_exp_held h2 E3 H3) in *.
  destruct (p2_repl_facts post' pre' i e3 LPRE0) as (_ & _ & NE3).
  destruct (p2_repl_facts (skipn (S i) hj) (firstn i hj) i (h3, jj) (p2_len_firstn hj i IHJ)) as (_ & _ & NH3).
  pose proof (p2_oth_repl es hj i pre' post' e3 (h3, jj) IL IHJ SBpre SBpost) as OTHEQ.
  pose proof (p2_sbs_blocks e2 e3 SB3) as ENB3.
  assert (TA0S : forall v, In v TA0 -> In v (target_addrs G (bv_unsigned out) es hj)).
  { intros v Hv. apply (p2_mid_in G (bv_unsigned out) es hj i e h jj v Hi Hh).
    destruct Hv as [<-|[<-|Hv]]; [right; left; reflexivity|left; reflexivity|right; right; exact Hv]. }
  assert (LE3S : forall x, In x (list_blocks E3) -> In x (list_blocks (hs_expected h2))).
  { intros x Hx. unfold list_blocks in Hx |- *. rewrite E3R, E3C, E3V in Hx. cbn [map] in Hx. rewrite app_nil_r in Hx.
    apply in_or_app. left. exact Hx. }
  assert (HB3 : forall x, In x (hs_blocks h3) -> In x (hs_blocks h2) \/ In x (list_blocks H3)).
  { intros x Hx. unfold h3, hs_blocks in Hx. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held] in Hx.
    apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [left; apply p2_hb_pend; exact Hx|].
    apply in_app_or in Hx. destruct Hx as [[<-|[]]|Hx]; [left; apply p2_hb_part|].
    apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [left; apply p2_hb_exp, LE3S; exact Hx|right; exact Hx]. }
  assert (HB23 : forall x, In x (hs_blocks h2) -> ~ In x (map fst (hl_recs (hs_expected h2)) ++ list_blocks (hs_held h2)) ->
      In x (hs_blocks h3)).
  { intros x Hx NR. unfold h3, hs_blocks. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
    unfold hs_blocks in Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx|].
    apply in_or_app; right. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx|].
    apply in_or_app; right. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
    - apply in_or_app; left. unfold list_blocks in Hx |- *. rewrite E3R, E3C, E3V. cbn [map]. rewrite app_nil_r.
      apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact Hx|]. exfalso. apply NR. apply in_or_app. left. exact Hx.
    - exfalso. apply NR. apply in_or_app. right. exact Hx. }
  assert (KEPT : image_kept (rc := rc) B E mem4 /\ stack_mid B E mem4 /\
      driver_kept B E (target_addrs G (bv_unsigned (if live then Z_to_bv 64 OUT2 else out)) (pre' ++ e3 :: post')
        (firstn i hj ++ (h3, jj) :: skipn (S i) hj)) L3 A3 mem4).
  { apply (p2_kept B API LS SH SK ra empty rc fx j E CS L A mem md L3 A3 mem4 md4 _ _
      (target_addrs G (bv_unsigned out) es hj) _ HF HMR HWF HIK HST HDK Rt).
  - intros a [[[X|X]|X]|X].
    + destruct X as [X|X]; [right; left; lia2|left; apply in_G_bss; lia2].
    + destruct (EDB a X) as [HI|(XA & NIa & v & n & Hv & Hvt & Hva)].
      * left. destruct (EDI a X HI) as [Y|[Y|[Y|Y]]]; apply in_G_bss; unfold G_BROKEN, G_EINTR, G_OUTV, HA, G_S, SRC_SIZE in *;
          lia2.
      * exact (p2_es_blk rc fx B (API rc) SP _ L A mem md v n a FA HMR Hv (TA0S v Hvt) Hva).
    + left. apply in_G_bss. lia2.
    + destruct X as [X|[X|(v & n & Hv & Hvh & Hva)]].
      * left. apply in_G_bss. unfold HA, G_S, SRC_SIZE in *. lia2.
      * right. left. lia2.
      * right. right. destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a - v) FA HM2 Hv ltac:(lia2)) as (NIa & B0 & B1).
        replace (v + (a - v)) with a in NIa by lia2. split; [lia2|]. split; [exact NIa|].
        intros x m Hx NT. destruct (Z_le_gt_dec m 0) as [M0|M0]; [lia2|].
        destruct (OLD x m Hx ltac:(lia2) (fun Y => NT (TA0S x Y))) as (Hx2 & NH2 & _).
        assert (NE : x <> v) by (intros <-; exact (NH2 Hvh)).
        destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 x m v n HM2 Hx2 Hv NE); lia2.
  - intros a Ha. destruct (Z_lt_le_dec a (SP + 40)) as [La|La]; [left|destruct (Z_lt_le_dec a (SP + 48)) as [Lb|Lb]].
    + intros [[[X|X]|X]|X].
      * destruct X as [X|X]; lia2.
      * pose proof (EDH a X). lia2.
      * lia2.
      * destruct X as [X|[X|(v & n & Hv & _ & Hva)]]; [unfold HA, G_S, SRC_SIZE in X; lia2|lia2|].
        destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a - v) FA HM2 Hv ltac:(lia2)) as (_ & _ & B1). lia2.
    + right. eapply cells_writable; [exact AT4|cbn; lia2].
    + left. intros [[[X|X]|X]|X].
      * destruct X as [X|X]; lia2.
      * pose proof (EDH a X). lia2.
      * lia2.
      * destruct X as [X|[X|(v & n & Hv & _ & Hva)]]; [unfold HA, G_S, SRC_SIZE in X; lia2|lia2|].
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
      apply p2_hb_held. exact HH3. }
  destruct KEPT as (IK4 & ST4 & DK4).
  assert (KN2 : forall q k x, In (q, k) (blocks L2 A2) -> ~ In q (hs_blocks h2) -> q <= x < q + k ->
      ~ (0x3101c <= x < 0x31020 \/ Ec x)).
  { intros q k x Hq NQ Hx. destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 q k (x - q) FA HM2 Hq ltac:(lia2))
      as (NIa & B0 & B1). replace (q + (x - q)) with x in NIa by lia2.
    intros [X|[X|[X|(v & n & Hv & Hvh & Hva)]]].
    - apply NIa. exact (proj1 (PL _ (in_G_bss x ltac:(lia2)))).
    - apply NIa. exact (proj1 (PL _ (in_G_bss x ltac:(unfold HA, G_S, SRC_SIZE in *; lia2)))).
    - lia2.
    - assert (NE : q <> v) by (intros <-; exact (NQ Hvh)).
      destruct (blocks_disjoint B (API rc) L2 A2 mem2 md2 q k v n HM2 Hq Hv NE); lia2. }
  assert (TG : forall a cs, rw_cells (ms_segs B) mem a cs ->
      (forall k, 0 <= k < Z.of_nat (cells_size cs) -> in_globals G_reply (a + k) /\ ~ (G_BROKEN <= a + k < G_BROKEN + 1) /\
         ~ (G_EINTR <= a + k < G_EINTR + 1) /\ ~ (G_OUTV + 8 <= a + k < G_OUTV + 32) /\
         ~ (HA + 12 <= a + k < HA + SRC_SIZE) /\ ~ (0x3101c <= a + k < 0x31020)) ->
      rw_cells (ms_segs B) mem4 a cs).
  { intros a cs H D. apply (rmid_rw_img B (API rc) AX _ _ _ _ L A mem md L3 A3 mem4 md4 a cs (hg_img_low B SEG) HKc HMR
      Rt H).
    intros k Hk1. destruct (D k Hk1) as (HG & N1 & N2 & N3 & N4 & N5). pose proof (proj1 (PL _ HG)) as HI.
    pose proof (in_img_low B SEG _ HI) as LOW. split; [exact (PL _ HG)|]. intros [[[X|X]|X]|X].
    - destruct X as [X|X]; [lia2|exact (N5 X)].
    - destruct (EDI _ X HI) as [Y|[Y|[Y|Y]]]; contradiction.
    - exact (N5 X).
    - destruct X as [X|[X|(v & n & Hv & _ & Hva)]]; [apply N4; unfold HA, G_S, SRC_SIZE in *; lia2|lia2|].
      destruct (p2_blk rc fx B (API rc) L2 A2 mem2 md2 v n (a + k - v) FA HM2 Hv ltac:(lia2)) as (NIa & _).
      apply NIa. replace (v + (a + k - v)) with (a + k) by lia2. exact HI. }
  assert (TC3 : forall a cs, rw_cells (ms_segs B) m3 a cs ->
      (forall k, 0 <= k < Z.of_nat (cells_size cs) -> in_globals G_reply (a + k) /\ ~ (HA + 64 <= a + k < HA + 96)) ->
      rw_cells (ms_segs B) mem4 a cs).
  { intros a cs H D. apply (rmid_rw_img B (API rc) AX _ _ _ _ L2 A2 m3 md2 L3 A3 mem4 md4 a cs (hg_img_low B SEG) HKc HM3
      Rcw H).
    intros k Hk1. destruct (D k Hk1) as (HG & N1). pose proof (proj1 (PL _ HG)) as HI. pose proof (in_img_low B SEG _ HI) as LOW.
    split; [exact (PL _ HG)|]. intros [X|[X|(v & n & Hv & _ & Hva)]]; [exact (N1 X)|lia2|].
    destruct (p2_blk rc fx B (API rc) L2 A2 m3 md2 v n (a + k - v) FA HM3 Hv ltac:(lia2)) as (NIa & _).
    apply NIa. replace (v + (a + k - v)) with (a + k) by lia2. exact HI. }
  assert (LEN' : length (pre' ++ e3 :: post') = length es).
  { destruct (p2_sbs_maps _ _ SBpost) as (_ & _ & _ & Lb). rewrite ESP. rewrite !length_app. cbn [length].
    rewrite (p2_len_firstn es i IL). clear - Lb LPRE0. lia. }
  assert (GL4 : globals_at B mem4 cl (if send_off cl br TOT then br else dd) gn dd (if send_off cl br TOT then ei else 0)
      (Z.of_nat (length (pre' ++ e3 :: post'))) G nfd mx (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
      (if live then Z_to_bv 64 CAP2 else cap) (if live then Z_to_bv 64 OUT2 else out)).
  { rewrite LEN'. unfold globals_at.
    split.
    { apply TG; [exact G1|]. intros k Hk1. cbn in Hk1. split; [apply g9_in_listen; unfold CF.relay_finish_b_c.G_LISTEN; lia2|].
      unfold CF.relay_finish_b_c.G_LISTEN, send_line_c.G_BROKEN, send_line_c.G_EINTR, send_line_c.G_OUTV, HA, HarnessRep.G_S,
        SRC_SIZE. repeat split; lia2. }
    split; [apply TG; [exact G2|]; p2g HA|].
    split; [apply TG; [exact G3|]; p2g HA|].
    split.
    { apply TC3; [apply TM3; [exact GBR2|cbn; unfold send_line_c.G_BROKEN; lia2]|].
      intros k Hk1. cbn in Hk1. split; [apply in_G_bss; unfold send_line_c.G_BROKEN; lia2|].
      unfold send_line_c.G_BROKEN, HA, HarnessRep.G_S, SRC_SIZE. lia2. }
    split; [apply TG; [exact G5|]; p2g HA|].
    split; [apply TG; [exact G6|]; p2g HA|].
    split.
    { apply TC3; [apply TM3; [exact GEI2|cbn; unfold send_line_c.G_EINTR; lia2]|].
      intros k Hk1. cbn in Hk1. split; [apply in_G_bss; unfold send_line_c.G_EINTR; lia2|].
      unfold send_line_c.G_EINTR, HA, HarnessRep.G_S, SRC_SIZE. lia2. }
    split; [apply TG; [exact G8|]; p2g HA|].
    split; [apply TG; [exact G9|]; p2g HA|].
    split; [apply TG; [exact G10|]; p2g HA|].
    split.
    { apply TC3; [exact GOV3|]. intros k Hk1. cbn in Hk1. split; [apply in_G_bss; unfold send_line_c.G_OUTV; lia2|].
      unfold send_line_c.G_OUTV, HA, HarnessRep.G_S, SRC_SIZE. lia2. }
    split.
    { rewrite <- SEG in CK3. apply TC3; [exact CK3|]. intros k Hk1. cbn in Hk1. unfold relay_event_c.G_LOCK.
      split; [apply in_G_bss; clear - Hk1; lia|]. unfold HA, HarnessRep.G_S, SRC_SIZE. clear - Hk1. lia. }
    split; [apply TG; [exact G13|]; p2g HA|].
    split; [destruct (entry_errno_cells B SEG ETP EOFF mem4) as [ev EV]; exists ev; rewrite SEG; exact EV|].
    split; [exact HCL|]. split; [destruct (send_off cl br TOT); [exact HBR|exact HDD]|]. split; [exact HGN|].
    split; [exact HDD|]. split; [destruct (send_off cl br TOT); [exact HEI|left; reflexivity]|].
    split; [|exact HMX].
    destruct (send_off cl br TOT) eqn:SO; [exact HGG|]. destruct HGG as [HG0 HG1].
    split; [intros X; destruct (HG0 X) as (Y1 & Y2 & Y3); split; [exact Y1|]; split; [exact Y3|exact Y3]|].
    intros X. destruct (HG1 X) as [Y|[Y|Y]]; [left; exact Y| |right; right; exact Y].
    exfalso. unfold send_off in SO. apply orb_false_iff in SO. destruct SO as [SO _]. apply orb_false_iff in SO.
    destruct SO as [_ SO]. rewrite Y in SO. discriminate. }
  assert (OUT4 : output_at (rc := rc) B L3 A3 mem4 (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
      (if live then Z_to_bv 64 CAP2 else cap) (if live then Z_to_bv 64 OUT2 else out)).
  { destruct live eqn:LV.
    - pose proof (LV1 eq_refl) as (TL1 & CAPF & INO & FRO & BYO & JL & _).
      assert (TOTP : 0 < TOT).
      { pose proof (dc_live gn cl br dd TOT HGN (proj1 HGG) (proj2 HGG)) as DL. rewrite <- LVD in DL.
        assert (TN : 0 <= TOT) by (unfold TOT; lia2).
        destruct (Z.eqb_spec TOT 0) as [X|X]; [rewrite andb_false_r in DL; discriminate|lia2]. }
      pose proof (CF.RelayCap.drain_ocap_le_tot true (bv_unsigned mx) (bv_unsigned nout)
        (bv_unsigned cap) e1 h (p2_fin_no true (bv_unsigned mx) (bv_unsigned nout)
          (bv_unsigned cap) rc B L A m1 e1 h HA EOK1 SRC1 ltac:(rewrite SS1; exact SKO) ltac:(rewrite SS1, SUU1; exact WU)))
        as OCB.
      rewrite <- CAPF in OCB. change (Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h)))))) with TOT in OCB.
      assert (CB2 : CAP2 <= TBBYTES).
      { clear - OCB CAPB HNO TOT26'. unfold TBBYTES in *. rewrite HNO in OCB. lia. }
      pose proof FRO as (FR1 & FR2 & FR3).
      assert (NOE : bv_unsigned (Z_to_bv 64 (bv_unsigned nout + TOT)) = TOT).
      { rewrite HNO. apply unsigned_lit. clear - TOT26' TOTP. lia. }
      assert (CAE : bv_unsigned (Z_to_bv 64 CAP2) = CAP2) by (apply unsigned_lit; clear - CB2 TL1 TOTP HNO; unfold TBBYTES in *; lia).
      assert (OUE : bv_unsigned (Z_to_bv 64 OUT2) = OUT2) by (apply unsigned_lit; clear - FR1 FR2 ACL TL1 TOTP HNO; lia).
      assert (NFO : ~ (False \/ In OUT2 (hs_blocks h2))) by (intros [[]|X]; apply NOL; apply in_or_app; right; exact X).
      unfold output_at. cbv zeta. rewrite NOE, CAE, OUE. split; [|exact CB2]. exists LB, junk2. right.
      rewrite O0 in BYO. cbn [app] in BYO. pose proof (with_nul_bzs Ls LB LBE) as LBL.
      split; [clear - TL1 TOTP HNO; lia|]. split; [clear - TL1 HNO; lia|].
      split.
      { exact (proj1 (rmid_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 OUT2 CAP2 0 Rum INO
          ltac:(clear - TL1 TOTP HNO; lia) NFO ltac:(clear - TL1 TOTP HNO; lia)
          (KN2 OUT2 CAP2 (OUT2 + 0) INO (fun X => NOL (in_or_app _ _ _ (or_intror X))) ltac:(clear - TL1 TOTP HNO; lia)))). }
      split; [exact FRO|].
      split.
      { apply (rmid_bytes_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 OUT2 CAP2 OUT2 _ Rum INO
          ltac:(clear - TL1 TOTP HNO; lia) NFO BYO); [apply Z.le_refl|rewrite length_app; clear - LBL JL TOTP HNO; unfold TOT in *; lia|].
        intros k Hk1. rewrite length_app in Hk1.
        exact (KN2 OUT2 CAP2 (OUT2 + k) INO (fun X => NOL (in_or_app _ _ _ (or_intror X)))
          ltac:(clear - Hk1 LBL JL TOTP HNO; unfold TOT in *; lia)). }
      split; [exact LBL|]. clear - JL HNO. lia.
    - destruct (LV0 eq_refl) as (_ & LV02 & LV03).
      unfold output_at. cbv zeta. split; [|exact CAPB]. exists O, junk.
      destruct OC as [OCl|(C0 & C1' & C2' & C3' & C4' & C5' & C6')]; [left; exact OCl|right].
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
      exact (KN2 (bv_unsigned out) (bv_unsigned cap) (bv_unsigned out + k) IN2 NOH ltac:(clear - Hk1 C5' C6'; lia)). }
  pose proof SRC4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOV4 & _ & _ & _ & _ & _ & _ & LH4 & NDB4).
  assert (NH3M : forall x m, In (x, m) (blocks L2 A2) -> 0 < m -> ~ In x (hs_blocks h2) -> ~ In x (hs_blocks h3)).
  { intros x m Hx Hm NX HX. destruct (HB3 x HX) as [Y|Y]; [exact (NX Y)|]. apply (NEW3 x m Hx Hm); [|exact Y].
    intros HR. apply NX. apply in_app_or in HR. destruct HR as [HR|HR]; [apply p2_hb_exp, p2_lb_recs; exact HR|].
    apply p2_hb_held. exact HR. }
  assert (NDM : NoDup (G :: bv_unsigned (if live then Z_to_bv 64 OUT2 else out) :: entry_blocks e3 ++ hs_blocks h3)).
  { rewrite DN2, ENB3. apply NoDup_ListNoDup. apply NoDup_ListNoDup in NDB4.
    assert (DEH3 : forall q, In q (entry_blocks e2) -> ~ In q (hs_blocks h3)).
    { intros q Hq. destruct (p2_eb_pos rc B L2 A2 mem2 e2 EOK2 q Hq) as (m' & Hm' & Hq').
      exact (NH3M q m' Hq' Hm' (DEH q Hq)). }
    assert (NOH3 : ~ In OUT2 (hs_blocks h3)).
    { intros HX. destruct (p2_hb_pos rc B L3 A3 mem4 HA h3 SRC4 OUT2 HX) as (m' & Hm' & Hq').
      destruct live eqn:LV.
      - pose proof (LV1 eq_refl) as (TL1 & _ & INO & _). apply (NH3M OUT2 CAP2 INO); [|intros X; apply NOL; apply in_or_app; right; exact X|exact HX].
        assert (TOTP : 0 < TOT).
        { pose proof (dc_live gn cl br dd TOT HGN (proj1 HGG) (proj2 HGG)) as DL. rewrite <- LVD in DL.
          assert (TN : 0 <= TOT) by (unfold TOT; lia2).
          destruct (Z.eqb_spec TOT 0) as [X|X]; [rewrite andb_false_r in DL; discriminate|lia2]. }
        clear - TL1 TOTP HNO. lia.
      - destruct (LV0 eq_refl) as (_ & LV02 & LV03).
        destruct OC as [(C0 & O0' & _)|(C0 & _)].
        + destruct (p2_blk rc fx B (API rc) L3 A3 mem4 md4 OUT2 m' 0 FA HM4 Hq' ltac:(clear - Hm'; lia)) as (_ & B0 & _).
          rewrite LV03, O0' in B0. clear - B0. lia.
        + destruct (LV02 C0) as (IN2 & _). rewrite LV03 in HX. apply (NH3M _ _ IN2 C0); [|exact HX].
          intros X. apply NOL. rewrite LV03. apply in_or_app. right. exact X. }
    constructor.
    - intros [EQ|X]; [exact (NG2 (eq_sym EQ))|]. apply in_app_or in X. destruct X as [X|X]; [exact (NGL (in_or_app _ _ _ (or_introl X)))|].
      exact (NH3M G 896 GIN2 ltac:(reflexivity) (fun Y => NGL (in_or_app _ _ _ (or_intror Y))) X).
    - constructor.
      + intros X. apply in_app_or in X. destruct X as [X|X]; [exact (NOL (in_or_app _ _ _ (or_introl X)))|exact (NOH3 X)].
      + apply (NoDup_count_occ Z.eq_dec). intros x. rewrite count_occ_app.
        pose proof (proj1 (NoDup_count_occ Z.eq_dec _) (proj1 (NoDup_ListNoDup _) NDE2) x) as C1.
        pose proof (proj1 (NoDup_count_occ Z.eq_dec _) NDB4 x) as C2.
        destruct (in_dec Z.eq_dec x (entry_blocks e2)) as [Y|Y].
        * pose proof (DEH3 x Y) as Y2. rewrite (count_occ_not_In Z.eq_dec) in Y2. lia.
        * rewrite (count_occ_not_In Z.eq_dec) in Y. lia. }
  destruct (p2_sbs_maps _ _ SBpre) as (M1pre & M2pre & M3pre & _).
  destruct (p2_sbs_maps _ _ SBpost) as (M1post & M2post & M3post & _).
  assert (FE4 : Forall (CF.RelayRep.entry_ok (rc := rc) B L3 A3 mem4) (pre' ++ e3 :: post')).
  { apply Forall_app. split; [exact EOpre|constructor; [exact EOK3|exact EOpost]]. }
  destruct (p2_nd_split _ _ _ _ NDA) as (GO & GNL & _ & _ & _ & _).
  assert (GNT : ~ In G TF0).
  { intros [EQ|X]; [exact (GO (eq_sym EQ))|]. apply GNL. apply in_app_or in X. destruct X as [X|X]; apply in_or_app.
    - left. apply in_concat. exists (entry_blocks e). split; [apply in_map; exact (nth_error_In es i Hi)|exact X].
    - right. apply in_concat. exists (hs_blocks h). split; [|exact X].
      exact (in_map (fun p => hs_blocks (fst p)) hj (h, jj) (nth_error_In hj i Hh)). }
  assert (NGH2 : ~ In G (hs_blocks h2)) by (intros X; apply NGL; apply in_or_app; right; exact X).
  assert (KGE : forall a, G <= a < G + 896 -> ~ (SA <= a < SA + SRC_ENTRY) ->
      ~ (((Es0 a \/ Ed a) \/ 0x3101c <= a < 0x31020) \/ Ec a)).
  { intros a Ha NSA. destruct (p2_blk rc fx B (API rc) L A mem md G 896 (a - G) FA HMR GIN ltac:(clear - Ha; lia))
      as (NIa & B0 & B1). replace (G + (a - G)) with a in NIa by (clear - IL; lia).
    intros [[[X|X]|X]|X].
    - destruct X as [X|X]; [clear - X B1 SPB1 Ha; lia|apply NIa; exact (proj1 (PL _ (in_G_bss a ltac:(clear - X; lia))))].
    - destruct X as [X|[X|[X|[X|[X|(v & n & Hv & Hvt & Hva)]]]]];
        try (apply NIa; apply (proj1 (PL a ltac:(apply in_G_bss; unfold G_BROKEN, G_EINTR, G_OUTV, HA, G_S, SRC_SIZE in X;
          clear - X JJ4; lia)))).
      + exact (NSA X).
      + assert (NE : G <> v) by (intros <-; exact (GNT Hvt)).
        destruct (blocks_disjoint B (API rc) L A mem md G 896 v n HMR GIN Hv NE) as [DJ|DJ]; clear - Ha Hva DJ; lia.
    - apply NIa. exact (proj1 (PL _ (in_G_bss a ltac:(clear - X; lia)))).
    - exact (KN2 G 896 a GIN2 NGH2 Ha (or_intror X)). }
  assert (NFG : ~ (((False \/ In G TF0) \/ False) \/ In G (hs_blocks h2))).
  { intros [[[[]|X]|[]]|X]; [exact (GNT X)|exact (NGH2 X)]. }
  assert (TAB4 : rw_cells (ms_segs B) mem4 G [CB 896 (concat (map entry_bytes (pre' ++ e3 :: post')) ++ tail)]).
  { destruct (hg_cut _ _ _ [_] [_; _] TS) as [TC1 TS2']. destruct (hg_cut _ _ _ [_] [_] TS2') as [_ TC3'].
    cbn [cells_size csize] in TS2', TC3'.
    assert (TC1m := rmid_rw_block B (API rc) BW _ _ _ _ L A mem md L3 A3 mem4 md4 G 896 G _ Rt GIN ltac:(reflexivity) NFG TC1
      ltac:(clear - IL; lia) ltac:(cbn [cells_size csize]; unfold SA in *; clear - IL Hes; lia)
      (fun k Hk1 => KGE (G + k) ltac:(cbn [cells_size csize] in Hk1; clear - Hk1 IL Hes; lia)
                     ltac:(cbn [cells_size csize] in Hk1; unfold SA, SRC_ENTRY; clear - Hk1; lia))).
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
        + rewrite A3E. unfold SA, SRC_ENTRY. clear - Hk1. lia. }
    assert (TM2 : rw_cells (ms_segs B) mem4 (G + Z.of_nat (56 * i + 0)) [CB 56 (entry_bytes e2)]).
    { replace (G + Z.of_nat (56 * i + 0)) with SA by (unfold SA; clear - IL; lia).
      replace (bv_unsigned (PropExec.getr R 10)) with SA in SA2 by (symmetry; exact HSA).
      apply (rmid_rw_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 G 896 SA _ Rum GIN2 ltac:(reflexivity)
        (fun X => match X with or_introl F => F | or_intror Y => NGH2 Y end) SA2);
        [unfold SA; clear - IL; lia|cbn [cells_size csize]; unfold SA; clear - IL Hes; lia|].
      intros k Hk1. cbn [cells_size csize] in Hk1.
      exact (KN2 G 896 (SA + k) GIN2 NGH2 ltac:(unfold SA; clear - Hk1 IL Hes; lia)). }
    pose proof (hg_join _ _ _ _ _ _ TM2 TC3m ltac:(cbn [cells_size csize]; rewrite A3E; clear; lia)) as J23.
    pose proof (hg_join _ _ _ _ _ _ TC1m J23 ltac:(cbn [cells_size csize]; clear - IL; lia)) as J123.
    eapply rw_cells_retype; [exact J123| |].
    - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_app, (p2_eb_len rc B L3 A3 mem4 _ FE4), LEN'.
      clear - TL. lia.
    - cbn [app cells_bytes cbytes]. rewrite map_app, concat_app. cbn [map concat].
      rewrite M2pre, M2post, (p2_sbs_bytes e2 e3 SB3), !app_nil_r, <- !app_assoc. reflexivity. }
  assert (GIN3 : In (G, SRC_TABLE) (blocks L3 A3)).
  { exact (proj1 (rmid_block B (API rc) BW _ _ _ _ L2 A2 mem2 md2 L3 A3 mem4 md4 G SRC_TABLE 0 Rum GIN2
      ltac:(reflexivity) (fun X => match X with or_introl F => F | or_intror Y => NGH2 Y end) ltac:(unfold SRC_TABLE, SRC_ENTRY; clear - IL; lia)
      (KN2 G SRC_TABLE (G + 0) GIN2 NGH2 ltac:(unfold SRC_TABLE, SRC_ENTRY; clear - IL; lia)))). }
  assert (MFD : map re_fd (pre' ++ e3 :: post') = map re_fd es).
  { transitivity (map re_fd (firstn i es ++ e :: skipn (S i) es)); [|rewrite <- ESP; reflexivity].
    rewrite !map_app. cbn [map]. rewrite M3pre, M3post, (proj1 SB3), FD2, SF1. reflexivity. }
  assert (MSND : map snd (firstn i hj ++ (h3, jj) :: skipn (S i) hj) = map snd hj).
  { transitivity (map snd (firstn i hj ++ (h, jj) :: skipn (S i) hj)); [|rewrite <- HJP; reflexivity].
    rewrite !map_app. reflexivity. }
  assert (PAI : pair_ok (rc := rc) B L3 A3 mem4 (t + 1) e3 (h3, jj)).
  { pose proof SB3 as (S31 & S32 & S33 & _ & _ & _ & _ & _ & _ & _ & S311 & S312 & _).
    unfold pair_ok. cbv zeta. cbn [fst snd]. split; [exact SRC4|]. split; [exact JJ4|].
    split; [unfold h3; cbn; rewrite S31, FD2, SF1, HFD2; exact FDH|].
    split; [intros _; unfold h3; cbn; rewrite S33, S312; split; [exact SKO2|exact WU2]|].
    split.
    { rewrite (p2_sbs_texts e2 e3 SB3). unfold h3; cbn [set_exp_held hs_held]. rewrite H3T, HHL2.
      rewrite (texts_lines (hs_expected h2) Ls ltac:(rewrite HEX2, EXP0; reflexivity) (dc_lines_range h)).
      rewrite (p2_sbs_texts e e1 SB1) in SSK2. exact (same_set_trans _ _ _ SSK2 (upds_same_set Ls _ _ SSK)). }
    split; [exact NDH3|]. split; [exact E3R|].
    unfold h3; cbn [set_exp_held hs_pending hs_expected hs_held].
    split; [unfold hl_n; rewrite HPR2; cbn; clear - Ht; lia|].
    split; [rewrite HPC2; clear - PC Ht; lia|].
    split; [unfold pending_stream; cbn [hs_pending set_exp_held]; rewrite HPR2; cbn; clear - Ht; unfold WRITE_MAX; lia|].
    split; [rewrite E3C, DC6; exact ECF|].
    rewrite HHL2 in HB22, H3C. clear - H3C HC HB22. lia. }
  assert (OPJ : slot_open hj jj = true).
  { unfold slot_open. apply existsb_exists. exists jj. split; [|apply Nat.eqb_refl].
    apply in_map_iff. exists (h, jj). split; [reflexivity|exact (nth_error_In hj i Hh)]. }
  assert (REL4 : relay_at (rc := rc) B L3 A3 mem4 (t + 1) nfd G (bv_unsigned (if live then Z_to_bv 64 OUT2 else out))
      (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj)).
  { unfold relay_at.
    split; [exists tail; split; [rewrite LEN'; exact TL|exact TAB4]|].
    split; [exact GIN3|]. split; [exact GFR|]. split; [exact FE4|].
    split; [rewrite MFD; exact NDF|].
    split.
    { assert (FDR' : Forall (fun z => FIRST_FD <= z < FIRST_FD + nfd) (map re_fd es)) by (apply Forall_map; exact FDR).
      rewrite <- MFD in FDR'. apply Forall_map in FDR'. exact FDR'. }
    split.
    { apply Forall2_app; [|constructor; [exact PAI|]].
      - eapply Forall2_impl; [|exact PApre']. intros e0 p0 H0. exact (pair_ok_t rc B L3 A3 mem4 t (t + 1) e0 p0 H0
          ltac:(clear - Ht; lia)).
      - eapply Forall2_impl; [|exact PApost']. intros e0 p0 H0. exact (pair_ok_t rc B L3 A3 mem4 t (t + 1) e0 p0 H0
          ltac:(clear - Ht; lia)). }
    split; [rewrite MSND; exact NDH|].
    split.
    { intros k Hk4 SO. assert (SO' : slot_open hj k = false) by (unfold slot_open in SO |- *; rewrite MSND in SO; exact SO).
      assert (KJ : k <> jj) by (intros ->; rewrite OPJ in SO'; discriminate).
      apply TG; [exact (ZH k Hk4 SO')|]. intros k' Hk'. cbn in Hk'.
      unfold send_line_c.G_BROKEN, send_line_c.G_EINTR, send_line_c.G_OUTV, HA, HarnessRep.G_S, SRC_SIZE.
      split; [apply in_G_bss; clear - Hk' Hk4; lia|repeat split; clear - Hk' Hk4 KJ; lia]. }
    apply (p2_nd_join G _ _ _ i e3 h3 jj NE3 NH3 NDM); [rewrite OTHEQ; exact (p2_oth_nd G (bv_unsigned out) es hj i e h jj NDA Hi Hh)|].
    intros x Hx. rewrite OTHEQ in Hx. destruct (OTX x Hx) as (NT & _). destruct (OTHP x Hx) as (m & Hm & Hxm).
    destruct (OLD x m Hxm Hm NT) as (Hx2 & NH2x & NE2x & NOx). intros [EQ|[EQ|X]].
    - apply NT. rewrite <- EQ. right; left; reflexivity.
    - rewrite DN2 in EQ. exact (NOx (eq_sym EQ)).
    - apply in_app_or in X. destruct X as [X|X]; [rewrite ENB3 in X; exact (NE2x X)|exact (NH3M x m Hx2 Hm NH2x X)]. }
  assert (COST4 : slot_cost (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj) <= K).
  { rewrite (p2_cost_app pre' (firstn i hj) e3 (h3, jj) post' (skipn (S i) hj)
      ltac:(rewrite LPRE0, (p2_len_firstn hj i IHJ); reflexivity)).
    rewrite (p2_cost_sbs _ _ _ SBpre), (p2_cost_sbs _ _ _ SBpost), (p2_sbs_cost e2 e3 (h3, jj) SB3).
    pose proof (p2_cost_app (firstn i es) (firstn i hj) e (h, jj) (skipn (S i) es) (skipn (S i) hj)
      ltac:(rewrite (p2_len_firstn es i IL), (p2_len_firstn hj i IHJ); reflexivity)) as CO.
    rewrite <- ESP, <- HJP in CO.
    pose proof EOK2 as (_ & _ & _ & _ & _ & _ & EUL2 & _).
    rewrite (p2_sbs_texts e e1 SB1) in SSK2.
    pose proof (p2_pair_cost e e2 h h3 jj SKO WU HOV EUL SKO2 WU2 HOV4 EUL2 HST2 HPR2 NDK2 SSK2) as PCC.
    clear - CO PCC Hcost. lia. }
  assert (TR5 : tail_regs E t K R5).
  { unfold tail_regs, base_regs, fix_regs. repeat split.
    - geq X5.
    - p2_chain X5 PRc X3 3. exact (eq_trans (PRd 3 (p2_cs 3 eq_refl)) D3).
    - p2_chain X5 PRc X3 4. exact (eq_trans (PRd 4 (p2_cs 4 eq_refl)) D4).
    - p2_chain X5 PRc X3 20. exact (eq_trans (PRd 20 (p2_cs 20 eq_refl)) D20).
    - p2_chain X5 PRc X3 19. reflexivity.
    - p2_chain X5 PRc X3 21. exact (eq_trans (PRd 21 (p2_cs 21 eq_refl)) D21).
    - p2_chain X5 PRc X3 24. exact (eq_trans (PRd 24 (p2_cs 24 eq_refl)) D24).
    - p2_chain X5 PRc X3 25. exact (eq_trans (PRd 25 (p2_cs 25 eq_refl)) D25).
    - p2_chain X5 PRc X3 26. exact (eq_trans (PRd 26 (p2_cs 26 eq_refl)) D26).
    - p2_chain X5 PRc X3 27. exact (eq_trans (PRd 27 (p2_cs 27 eq_refl)) D27).
    - p2_chain X5 PRc X3 8. exact (eq_trans (PRd 8 (p2_cs 8 eq_refl)) D8).
    - p2_chain X5 PRc X3 23. exact (eq_trans (PRd 23 (p2_cs 23 eq_refl)) D23).
    - p2_chain X5 PRc X3 22. exact (eq_trans (PRd 22 (p2_cs 22 eq_refl)) D22). }
  exists fx', L3, A3, R5, mem4, md4, cl, (if send_off cl br TOT then br else dd), gn, dd,
    (if send_off cl br TOT then ei else 0), G, nfd, mx, (if live then Z_to_bv 64 (bv_unsigned nout + TOT) else nout),
    (if live then Z_to_bv 64 CAP2 else cap), (if live then Z_to_bv 64 OUT2 else out), (pre' ++ e3 :: post'),
    (firstn i hj ++ (h3, jj) :: skipn (S i) hj).
  split; [reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split; [exact TR5|]. split; [exact HM4|]. split; [exact HWF4|]. split; [exact HBD4|]. split; [exact INIT3|].
  split; [destruct MD4 as [v4 EV4]; destruct MD2 as [v2 EV2]; destruct HVM as [v0 EV0]; exists v4;
    rewrite EV4, EV2, EV0, !with_vmmaps_twice; reflexivity|].
  split; [exact RO4|]. split; [exact IK4|]. split; [exact ST4|]. split; [exact DK4|]. split; [exact GL4|].
  split; [change (0 <= nfd <= t + 2); clear - Hnfd; lia|]. split; [exact OUT4|]. split; [exact REL4|].
  split; [rewrite LEN'; exact Hes|]. split; [exact COST4|].
  assert (NB3 : List.NoDup (map fst (blocks L3 A3))).
  { pose proof (NDB L3 A3 mem4 md4 HM4) as XN3. first [exact XN3|exact (proj1 (NoDup_ListNoDup _) XN3)]. }
  pose proof (CF.SlotNcWt.ncs_le_wt (rc := rc) B (API rc) L3 A3 mem4 md4 (t + 1) nfd G _ _ _ _ _ HM4 OUT4 REL4
    ltac:(rewrite LEN'; exact Hes) NB3) as NCS3.
  rewrite DN2. rewrite DN2 in REL4, NCS3.
  pose proof REL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ND4).
  destruct (p2_ta_nd _ _ _ _ (proj1 (NoDup_ListNoDup _) ND4)) as (NV3 & _).
  pose proof (CF.SlotPass4.p4_src_blk_of B L3 A3 mem4 HA h3 SRC4) as P3S.
  pose proof P3S as (_ & _ & _ & P3H & _).
  assert (MV3 : nc_move (view_of G OUT2 es2 hj2) L2 A2
      (view_of G OUT2 (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj)) L3 A3
      (p2_arr_dels (hs_held h2) H3) (p2_arr_adds (hs_held h2) H3)).
  { apply (p2_cnl_mv L2 A2 L3 A3 G OUT2 es2 (pre' ++ e3 :: post') hj2 (firstn i hj ++ (h3, jj) :: skipn (S i) hj)
      (firstn i hj) (skipn (S i) hj) h2 h3 jj eq_refl eq_refl).
    + unfold es2. rewrite !map_app, !concat_app. cbn [map concat].
      rewrite (p2_sbs_cnc _ _ SBpre), (p2_sbs_cnc _ _ SBpost), (p2_sbs_enc _ _ SB3). reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold h3. cbn [set_exp_held hs_expected]. unfold arr_nc. rewrite E3V, E3C. reflexivity.
    + exact NB2.
    + exact NB3.
    + exact NV2.
    + exact NV3.
    + intros xq mq Hxq Hvq NAq. apply SURV3; [exact Hxq|]. intros HRq. apply in_app_or in HRq as [HRq|HRq].
      * apply (NR2 xq Hvq). apply (p2_rest_in es2 hj2 h2 jj xq (nth_error_In _ _ NH2i)). unfold p2_srecs.
        apply in_or_app; right; apply in_or_app; left; exact HRq.
      * unfold list_blocks in HRq. apply in_app_or in HRq as [HRq|HRq]; [exact (NAq HRq)|].
        apply (NR2 xq Hvq). apply (p2_rest_in es2 hj2 h2 jj xq (nth_error_In _ _ NH2i)). unfold p2_srecs.
        apply in_or_app; right; apply in_or_app; right; exact HRq.
    + exact (proj1 P2H).
    + exact (proj1 P3H).
    + intros xq mq Hqq. exact (p2_pos rc B (API rc) L2 A2 mem2 md2 xq mq HM2 Hqq).
    + intros xq mq Hqq. exact (p2_pos rc B (API rc) L3 A3 mem4 md4 xq mq HM4 Hqq). }
  assert (WT3 : nc_wt (pre' ++ e3 :: post') (firstn i hj ++ (h3, jj) :: skipn (S i) hj) <= cnl_wt es2 hj2 h2).
  { assert (SB2 : Forall2 p2_sbs es2 (pre' ++ e3 :: post')).
    { unfold es2. apply Forall2_app; [exact SBpre|constructor; [exact SB3|exact SBpost]]. }
    rewrite (p2_sbs_wt _ _ _ SB2). unfold hj2, h3.
    exact (cnl_wt_post es2 (firstn i hj) (skipn (S i) hj) h2 jj E3 H3 E3R E3C H3C H3T). }
  pose proof Rum as (_ & _ & _ & LYu & _).
  apply (RPOST2 L3 A3 qs3 LQ3 RF3 E3 H3 SHR3 SHL3 E3R E3V E3C NDH3 H3T BL3 NEW3).
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
  - rewrite LEN'. exact Hes.
  - rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. clear - Hes IHJ LHJ. lia.
  - exact MV3.
  - exact NB3.
  - exact (p2_nc_keep _ _ _ _ _ _ _ _ HWF2 LYu MV3).
  - exact NCS3.
  - exact WT3.
Qed.

Theorem pass2_holds : forall (F : ResFormT),
  check_bounded_contract -> pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty -> @drain_contract fx rc B (API rc) F) ->
  check_no_loss_read_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @check_no_loss_contract fx rc B (API rc) F) ->
  check_shape_done_contract ->
  forall RI, RI_mono RI -> p2_drain_res_s F RI -> p2_cnl_res_s F RI -> pass_ok RI 2.
Proof.
  intros F CB LCK ULK HD CNR HC CSD RI RIM DRES CRES B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop.
  cbv beta in Hop.
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 2) with 0x13d90 in HM.
  pose proof (walk_pick E t k 2 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
    (or_introl eq_refl)) as HW2.
  eapply SR_bind; [exact (MI_op2_scan B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 2 k) s c' HF CB LCK HW2 HM)|].
  intros c2 [HL2|HD2]; [apply SR_ret; exists (disp_k E 2 k); exact HL2|].
  exact (p2_drain_path F B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 2 k) c2 HF CB ULK
    (fun fx' => HD B API LS SH SK ra empty rc fx' (proj1 HF)) CNR
    (fun fx' => HC B API LS SH SK ra empty rc fx' (proj1 HF)) CSD DRES CRES HW2 HD2).
Qed.
