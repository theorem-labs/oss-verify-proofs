(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 684 of its 782 lines of code are new or changed and 919 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/arg_s.v, with its module paths, module names and numbers changed; 258 of its 325 lines of code are new or changed and 715 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_struct.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma land7_zero : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Ltac ub_align H := try change (bv_wrap 64 7) with 7; rewrite (land7_zero _ H).

Lemma close_closed :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (sw olen vtag vid : word)
         (pad : list byte),
    rw_cells rsegs m (bv_unsigned a0) (ps_cells (wz 0) sw olen vtag vid pad) ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists a0' m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                       F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sw olen vtag vid pad HPS NZ A8 ST LO HSP.
  unfold ps_cells, wz in HPS.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  do 4 step.
  if_false.
  do 3 step.
  ub_align A8.
  if_false.
  do 2 step.
  if_true.
  do 4 step.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; eassumption.
Qed.

Lemma close_pro :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (f sw olen vtag vid : word)
         (pad : list byte),
    rw_cells rsegs m (bv_unsigned a0) (ps_cells f sw olen vtag vid pad) -> bv_unsigned f <> 0 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists sp' m1, ms' = MS (mkR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_close + 0x28)%Z)) sp' gp tp t0 t1 t2 a0 s1 f a1 a2 a3 a4 a5 a6 a7
                                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                       F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_fclose)) fc None m1 (seg_rom rsegs) /\
         bv_unsigned sp' = bv_unsigned sp - 16 /\
         rw_cells rsegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra] /\
         rw_cells rsegs m1 (bv_unsigned a0) (ps_cells f sw olen vtag vid pad) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp - 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo f sw olen vtag vid pad HPS NZ NZ0 A8 ST LO HSP.
  unfold ps_cells in HPS.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  do 4 step.
  if_false.
  do 3 step.
  ub_align A8.
  if_false.
  do 2 step.
  if_false.
  step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [apply unsigned_lit; lia|].
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.

Lemma close_epi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 ra0 s0o : word)
         (f sw olen vtag vid : word) (pad : list byte),
    bv_unsigned sp = bv_unsigned sp0 - 16 -> bv_unsigned sp0 <= bv_unsigned s0 ->
    rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s0o; C8 ra0] ->
    rw_cells rsegs m (bv_unsigned s0) (ps_cells f sw olen vtag vid pad) ->
    evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0o s1 a0 a1 a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
         rw_cells rsegs m' (bv_unsigned s0) (ps_cells (wz 0) sw olen vtag vid pad) /\
         munch [(bv_unsigned s0, bv_unsigned s0 + 8)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_close + 0x28)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s0o f sw olen vtag vid pad Hsp HS0 HFR HPS.
  unfold ps_cells in HPS.
  pose proof (zr_word sp0) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (munch_refl [(bv_unsigned s0, bv_unsigned s0 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  rewrite <- Hsp in HFR.
  do 5 step.
  apply evt_done.
  assert (ESP : Z_to_bv 64 (bv_unsigned sp + 16) = sp0).
  { rewrite Hsp. replace (bv_unsigned sp0 - 16 + 16) with (bv_unsigned sp0) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite ESP. eexists. split; [reflexivity|].
  unfold ps_cells, wz. split; [eassumption|]. split; eassumption.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import KindB pcap_lib fclose_c pcap_source_close_c.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis HFC : fclose_contract B API.

Theorem pcap_source_close_holds : pcap_source_close_contract B API.
Proof.
  unfold pcap_source_close_contract.
  intros L A regs mem md ps h sw olen vtag vid pad b p Fc b0 HSEG PRE A0 PSN PS8 PSS HPS HR HOPEN HGU RO RES.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  assert (IL : img_low B).
  { eapply img_low_of_check with (C := (symaddr ImgPages.Ubsan.top)); [unfold img_check; rewrite HSEG; vm_compute; reflexivity | lia]. }
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold CLOSE_K in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof HPS as (_ & HP0 & HP24 & _). unfold ps_cells in HP24. cbn in HP24.
  assert (U10 : bv_unsigned (reg_get regs 10) = ps) by (change (reg_get regs 10) with (getr regs 10); rewrite A0; apply unsigned_lit; lia).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8256) (bv_unsigned sp)).
  { pose proof (kb_stk B API IL 8256 L A regs mem md PRE0 ltac:(lia)) as X. rewrite HSEG in X. exact X. }
  assert (OUTW : forall x, ~ (bv_unsigned sp - 16 <= x < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 16, bv_unsigned sp)] x) by (intros x Hx; cbn; split; [exact Hx | exact I]).
  rewrite HSEG in RO, HWS, HERR.
  rewrite HSEG.
  destruct (Z.eq_dec h 0) as [H0|HN0].
  - subst h.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold PCAP_SOURCE_CLOSE.
      eapply close_closed with (lo := bv_unsigned sp - 8256);
        [rewrite U10; exact HPS | rewrite U10; exact PSN | rewrite U10; exact PS8 | exact ST | lia | rewrite U10; exact PSS]. }
    intros ms1 (can1 & (a0' & m1 & -> & MU1 & WM1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    apply SR_ret.
    exists L, A, R1, m1, md.
    split; [reflexivity|].
    assert (MID : kb_mid B API 8256 (bv_unsigned sp) L A mem md (fun _ => False) L A m1 md).
    { eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]);
        [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite HSEG; exact WM1 | | ].
      - intros a [Ha|Ha]; rewrite HSEG; [apply HWS; lia | apply HERR; exact Ha].
      - intros x _ Hs _. apply OUTW. lia.
      - intros x Hx _. apply OUTW. lia. }
    pose proof (keep_munch _ _ _ 0 (bv_unsigned sp - 16) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
      as KLO.
    pose proof (keep_munch _ _ _ (bv_unsigned sp) (2 ^ 64) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
      as KHI.
    split.
    { apply (kb_post B API).
      - eapply (kb_mid_E B API); [exact MID | intros a F; destruct F].
      - eapply pres_mkR. exact X1. }
    split; [apply (kp_rw_cells mem m1 (bv_unsigned sp) (2 ^ 64) KHI ps _ HPS PSS); unfold ps_cells; cbn; lia|].
    split; [apply (kp_guard_ok mem m1 0 (bv_unsigned sp - 16) KLO HGU); unfold A_GOT_GUARD, A_GUARD; lia|].
    split; [exact (ro_agree_munch _ _ _ RO MU1 (fun x Hx => OUTW x ltac:(lia)))|].
    split.
    { intros _. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU1 | exact RES]. }
    intros C. exfalso. apply C. reflexivity.
  - destruct (HOPEN HN0) as (INH & INB & HST & HOFL & HSO).
    destruct (block_facts B _ LAWS L A mem md h 1304 0 HMR INH ltac:(lia)) as (_ & Hh4k & HhC & _).
    destruct (pl_in_blocks_user L A b _ INB) as (pb & Hpb & Eb).
    pose proof (mr_blocks_range B _ LAWS L A mem md pb _ HMR Hpb) as (Hb4k & HbC). rewrite Eb in Hb4k, HbC.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold PCAP_SOURCE_CLOSE.
      eapply close_pro with (lo := bv_unsigned sp - 8256);
        [ rewrite U10; exact HPS | unfold wz; rewrite unsigned_lit by lia; exact HN0 | rewrite U10; exact PSN
        | rewrite U10; exact PS8 | exact ST | lia | rewrite U10; exact PSS ]. }
    intros ms1 (can1 & (sp1 & m1 & -> & SP1 & FR1 & PS1 & MU1 & WM1 & ST1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    rewrite U10 in PS1.
    assert (E1_1 : getr R1 1 = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_close + 0x28)%Z)) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); reflexivity).
    assert (E1_2 : getr R1 2 = sp1) by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); reflexivity).
    assert (E1_8 : getr R1 8 = reg_get regs 10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); reflexivity).
    assert (E1_10 : getr R1 10 = wz h) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); reflexivity).
    assert (SPZ1 : spZ R1 = bv_unsigned sp - 16) by (unfold spZ; rewrite E1_2; exact SP1).
    pose proof (keep_munch _ _ _ 0 (bv_unsigned sp - 16) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
      as KLO.
    assert (MID1 : kb_mid B API 8256 (bv_unsigned sp) L A mem md (fun _ => False) L A m1 md).
    { eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]);
        [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite HSEG; exact WM1 | | ].
      - intros a [Ha|Ha]; rewrite HSEG; [apply HWS; lia | apply HERR; exact Ha].
      - intros x _ Hs _. apply OUTW. lia.
      - intros x Hx _. apply OUTW. lia. }
    assert (CP : call_pre_k B (aa_MR API) 8240 L A R1 m1 md).
    { eapply (kb_pre_A B API) with (K := 8256) (f := 16) (W := [(bv_unsigned sp - 16, bv_unsigned sp)]);
        [ exact PRE0 | lia | lia | lia | exact SPZ1 | | rewrite E1_4; reflexivity | | exact MU1
        | rewrite HSEG; exact WM1 | | ].
      - rewrite SPZ1. replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
      - intros x _ Hx. change (spZ regs) with (bv_unsigned sp) in Hx. apply OUTW. lia.
      - intros x Hx _. apply OUTW. lia. }
    pose proof HFC as FC. unfold fclose_contract in FC. rewrite HSEG in FC. unfold FCLOSE in FC.
    eapply SR_bind.
    { apply (FC L A R1 m1 md h b p Fc b0 eq_refl CP E1_10 INH INB).
      - apply (kp_mstl mem m1 0 (bv_unsigned sp - 16) KLO); [exact HST | lia | lia | lia | lia].
      - apply (kp_ofl_one mem m1 0 (bv_unsigned sp - 16) KLO); [exact HOFL | unfold A_OFL_HEAD; lia | unfold A_OFL_HEAD; lia].
      - apply (kp_stdio_ok mem m1 0 (bv_unsigned sp - 16) KLO); [exact HSO | unfold A_LIBC; lia | unfold A_OFL_LOCK; lia].
      - apply (kp_guard_ok mem m1 0 (bv_unsigned sp - 16) KLO); [exact HGU | unfold A_GOT_GUARD; lia | unfold A_GUARD; lia].
      - exact (ro_agree_munch _ _ _ RO MU1 (fun x Hx => OUTW x ltac:(lia))).
      - exact RES. }
    intros c2 RET.
    destruct RET as (L' & A' & R2 & m2 & md2 & -> & POST & A0' & BLK & KEPT & UBK & INIT & RLEN & RES' & OFE
      & SO2 & GU2 & RO2 & BF2).
    destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST) as [MIDc HPRES].
    pose proof POST as (HMR' & HWF' & HBD' & HLE & HSTAB & _ & HVM & HFRAME & HBLKS & HSCR).
    destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
    rewrite SPZ1 in MIDc. unfold FCLOSE_K in *.
    assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
    { intros a Ha. split; intros Ho;
        [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
    assert (KH2 : forall a, bv_unsigned sp - 16 <= a < 2 ^ 64 ->
       mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs m2 a)).
    { intros a Ha. destruct (NOWN a ltac:(lia)) as [N1 N2]. rewrite <- HSEG.
      destruct (HFRAME a ltac:(left; lia) N1 N2) as [E W].
      - unfold scratch_k. rewrite SPZ1. intros [H|H]; lia.
      - unfold fclose_writes, A_OFL_HEAD. intros [H|H]; lia.
      - split; [exact E | intros Hw; apply W; exact Hw]. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)])
      by (apply (kp_rw_cells m1 m2 (bv_unsigned sp - 16) (2 ^ 64) KH2 _ _ FR1); cbn; lia).
    assert (PS2 : rw_cells rsegs m2 ps (ps_cells (wz h) sw olen vtag vid pad))
      by (apply (kp_rw_cells m1 m2 (bv_unsigned sp - 16) (2 ^ 64) KH2 _ _ PS1); unfold ps_cells; cbn; lia).
    assert (G2 : reg_get R2 2 = sp1) by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (G8 : reg_get R2 8 = reg_get regs 10) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
    rewrite E1_1.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply close_epi with (sp0 := sp) (ra0 := reg_get regs 1) (s0o := reg_get regs 8);
        [ rewrite G2; exact SP1 | rewrite G8, U10; lia | exact FR2 | rewrite G8, U10; exact PS2 ]. }
    intros ms3 (can3 & (m3 & -> & PS3 & MU3 & WM3) & EQ3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    rewrite G8, U10 in PS3, MU3.
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    apply SR_ret.
    exists L', A', R3, m3, md2.
    split; [reflexivity|].
    assert (OUT3 : forall x, x < ps -> outside [(ps, ps + 8)] x) by (intros x Hx; cbn; split; [lia | exact I]).
    pose proof (keep_munch _ _ _ 0 ps MU3 ltac:(lia) ltac:(lia) (fun x Hx => OUT3 x ltac:(lia))) as KL3.
    assert (MID2 : kb_mid B API 8256 (bv_unsigned sp) L A mem md (fun a => False \/ fclose_writes h a) L' A' m2 md2).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDc | lia | lia | lia | lia |].
      intros a Ha1 Ha2 HW. unfold fclose_writes, A_OFL_HEAD in HW. lia. }
    assert (MID3 : kb_mid B API 8256 (bv_unsigned sp) L A mem md
                     (fun a => (False \/ fclose_writes h a) \/ (ps <= a < ps + 8)) L' A' m3 md2).
    { eapply (kb_mid_tail B API IL) with (W := [(ps, ps + 8)]);
        [ exact MID2 | exact MU3 | rewrite HSEG; exact WM3 | | | | ].
      - intros x Hx. destruct (kb_outside_dec [(ps, ps + 8)] (bv_unsigned x)) as [Ho|Ho];
          [rewrite (MU3 x Ho); exact Hx|].
        assert (Hin : ps <= bv_unsigned x < ps + 8) by (cbn in Ho; lia).
        pose proof PS3 as (_ & _ & _ & HW3).
        pose proof (HW3 (bv_unsigned x - ps) ltac:(unfold ps_cells; cbn; lia)) as Wx.
        replace (ps + (bv_unsigned x - ps)) with (bv_unsigned x) in Wx by lia.
        destruct (writable_hi_present m3 (bv_unsigned x) ltac:(pose proof (bv_unsigned_in_range 64 x) as R;
                    unfold bv_modulus in R; lia) Wx) as [bb Ebb].
        rewrite Z_to_bv_bv_unsigned in Ebb. rewrite Ebb. discriminate.
      - intros x Hx Hs He. apply outside_one. lia.
      - intros x Hx _. apply outside_one. lia.
      - intros q n i Hin Hin' Hi.
        destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
        apply outside_one. lia. }
    assert (PRES : regs_preserved regs R3).
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8)) regs R1 R2 R3 _ _ X1 HPRES X3).
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
        subst r. discriminate O. }
    split.
    { apply (kb_post B API); [|exact PRES].
      eapply (kb_mid_E B API); [exact MID3|].
      intros a [[F|HW]|HW]; [destruct F | split; [exact HN0 | left; exact HW] | split; [exact HN0 | right; exact HW]]. }
    split; [exact PS3|].
    split; [apply (kp_guard_ok m2 m3 0 ps KL3); [exact GU2 | unfold A_GOT_GUARD; lia | unfold A_GUARD; lia]|].
    split; [exact (ro_agree_munch _ _ _ RO2 MU3 (fun x Hx => OUT3 x ltac:(lia)))|].
    split; [intros C; exfalso; exact (HN0 C)|].
    intros _.
    split; [exact BLK|].
    split.
    { intros a k i Hin Hne Hi.
      destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
      rewrite (munch_mbyte (ms_segs B) _ _ _ _ MU3) by (try lia; apply OUT3; lia).
      rewrite (KEPT a k i Hin Hne Hi).
      apply (munch_mbyte (ms_segs B) _ _ _ _ MU1); [lia | apply OUTW; lia]. }
    split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN|]. split; [exact RES'|].
    split; [apply (kp_ofl_empty m2 m3 0 ps KL3); [exact OFE | unfold A_OFL_HEAD; lia | unfold A_OFL_HEAD; lia]|].
    split; [apply (kp_stdio_ok m2 m3 0 ps KL3); [exact SO2 | unfold A_LIBC; lia | unfold A_OFL_LOCK; lia]|].
    apply (kp_bytes_at m2 m3 0 ps KL3); [exact BF2 | lia | lia].
Qed.

End K.
