(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 101 of its 146 lines of code are new or changed and 1021 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel strcmp_c.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Contract KindBGlue SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import KindB pcap_lib fmemopen_c libreac_fuzz_fopen_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import libreac_fuzz_fopen fmemopen_cf_c libreac_fuzz_fopen_cf_c.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis HSC : strcmp_contract.
Hypothesis HFM : fmemopen_contract_cf B API.

Lemma fopen_evt_SRcf : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  ms_segs B = rsegs ->
  Exec.evt rsegs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof using.
  intros ms Q md P E. rewrite <- E. exact (evt_SRcf_canon B ms Q md P).
Qed.

Theorem libreac_fuzz_fopen_cf_holds : libreac_fuzz_fopen_contract_cf B API.
Proof.
  unfold libreac_fuzz_fopen_contract_cf.
  intros L A regs mem md pth b Fc b0 HSEG PRE A0 PN0 HPB HPD A1 HG HN26 HBLK HSO HOE HGU RO RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  assert (IL : img_low B).
  { eapply img_low_of_check with (C := (symaddr ImgPages.Plain.top)); [unfold img_check; rewrite HSEG; vm_compute; reflexivity | lia]. }
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold FOPEN_K in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof HPB as (HPB0 & HPB1 & _). cbn in HPB1.
  assert (U10 : bv_unsigned (reg_get regs 10) = pth)
    by (change (reg_get regs 10) with (getr regs 10); rewrite A0; apply unsigned_lit; lia).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8240) (bv_unsigned sp)).
  { pose proof (kb_stk B API IL 8240 L A regs mem md PRE0 ltac:(lia)) as X. rewrite HSEG in X. exact X. }
  assert (OUTW : forall x, ~ (bv_unsigned sp - 32 <= x < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 32, bv_unsigned sp)] x) by (intros x Hx; cbn; split; [exact Hx | exact I]).
  rewrite HSEG in RO, HWS, HERR.
  rewrite HSEG.
  eapply (fopen_evt_SRcf _ _ _ _ HSEG); [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold LIBREAC_FUZZ_FOPEN.
    eapply (fopen_run HSC) with (lo := bv_unsigned sp - 8240) (N := wz (Z.of_nat (length Fc))) (Bw := wz b);
      [ rewrite U10; exact HPB | rewrite U10; exact PN0 | rewrite U10; lia | exact (path_img _ RO) | exact HG
      | exact ST | lia | lia ]. }
  intros ms1 (can1 & (a1' & a2' & a3' & m1 & [[N0 ->] | [N0 ->]] & MU1 & WM1) & EQ1);
    unfold wz in N0; rewrite unsigned_lit in N0 by lia;
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1);
    pose proof (keep_munch _ _ _ 0 (bv_unsigned sp - 32) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
      as KLO;
    assert (MID1 : kb_mid B API 8240 (bv_unsigned sp) L A mem md (fun _ => False) L A m1 md) by
      (eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 32, bv_unsigned sp)]);
        [ exact HMR | exact HWF | exact HBD | intros a [Ha|Ha]; rewrite HSEG; [apply HWS; lia | apply HERR; exact Ha]
        | exact MU1 | rewrite HSEG; exact WM1 | intros x _ Hs _; apply OUTW; lia | intros x Hx _; apply OUTW; lia ]).
  - assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    apply SRcf_ret.
    exists L, A, R1, m1, md, 0.
    split; [reflexivity|].
    split.
    { apply (kb_post B API).
      - eapply (kb_mid_E B API); [exact MID1 | intros a F; destruct F].
      - eapply pres_mkR. exact X1. }
    split; [rewrite (getr_of_eqv _ _ 10 X1 eq_refl); reflexivity|].
    split; [apply (kp_stdio_ok mem m1 0 (bv_unsigned sp - 32) KLO HSO); unfold A_LIBC, A_OFL_LOCK; lia|].
    split; [apply (kp_guard_ok mem m1 0 (bv_unsigned sp - 32) KLO HGU); unfold A_GOT_GUARD, A_GUARD; lia|].
    split; [exact (ro_agree_munch _ _ _ RO MU1 (fun x Hx => OUTW x ltac:(lia)))|].
    split.
    { intros _. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU1|].
      split; [apply (kp_ofl_empty mem m1 0 (bv_unsigned sp - 32) KLO HOE); unfold A_OFL_HEAD; lia | exact RES]. }
    intros C. lia.
  - destruct (HBLK ltac:(lia)) as (INB & BF).
    destruct (pl_in_blocks_user L A b _ INB) as (pb & Hpb & Eb).
    pose proof (mr_blocks_range B _ LAWS L A mem md pb _ HMR Hpb) as (Hb4k & HbC). rewrite Eb in Hb4k, HbC.
    assert (E1_1 : getr R1 1 = reg_get regs 1) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); reflexivity).
    assert (E1_2 : getr R1 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); reflexivity).
    assert (E1_10 : getr R1 10 = wz b) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 (Z.of_nat (length Fc)))
      by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); reflexivity).
    assert (E1_12 : getr R1 12 = reg_get regs 11) by (rewrite (getr_of_eqv _ _ 12 X1 eq_refl); reflexivity).
    assert (SPZ1 : spZ R1 = bv_unsigned sp) by (unfold spZ; rewrite E1_2; reflexivity).
    assert (CP : call_pre_k B (aa_MR API) 8240 L A R1 m1 md).
    { eapply (kb_pre_A B API) with (K := 8240) (f := 0) (W := [(bv_unsigned sp - 32, bv_unsigned sp)]);
        [ exact PRE0 | lia | lia | lia | rewrite SPZ1; change (spZ regs) with (bv_unsigned sp); lia
        | rewrite SPZ1; exact HAL | rewrite E1_4; reflexivity
        | rewrite E1_1; exact HRA | exact MU1 | rewrite HSEG; exact WM1 | | ].
      - intros x _ Hx. change (spZ regs) with (bv_unsigned sp) in Hx. apply OUTW. lia.
      - intros x Hx _. apply OUTW. lia. }
    pose proof HFM as FM. unfold fmemopen_contract_cf in FM. rewrite HSEG in FM. unfold FMEMOPEN in FM.
    eapply SRcf_mono.
    { apply (FM L A R1 m1 md b Fc b0 eq_refl CP E1_10 E1_11).
      - rewrite E1_12. exact A1.
      - exact INB.
      - lia.
      - apply (kp_bytes_at mem m1 0 (bv_unsigned sp - 32) KLO); [exact BF | lia | lia].
      - apply (kp_stdio_ok mem m1 0 (bv_unsigned sp - 32) KLO HSO); unfold A_LIBC, A_OFL_LOCK; lia.
      - apply (kp_ofl_empty mem m1 0 (bv_unsigned sp - 32) KLO HOE); unfold A_OFL_HEAD; lia.
      - apply (kp_guard_ok mem m1 0 (bv_unsigned sp - 32) KLO HGU); unfold A_GOT_GUARD, A_GUARD; lia.
      - exact (ro_agree_munch _ _ _ RO MU1 (fun x Hx => OUTW x ltac:(lia))).
      - exact RES.
      - exact ROOM. }
    intros c' RET.
    destruct RET as (L' & A' & R2 & m2 & md2 & h & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & UBK & INIT
      & RLEN & RES' & MSTL & OFL & SO2 & GU2 & RO2).
    destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST) as [MIDc HPRES].
    unfold FMEMOPEN_K in *. rewrite SPZ1 in MIDc.
    exists L', A', R2, m2, md2, h.
    split; [rewrite E1_1; reflexivity|].
    assert (MID2 : kb_mid B API 8240 (bv_unsigned sp) L A mem md (fun a => False \/ fmemopen_writes h a) L' A' m2 md2).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDc | lia | lia | lia | lia |].
      intros a Ha1 Ha2. exfalso. lia. }
    split.
    { apply (kb_post B API).
      - eapply (kb_mid_E B API); [exact MID2|]. intros a [F|HW]; [destruct F | split; [exact NZ | exact HW]].
      - apply (kb_preserved_trans regs R1 R2); [eapply pres_mkR; exact X1 | exact HPRES]. }
    split; [exact A0'|]. split; [exact SO2|]. split; [exact GU2|]. split; [exact RO2|].
    split; [intros C; lia|].
    intros _.
    split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|]. split; [exact BLK|].
    split.
    { intros a k i Hin _ Hi.
      destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
      rewrite (KEPT a k i Hin ltac:(tauto) Hi).
      apply (munch_mbyte (ms_segs B) _ _ _ _ MU1); [lia | apply OUTW; lia]. }
    split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN|]. split; [exact RES'|].
    split; [exact MSTL | exact OFL].
Qed.

End K.
