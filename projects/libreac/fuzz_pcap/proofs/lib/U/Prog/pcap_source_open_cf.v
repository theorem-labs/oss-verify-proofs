(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v; 26 of its 474 lines of code are new or changed and 618 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fread_c fread_ro_c pcap_source_struct pcap_lib.
Import ListNotations.
Open Scope Z_scope.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract KindBGlue SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import KindB pcap_lib fmemopen_c fclose_c
  libreac_fuzz_fopen_c pcap_source_open_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import pcap_source_open libreac_fuzz_fopen_cf_c fclose_cf_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import UContractCF.
Local Open Scope Z_scope.


Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HFO : libreac_fuzz_fopen_contract_cf B API.
Hypothesis HFR : fread_ro_contract.
Hypothesis HFC : fclose_contract_cf B API.

Lemma open_evt_SRcf : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  ms_segs B = rsegs ->
  Exec.evt rsegs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof using.
  intros ms Q md P E. rewrite <- E. exact (evt_SRcf_canon B ms Q md P).
Qed.

Theorem pcap_source_open_cf_holds : pcap_source_open_contract_cf B API.
Proof.
  unfold pcap_source_open_contract_cf.
  intros L A regs mem md ps pth b Fc f sw olen vtag vid pad b0 HSEG PRE A0 PSN PS8 PSS HPS HA11 PN0 HPB HPD HG HN26
    HBLK HSO HOE HGU RO RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  assert (IL : img_low B).
  { eapply img_low_of_check with (C := (symaddr ImgPages.Ubsan.top)); [unfold img_check; rewrite HSEG; vm_compute; reflexivity | lia]. }
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold OPEN_K in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof HPS as (_ & HP0 & HP24 & _). unfold ps_cells in HP24. cbn in HP24.
  pose proof HPB as (HPB0 & HPB1 & _).
  change (length (PATH_STR ++ [Z_to_bv 8 0])) with 13%nat in HPB1.
  assert (U10 : bv_unsigned (reg_get regs 10) = ps)
    by (change (reg_get regs 10) with (getr regs 10); rewrite A0; apply unsigned_lit; lia).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8304) (bv_unsigned sp)).
  { pose proof (kb_stk B API IL 8304 L A regs mem md PRE0 ltac:(lia)) as X. rewrite HSEG in X. exact X. }
  assert (OUTW : forall x, ~ (bv_unsigned sp - 64 <= x < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 64, bv_unsigned sp)] x) by (intros x Hx; cbn; split; [exact Hx | exact I]).
  assert (NOWN0 : forall a, alloc_ceiling <= a -> ~ owned B L A a).
  { intros a Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho). lia. }
  rewrite HSEG in RO, HWS, HERR.
  rewrite HSEG.
  eapply (open_evt_SRcf _ _ _ _ HSEG); [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold PCAP_SOURCE_OPEN.
    eapply open_pro with (lo := bv_unsigned sp - 8304); [exact ST | lia]. }
  intros ms1 (can1 & (sp1 & m1 & junk & -> & SP1 & FR1 & MU1 & WM1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0x2c)%Z)) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); reflexivity).
  assert (E1_2 : getr R1 2 = sp1) by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); reflexivity).
  assert (E1_8 : getr R1 8 = reg_get regs 10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 pth) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); exact HA11).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 A_MODE) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); reflexivity).
  assert (SPZ1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E1_2; exact SP1).
  pose proof (keep_munch _ _ _ 0 (bv_unsigned sp - 64) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
    as KLO.
  pose proof (keep_munch _ _ _ (bv_unsigned sp) (2 ^ 64) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
    as KHI.
  destruct (open_frame m1 _ junk _ _ _ _ FR1) as (junk' & FRa & FRb).
  replace (bv_unsigned sp - 64 + 8 + 24) with (bv_unsigned sp - 64 + 32) in FRb by lia.
  assert (MID1 : kb_mid B API 8304 (bv_unsigned sp) L A mem md (fun _ => False) L A m1 md).
  { eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 64, bv_unsigned sp)]);
      [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite HSEG; exact WM1 | | ].
    - intros a [Ha|Ha]; rewrite HSEG; [apply HWS; lia | apply HERR; exact Ha].
    - intros x _ Hs _. apply OUTW. lia.
    - intros x Hx _. apply OUTW. lia. }
  assert (CP : call_pre_k B (aa_MR API) 8240 L A R1 m1 md).
  { eapply (kb_pre_A B API) with (K := 8304) (f := 64) (W := [(bv_unsigned sp - 64, bv_unsigned sp)]);
      [ exact PRE0 | lia | lia | lia | exact SPZ1 | | rewrite E1_4; reflexivity | | exact MU1
      | rewrite HSEG; exact WM1 | | ].
    - rewrite SPZ1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - intros x _ Hx. change (spZ regs) with (bv_unsigned sp) in Hx. apply OUTW. lia.
    - intros x Hx _. apply OUTW. lia. }
  assert (HPB1' : bytes_at rsegs m1 pth (PATH_STR ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer rsegs mem m1 pth _ HPB). intros i Hi. change (length (PATH_STR ++ [Z_to_bv 8 0])) with 13%nat in Hi.
    apply (munch_mbyte rsegs _ _ _ _ MU1); [lia | apply OUTW; lia]. }
  pose proof HFO as FO. unfold libreac_fuzz_fopen_contract_cf in FO. rewrite HSEG in FO. unfold LIBREAC_FUZZ_FOPEN in FO.
  eapply SRcf_bind.
  { apply (FO L A R1 m1 md pth b Fc b0 eq_refl CP E1_10 PN0 HPB1').
    - rewrite SPZ1. unfold FOPEN_K. lia.
    - exact E1_11.
    - apply (kp_bytes_at mem m1 0 (bv_unsigned sp - 64) KLO); [exact HG | unfold G_FILE_LEN; lia |].
      rewrite length_app, !length_le8. unfold G_FILE_LEN. lia.
    - exact HN26.
    - intros HL1. destruct (HBLK HL1) as (INB & BF). split; [exact INB|].
      destruct (pl_in_blocks_user L A b _ INB) as (pb & Hpb & Eb).
      pose proof (mr_blocks_range B _ LAWS L A mem md pb _ HMR Hpb) as (Hb4k & HbC). rewrite Eb in Hb4k, HbC.
      apply (kp_bytes_at mem m1 0 (bv_unsigned sp - 64) KLO); [exact BF | lia | lia].
    - apply (kp_stdio_ok mem m1 0 (bv_unsigned sp - 64) KLO HSO); unfold A_LIBC, A_OFL_LOCK; lia.
    - apply (kp_ofl_empty mem m1 0 (bv_unsigned sp - 64) KLO HOE); unfold A_OFL_HEAD; lia.
    - apply (kp_guard_ok mem m1 0 (bv_unsigned sp - 64) KLO HGU); unfold A_GOT_GUARD, A_GUARD; lia.
    - exact (ro_agree_munch _ _ _ RO MU1 (fun x Hx => OUTW x ltac:(lia))).
    - exact RES.
    - exact ROOM. }
  intros c2 RET.
  destruct RET as (L1 & A1 & R2 & m2 & md1 & h & -> & POST & A0' & SO2 & GU2 & RO2 & HZ & HNZ).
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST) as [MIDc HPRES].
  pose proof POST as (HMR1 & HWF1 & HBD1 & HLE1 & HPA1 & _ & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
  rewrite SPZ1 in MIDc. unfold FOPEN_K in *.
  rewrite E1_1.
  assert (G2 : reg_get R2 2 = sp1) by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (G4 : reg_get R2 4 = reg_get regs 4) by exact (eq_trans (HPRES 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (G8 : reg_get R2 8 = reg_get regs 10) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (NOWN1 : forall a, alloc_ceiling <= a -> ~ owned B L1 A1 a).
  { intros a Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR1 Ho). lia. }
  destruct (Nat.eq_dec (length Fc) 0) as [LZ|LNZ].
  - destruct (HZ LZ) as (-> & -> & -> & -> & MUz & OFE2 & RES2).
    rewrite SPZ1 in MUz.
    assert (MID2 : kb_mid B API 8304 (bv_unsigned sp) L A mem md (fun a => False \/ fopen_writes 0 a) L A m2 md).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDc | lia | lia | lia | lia |].
      intros a _ _ (C & _). apply C. reflexivity. }
    assert (KZ : forall x, bv_unsigned sp - 64 <= x < 2 ^ 64 ->
       mbyte rsegs m2 x = mbyte rsegs m1 x /\ (writable_at rsegs m1 x -> writable_at rsegs m2 x)).
    { apply (keep_munch _ _ _ (bv_unsigned sp - 64) (2 ^ 64) MUz); [lia | lia |].
      intros x Hx. cbn. split; [lia | exact I]. }
    eapply (open_evt_SRcf _ _ _ _ HSEG); [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply open_null with (sp0 := sp) (ra0 := reg_get regs 1) (s0o := reg_get regs 8) (s1o := reg_get regs 9)
        (s2o := reg_get regs 18).
      - exact A0'.
      - rewrite G8, U10. exact PSN.
      - rewrite G8, U10. exact PS8.
      - rewrite G2. exact SP1.
      - rewrite G8, U10. lia.
      - rewrite G8, U10. apply (kp_rw_cells m1 m2 _ _ KZ); [| lia | unfold ps_cells; cbn; lia].
        apply (kp_rw_cells mem m1 _ _ KHI); [exact HPS | lia | unfold ps_cells; cbn; lia].
      - rewrite G2, SP1. apply (kp_rw_cells m1 m2 _ _ KZ); [exact FRb | lia | cbn; lia]. }
    intros ms3 (can3 & (a3' & m3 & -> & PS3 & MU3 & WM3) & EQ3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    rewrite G8, U10 in PS3, MU3.
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    apply SRcf_ret.
    exists L, A, R3, m3, md, 0.
    split; [reflexivity|].
    assert (OUT3 : forall x, x < ps -> outside [(ps, ps + 22)] x) by (intros x Hx; cbn; split; [lia | exact I]).
    pose proof (keep_munch _ _ _ 0 ps MU3 ltac:(lia) ltac:(lia) (fun x Hx => OUT3 x ltac:(lia))) as KL3.
    assert (MID3 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                     (fun a => (False \/ fopen_writes 0 a) \/ (ps <= a < ps + 22)) L A m3 md).
    { eapply (kb_mid_tail B API IL) with (W := [(ps, ps + 22)]);
        [ exact MID2 | exact MU3 | rewrite HSEG; exact WM3 | | | | ].
      - apply (op_present B HSEG _ _ _ MU3 WM3). intros x Hx Ho Hi.
        pose proof (in_img_low B HSEG x Hi). apply Ho. cbn. split; [lia | exact I].
      - intros x Hx Hs He. apply outside_one. lia.
      - intros x Hx _. apply outside_one. lia.
      - intros q n i Hin Hin' Hi.
        destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
        apply outside_one. lia. }
    assert (PRES : regs_preserved regs R3).
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18)) regs R1 R2 R3 _ _ X1 HPRES X3).
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
      intros a [[F|HW]|HW]; [destruct F | left; exact HW | right; left; exact HW]. }
    split; [apply (kp_stdio_ok m2 m3 0 ps KL3 SO2); unfold A_LIBC, A_OFL_LOCK; lia|].
    split; [apply (kp_guard_ok m2 m3 0 ps KL3 GU2); unfold A_GOT_GUARD, A_GUARD; lia|].
    split; [exact (ro_agree_munch _ _ _ RO2 MU3 (fun x Hx => OUT3 x ltac:(lia)))|].
    split.
    { intros _.
      split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); reflexivity|].
      split; [exact PS3|].
      split; [apply (kp_ofl_empty m2 m3 0 ps KL3 OFE2); unfold A_OFL_HEAD; lia|].
      split; [reflexivity|].
      split.
      { intros a k i Hin _ Hi.
        destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
        rewrite (munch_mbyte (ms_segs B) _ _ _ _ MU3) by (try lia; apply OUT3; lia).
        rewrite (munch_mbyte (ms_segs B) _ _ _ _ MUz) by first [lia | cbn; split; [lia | exact I]].
        apply (munch_mbyte (ms_segs B) _ _ _ _ MU1); [lia | apply OUTW; lia]. }
      split; [intros q k Hin _; exact Hin|].
      split; [lia|].
      split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | exact RES2]|].
      intros C. lia. }
    intros C. unfold pcap_good in C. rewrite LZ in C. cbn in C. discriminate C.
  - destruct (HNZ ltac:(lia)) as (HN0 & HAL16 & FRESH & BLK & KEPT & UBK & INIT & RLEN & RES1 & MSTL & OFL).
    destruct BLK as (b1 & b2 & EB1 & EB).
    pose proof FRESH as (FR4k & FRC & FRimg).
    destruct (HBLK ltac:(lia)) as (INB & BF).
    destruct (pl_in_blocks_user L A b _ INB) as (pb & Hpb & Eb).
    pose proof (mr_blocks_range B _ LAWS L A mem md pb _ HMR Hpb) as (Hb4k & HbC). rewrite Eb in Hb4k, HbC.
    assert (U2_10 : bv_unsigned (reg_get R2 10) = h)
      by (change (reg_get R2 10) with (getr R2 10); rewrite A0'; apply unsigned_lit; lia).
    assert (R2_10 : reg_get R2 10 = Z_to_bv 64 h) by exact A0'.
    assert (INH1 : In (h, 1304) (blocks L1 A1)) by (rewrite EB1; apply in_or_app; right; left; reflexivity).
    assert (MID2 : kb_mid B API 8304 (bv_unsigned sp) L A mem md (fun a => False \/ fopen_writes h a) L1 A1 m2 md1).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDc | lia | lia | lia | lia |].
      intros a Ha1 Ha2 (_ & HW). unfold fmemopen_writes, A_OFL_HEAD in HW. lia. }
    assert (KH2 : forall a, bv_unsigned sp - 64 <= a < 2 ^ 64 ->
       mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs m2 a)).
    { intros a Ha. rewrite <- HSEG.
      destruct (HFRAME1 a ltac:(left; lia) (NOWN0 a ltac:(lia)) (NOWN1 a ltac:(lia))) as [E W].
      - unfold scratch_k. rewrite SPZ1. intros [H|H]; lia.
      - unfold fopen_writes, fmemopen_writes, A_OFL_HEAD. intros (_ & [H|H]); lia.
      - split; [exact E | intros Hw; apply W; exact Hw]. }
    eapply (open_evt_SRcf _ _ _ _ HSEG); [ | exact Hh1 | exact Hl1 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply (open_mid HFR) with (lo := bv_unsigned sp - 8304) (b := b) (Fc := Fc) (f := f) (sw := sw) (olen := olen)
        (vtag := vtag) (vid := vid) (pad := pad) (junk := junk') (sp0 := sp) (ra0 := reg_get regs 1)
        (s0o := reg_get regs 8) (s1o := reg_get regs 9) (s2o := reg_get regs 18).
      - rewrite U2_10. exact HN0.
      - rewrite G8, U10. exact PSN.
      - rewrite G8, U10. exact PS8.
      - rewrite G2. exact SP1.
      - lia.
      - rewrite G8, U10. lia.
      - rewrite G8, U10. apply (kp_rw_cells m1 m2 _ _ KH2); [| lia | unfold ps_cells; cbn; lia].
        apply (kp_rw_cells mem m1 _ _ KHI); [exact HPS | lia | unfold ps_cells; cbn; lia].
      - rewrite G2, SP1. apply (kp_rw_cells m1 m2 _ _ KH2); [exact FRa | lia | cbn; lia].
      - rewrite G2, SP1. apply (kp_rw_cells m1 m2 _ _ KH2); [exact FRb | lia | cbn; lia].
      - rewrite G2, SP1. apply op_stk; [lia | lia |]. intros a Ha. rewrite <- HSEG. apply HSCR1.
        unfold scratch_k. rewrite SPZ1. left. lia.
      - rewrite G2, SP1. lia.
      - rewrite U2_10. exact MSTL.
      - rewrite U2_10. intros i Hi. unfold wa. apply (ro_addr_out B HSEG); [lia | apply FRimg; lia].
      - rewrite G2, SP1. intros i Hi. unfold wa. apply ro_addr_hi. lia.
      - rewrite G2, SP1. intros i Hi. unfold wa. apply ro_addr_hi. lia.
      - rewrite U2_10. lia.
      - lia.
      - lia.
      - exact RO2. }
    intros ms3 (can3 & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3
      & HOR & MU3 & WM3 & RO3) & EQ3).
    rewrite G2, SP1, U2_10, G8, U10 in MU3.
    assert (OUTI : forall a, in_img B a ->
      outside [(bv_unsigned sp - 64 - 112, bv_unsigned sp); (h, h + 1304); (ps, ps + 22)] a).
    { intros a Ha. pose proof (in_img_low B HSEG a Ha) as Hlow. cbn [outside].
      split; [lia|]. split; [|split; [lia | exact I]].
      intros Hin. apply (FRimg (a - h)); [lia|]. replace (h + (a - h)) with a by lia. exact Ha. }
    assert (KI3 : forall a, in_img B a ->
      mbyte rsegs m3 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a -> writable_at rsegs m3 a)).
    { intros a Ha. pose proof (in_img_low B HSEG a Ha) as Hlow.
      split; [apply (munch_mbyte rsegs _ _ _ _ MU3); [lia | exact (OUTI a Ha)]|].
      intros Hw. apply (proj1 (munch_writable rsegs _ _ _ a MU3 ltac:(lia) (OUTI a Ha))). exact Hw. }
    pose proof (ki_stdio_ok B HSEG m2 m3 KI3 SO2) as SO3.
    pose proof (ki_guard_ok B HSEG m2 m3 KI3 GU2) as GU3.
    pose proof (ki_ofl_one B HSEG m2 m3 KI3 h OFL) as OFL3.
    assert (MID3 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                     (fun a => (False \/ fopen_writes h a) \/
                        (fopen_writes h a \/ (ps <= a < ps + 22) \/ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)))
                     L1 A1 m3 md1).
    { eapply (kb_mid_tail B API IL) with (W := [(bv_unsigned sp - 64 - 112, bv_unsigned sp); (h, h + 1304); (ps, ps + 22)]);
        [ exact MID2 | exact MU3 | rewrite HSEG; exact WM3 | | | | ].
      - apply (op_present B HSEG _ _ _ MU3 WM3). intros x Hx Ho Hi. apply Ho. exact (OUTI x Hi).
      - intros x Hx Hs He. cbn [outside]. split; [lia|]. split; [|split; [| exact I]].
        + intros Hin. apply He. left. split; [exact HN0 | right; lia].
        + intros Hin. apply He. right. left. lia.
      - intros x Hx Ho. cbn [outside]. split; [lia|]. split; [|split; [lia | exact I]].
        intros Hin. destruct (block_facts B _ LAWS L1 A1 m2 md1 h 1304 (x - h) HMR1 INH1 ltac:(lia)) as (_ & _ & _ & No).
        apply No. replace (h + (x - h)) with x by lia. exact Ho.
      - intros q n i Hin Hin' Hi.
        pose proof (pl_in_blocks_of_user L A q n Hin) as INq.
        destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
        rewrite EB in INq.
        destruct (blocks_mid_disjoint B _ LAWS L1 A1 m2 md1 b1 b2 h 1304 _ _ HMR1 EB1 INq) as [D|D];
          cbn [outside]; (split; [lia|]); (split; [lia|]); (split; [lia | exact I]). }
    assert (KB3 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
                    mbyte (ms_segs B) m3 (a + i) = mbyte (ms_segs B) mem (a + i)).
    { intros a k i Hin Hi.
      destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
      pose proof Hin as Hin2. rewrite EB in Hin2.
      destruct (blocks_mid_disjoint B _ LAWS L1 A1 m2 md1 b1 b2 h 1304 _ _ HMR1 EB1 Hin2) as [D|D];
        (rewrite (munch_mbyte (ms_segs B) _ _ _ _ MU3)
           by first [lia | cbn [outside]; (split; [lia|]); (split; [lia|]); (split; [lia | exact I])]);
        (rewrite (KEPT a k i Hin ltac:(tauto) Hi));
        (apply (munch_mbyte (ms_segs B) _ _ _ _ MU1); [lia | apply OUTW; lia]). }
    destruct HOR as [(GD & -> & PS3 & MS3) | (BD & (s1' & s2' & ->) & PS3 & FR3 & MS3)];
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    + rewrite G8, U10, R2_10 in PS3. rewrite U2_10 in MS3.
      assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
      rewrite RP.
      apply SRcf_ret.
      exists L1, A1, R3, m3, md1, h.
      split; [reflexivity|].
      assert (PRES : regs_preserved regs R3).
      { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18)) regs R1 R2 R3 _ _ X1 HPRES X3).
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
        intros a [[F|HW]|[HW|[HW|HW]]];
          [destruct F | left; exact HW | left; exact HW | right; left; exact HW | right; right; split; [exact HN0 | exact HW]]. }
      split; [exact SO3|]. split; [exact GU3|]. split; [exact RO3|].
      split; [intros C; congruence|].
      intros _.
      split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); reflexivity|].
      split; [exact HN0|]. split; [exact HAL16|]. split; [exact FRESH|].
      split; [exact PS3|].
      split; [exists b1, b2; split; [exact EB1 | exact EB]|].
      split; [intros a k i Hin _ Hi; exact (KB3 a k i Hin Hi)|].
      split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN|]. split; [exact RES1|].
      split; [exact MS3 | exact OFL3].
    + rewrite G8, U10, R2_10 in PS3. rewrite U2_10 in MS3. rewrite G2, SP1 in FR3.
      assert (E3_1 : getr R3 1 = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0xc8)%Z)) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); reflexivity).
      assert (E3_2 : getr R3 2 = sp1) by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); exact G2).
      assert (E3_4 : getr R3 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); exact G4).
      assert (E3_8 : getr R3 8 = reg_get regs 10) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); exact G8).
      assert (E3_10 : getr R3 10 = Z_to_bv 64 h) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); exact R2_10).
      assert (SPZ3 : spZ R3 = bv_unsigned sp - 64) by (unfold spZ; rewrite E3_2; exact SP1).
      assert (CP2 : call_pre_k B (aa_MR API) 8240 L1 A1 R3 m3 md1).
      { eapply (op_pre B API) with (K := 8304) (f := 64) (regs := regs) (mem := mem) (md := md) (L := L) (A := A);
          [ exact PRE0 | exact MID3 | exact INIT | lia | lia | lia | exact SPZ3 | | rewrite E3_4; reflexivity | ].
        - rewrite SPZ3. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
          rewrite Z.mod_add by lia. exact HAL.
        - rewrite E3_1. apply bv_eq. vm_compute. reflexivity. }
      pose proof MID3 as (HMR3 & _).
      pose proof HFC as FC. unfold fclose_contract_cf in FC. rewrite HSEG in FC. unfold FCLOSE in FC.
      eapply SRcf_bind.
      { apply (FC L1 A1 R3 m3 md1 h b (Z.min 24 (Z.of_nat (length Fc))) Fc (sb_malloc b0 1304) eq_refl CP2 E3_10 INH1).
        - rewrite EB1. rewrite EB in INB. apply in_app_or in INB as [I|I]; apply in_or_app; [left; exact I | right; right; exact I].
        - exact MS3.
        - exact OFL3.
        - exact SO3.
        - exact GU3.
        - exact RO3.
        - exact RES1. }
      intros c4 RET2.
      destruct RET2 as (L2 & A2 & R4 & m4 & md2 & -> & POST2 & A0'' & BLK2 & KEPT2 & UBK2 & INIT2 & RLEN2 & RES2
        & OFE4 & SO4 & GU4 & RO4 & BF4).
      destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST2) as [MIDc2 HPRES2].
      pose proof POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HPA2 & _ & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
      destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
      rewrite SPZ3 in MIDc2. unfold FCLOSE_K in *.
      assert (NOWN2 : forall a, alloc_ceiling <= a -> ~ owned B L2 A2 a).
      { intros a Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho). lia. }
      assert (MID4 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                       (fun a => ((False \/ fopen_writes h a) \/
                          (fopen_writes h a \/ (ps <= a < ps + 22) \/ (ms_ctx B <= a < ms_ctx B + CTX_SIZE))) \/
                          fclose_writes h a) L2 A2 m4 md2).
      { eapply (op_seqXX B API); [exact MID3 | exact MIDc2 | exact UBK | exact RLEN | | lia | lia | lia | lia |].
        - intros a Ha No No2 NE1 NE2 [Hao|Hst]; [|apply No; right; exact Hst].
          apply NE1. right. right. right. exact (ax_img AX L1 A1 m3 md1 a HMR3 Ha Hao).
        - intros a Ha1 Ha2 HW. unfold fclose_writes, A_OFL_HEAD in HW. lia. }
      assert (G4_2 : reg_get R4 2 = sp1) by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) E3_2).
      assert (G4_8 : reg_get R4 8 = reg_get regs 10)
        by exact (eq_trans (HPRES2 8 ltac:(unfold callee_saved; lia)) E3_8).
      assert (KH4 : forall a, bv_unsigned sp - 64 <= a < 2 ^ 64 ->
         mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a -> writable_at rsegs m4 a)).
      { intros a Ha. rewrite <- HSEG.
        destruct (HFRAME2 a ltac:(left; lia) (NOWN1 a ltac:(lia)) (NOWN2 a ltac:(lia))) as [E W].
        - unfold scratch_k. rewrite SPZ3. intros [H|H]; lia.
        - unfold fclose_writes, A_OFL_HEAD. intros [H|H]; lia.
        - split; [exact E | intros Hw; apply W; exact Hw]. }
      rewrite E3_1.
      eapply (open_evt_SRcf _ _ _ _ HSEG); [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        eapply open_tail with (sp0 := sp) (ra0 := reg_get regs 1) (s0o := reg_get regs 8) (s1o := reg_get regs 9)
          (s2o := reg_get regs 18) (f := Z_to_bv 64 h) (sw := sw) (olen := wz 0) (vtag := wz 0) (vid := wz 0) (pad := pad).
        - rewrite G4_2. exact SP1.
        - rewrite G4_8, U10. lia.
        - rewrite G4_8, U10. apply (kp_rw_cells m3 m4 _ _ KH4); [exact PS3 | lia | unfold ps_cells; cbn; lia].
        - rewrite G4_2, SP1. apply (kp_rw_cells m3 m4 _ _ KH4); [exact FR3 | lia | cbn; lia]. }
      intros ms5 (can5 & (m5 & -> & PS5 & MU5 & WM5) & EQ5).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
      rewrite G4_8, U10 in PS5, MU5.
      assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
      rewrite RP.
      apply SRcf_ret.
      exists L2, A2, R5, m5, md2, h.
      split; [reflexivity|].
      assert (OUT5 : forall x, x < ps -> outside [(ps, ps + 8)] x) by (intros x Hx; cbn; split; [lia | exact I]).
      pose proof (keep_munch _ _ _ 0 ps MU5 ltac:(lia) ltac:(lia) (fun x Hx => OUT5 x ltac:(lia))) as KL5.
      assert (MID5 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                       (fun a => (((False \/ fopen_writes h a) \/
                          (fopen_writes h a \/ (ps <= a < ps + 22) \/ (ms_ctx B <= a < ms_ctx B + CTX_SIZE))) \/
                          fclose_writes h a) \/ (ps <= a < ps + 8)) L2 A2 m5 md2).
      { eapply (kb_mid_tail B API IL) with (W := [(ps, ps + 8)]);
          [ exact MID4 | exact MU5 | rewrite HSEG; exact WM5 | | | | ].
        - apply (op_present B HSEG _ _ _ MU5 WM5). intros x Hx Ho Hi.
          pose proof (in_img_low B HSEG x Hi). apply Ho. cbn. split; [lia | exact I].
        - intros x Hx Hs He. apply outside_one. lia.
        - intros x Hx _. apply outside_one. lia.
        - intros q n i Hin Hin' Hi.
          destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
          apply outside_one. lia. }
      assert (PRES : regs_preserved regs R5).
      { eapply (op_chain2 (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18)) regs R1 R2 R3 R4 R5 _ _ _ X1 HPRES X3 HPRES2 X5).
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; [reflexivity | split; reflexivity]]|]).
          subst r. split; [reflexivity | split; reflexivity].
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
          subst r. discriminate O. }
      split.
      { apply (kb_post B API); [|exact PRES].
        eapply (kb_mid_E B API); [exact MID5|].
        intros a [[[[F|HW]|[HW|[HW|HW]]]|HW]|HW];
          [ destruct F | left; exact HW | left; exact HW | right; left; exact HW
          | right; right; split; [exact HN0 | exact HW] | left; split; [exact HN0 | exact HW]
          | right; left; lia ]. }
      split; [apply (kp_stdio_ok m4 m5 0 ps KL5); [exact SO4 | unfold A_LIBC; lia | unfold A_OFL_LOCK; lia]|].
      split; [apply (kp_guard_ok m4 m5 0 ps KL5); [exact GU4 | unfold A_GOT_GUARD; lia | unfold A_GUARD; lia]|].
      split; [exact (ro_agree_munch _ _ _ RO4 MU5 (fun x Hx => OUT5 x ltac:(lia)))|].
      split.
      { intros _.
        split; [rewrite (getr_of_eqv _ _ 10 X5 eq_refl); reflexivity|].
        split; [exact PS5|].
        split; [apply (kp_ofl_empty m4 m5 0 ps KL5 OFE4); unfold A_OFL_HEAD; lia|].
        split.
        { destruct BLK2 as (c1 & c2 & EC1 & EC2). rewrite EC2, EB.
          symmetry. apply (op_rm_unique b1 b2 c1 c2 (h, 1304)).
          - rewrite <- EB1. exact (mr_blocks_disjoint B _ LAWS L1 A1 m3 md1 HMR3).
          - cbn. lia.
          - rewrite <- EB1. exact EC1. }
        split.
        { intros a k i Hin _ Hi.
          destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
          pose proof Hin as Hin2. rewrite EB in Hin2.
          assert (Hne : a <> h).
          { destruct (blocks_mid_disjoint B _ LAWS L1 A1 m2 md1 b1 b2 h 1304 _ _ HMR1 EB1 Hin2) as [D|D]; lia. }
          assert (Hin1 : In (a, k) (blocks L1 A1)).
          { rewrite EB1. apply in_app_or in Hin2 as [I|I]; apply in_or_app; [left; exact I | right; right; exact I]. }
          rewrite (munch_mbyte (ms_segs B) _ _ _ _ MU5) by (try lia; apply OUT5; lia).
          rewrite (KEPT2 a k i Hin1 Hne Hi).
          exact (KB3 a k i Hin Hi). }
        split.
        { intros q k Hin Hne. apply (UBK2 q k (UBK q k Hin)). rewrite (HPA1 q k Hin (UBK q k Hin)). exact Hne. }
        split; [lia|].
        split; [intros C; lia|].
        intros _. split; [exact HN0|]. split; [exact FRESH|]. split; [exact (INIT2 INIT)|]. split; [exact RES2|].
        apply (kp_bytes_at m4 m5 0 ps KL5); [exact BF4 | lia | lia]. }
      intros C. congruence.
Qed.

End K.
