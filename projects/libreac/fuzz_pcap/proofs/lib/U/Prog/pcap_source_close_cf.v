(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 153 of its 225 lines of code are new or changed and 994 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_struct.
Import ListNotations.
Open Scope Z_scope.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract KindBGlue SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import KindB pcap_lib fclose_c pcap_source_close_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import pcap_source_close fclose_cf_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import UContractCF.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis HFC : fclose_contract_cf B API.

Lemma close_evt_SRcf : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  ms_segs B = rsegs ->
  Exec.evt rsegs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof using.
  intros ms Q md P E. rewrite <- E. exact (evt_SRcf_canon B ms Q md P).
Qed.

Theorem pcap_source_close_cf_holds : pcap_source_close_contract_cf B API.
Proof.
  unfold pcap_source_close_contract_cf.
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
    eapply (close_evt_SRcf _ _ _ _ HSEG); [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold PCAP_SOURCE_CLOSE.
      eapply close_closed with (lo := bv_unsigned sp - 8256);
        [rewrite U10; exact HPS | rewrite U10; exact PSN | rewrite U10; exact PS8 | exact ST | lia | rewrite U10; exact PSS]. }
    intros ms1 (can1 & (a0' & m1 & -> & MU1 & WM1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    apply SRcf_ret.
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
    eapply (close_evt_SRcf _ _ _ _ HSEG); [ | exact Hh | exact Hl | ].
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
    pose proof HFC as FC. unfold fclose_contract_cf in FC. rewrite HSEG in FC. unfold FCLOSE in FC.
    eapply SRcf_bind.
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
    eapply (close_evt_SRcf _ _ _ _ HSEG); [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply close_epi with (sp0 := sp) (ra0 := reg_get regs 1) (s0o := reg_get regs 8);
        [ rewrite G2; exact SP1 | rewrite G8, U10; lia | exact FR2 | rewrite G8, U10; exact PS2 ]. }
    intros ms3 (can3 & (m3 & -> & PS3 & MU3 & WM3) & EQ3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    rewrite G8, U10 in PS3, MU3.
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    apply SRcf_ret.
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
