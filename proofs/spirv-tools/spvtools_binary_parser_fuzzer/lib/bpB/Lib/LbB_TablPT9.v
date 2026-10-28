(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT5 LbB_TablPT6 LbB_TablPT8.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PT9.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Lemma sh_lt_2_45 : forall a, 0 <= a <= 2 ^ 47 -> sh a < 2 ^ 45 - 8.
  Proof. intros a Ha. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. Qed.

  Lemma pt_ok0_sh : forall e LBi pidi bi capi, ppre H e -> In (pidi, bi, 4 * capi) LBi -> ablock_range H bi (4 * capi) -> 0 < capi ->
    pt_ok0 H e LBi (sh bi, sh bi + nsh (4 * capi))
    /\ (sh bi + nsh (4 * capi) <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= sh bi).
  Proof.
    intros e LBi pidi bi capi P HIn ABR C0.
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & _ & _ & _ & _ & _ & _).
    pose proof P as (FF & _).
    pose proof (osframe_facts H _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (D1 : sh bi + nsh (4 * capi) <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh bi)
      by (apply aapp_disjoint_sh; [exact G10 | lia | unfold AAPP_HI; lia | lia]).
    assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    assert (F8 : p_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (D2 : sh bi + nsh (4 * capi) <= sh (p_ff e) \/ sh (p_ff e) + nsh 64 <= sh bi).
    { apply pt_sh_apart; [lia | lia | lia | lia | exact B8 | exact F8 |]. unfold AFS_SIZE, AFS_HDR in *. lia. }
    change (nsh 64) with 8 in D2.
    assert (SL : 0x6e7248 <= sh bi) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SH : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
    pose proof (sh_lt_2_45 (bi + 4 * capi) ltac:(lia)) as SB.
    unfold pt_ok0. cbn [fst snd].
    split; [|lia].
    split; [right; right; right; left; exists (pidi, bi, 4 * capi); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
    split; [apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; lia | right; left; lia]|].
    split; [apply stack0_ok_sh; lia|].
    unfold ATP. unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    unfold AFS_SIZE in *. lia.
  Qed.

  Lemma pt_ok0_stk : forall e LBi k, ppre H e -> 0 <= k <= PT_STACK - 224 ->
    pt_ok0 H e LBi (pS1 e - k, pS1 e) /\ (pS1 e <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= pS1 e - k).
  Proof.
    intros e LBi k P Hk.
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH1 & SH2 & _ & _ & _ & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (AK : aceil <= pS1 e - k) by (clear - Hk LO CE; lia).
    destruct (stack_window_ok H LBi (pLF e) (pS1 e - k) (pS1 e) AK FS2) as (W1 & W2 & W3).
    unfold pt_ok0. cbn [fst snd].
    split; [|lia].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [left; cbn [fst]; unfold AHI_LO; lia|].
    unfold ATP. lia.
  Qed.

  Lemma pt_ok0_slot : forall e LBi pidi bi capi a, ppre H e -> In (pidi, bi, 4 * capi) LBi -> ablock_range H bi (4 * capi) ->
    bi <= a -> a + 4 <= bi + 4 * capi ->
    pt_ok0 H e LBi (a, a + 4) /\ (a + 4 <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= a).
  Proof.
    intros e LBi pidi bi capi a P HIn ABR A1 A2.
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH1 & SH2 & _ & _ & _ & _).
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (D : a + 4 <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= a).
    { destruct (pt_app_sh a 4 (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left | right]; lia)) as [X|X];
      change (nsh 64) with 8 in X; lia. }
    unfold pt_ok0. cbn [fst snd].
    split; [|exact D].
    split; [right; right; left; exists (pidi, bi, 4 * capi); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia]|].
    split; [eapply (LbB_SR.aconst_ok_app bi (4 * capi)); [exact AP | lia | lia]|].
    split; [eapply (stack0_ok_aapp bi (4 * capi)); [exact AP | lia | lia]|].
    unfold ATP, AIMG_TOP in *. unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    unfold AFS_SIZE in *. lia.
  Qed.

  Lemma pt_ok0_hdr : forall e LBi bi capi pidi, ppre H e -> pgrown H e LBi bi capi pidi ->
    pt_ok0 H e LBi (p_v e + 8, p_v e + 16) /\ (p_v e + 16 <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= p_v e + 8).
  Proof.
    intros e LBi bi capi pidi P GR.
    pose proof (pgrown_blocks H HB e LBi bi capi pidi P GR) as BL.
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH1 & SH2 & _ & FB & _
                   & V8 & VB & VL & VF & _).
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OBJ & _ & _ & _ & _ & _ & _ & _ & _ & _
                     & CX & B0C & BB & BD).
    destruct OBJ as (_ & _ & WO & FW & CO & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (DB : p_v e + 16 <= p_b e \/ p_b e + 4 * p_cap e <= p_v e + 8).
    { destruct (Z.eq_dec (p_b e) 0) as [E|E]; [right; pose proof (B0C E); lia|]. destruct (BD E); lia. }
    assert (DS : p_v e + 16 <= sh (p_b e) \/ sh (p_b e) + nsh (4 * p_cap e) <= p_v e + 8).
    { destruct (pt_app_sh (p_v e + 8) 8 (p_b e) (4 * p_cap e) ltac:(destruct BB; lia) ltac:(lia) ltac:(destruct BB; lia)
                 ltac:(destruct VB; [left | right]; lia)) as [X|X]; lia. }
    assert (D : p_v e + 16 <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= p_v e + 8).
    { destruct (pt_app_sh (p_v e + 8) 8 (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left | right]; lia)) as [X|X];
      change (nsh 64) with 8 in X; lia. }
    unfold pt_ok0. cbn [fst snd].
    split; [|exact D].
    split.
    { replace (p_v e + 16) with (p_v e + 8 + 8) by lia.
      eapply (pt_awo_LBi H (p_LB e) LBi (p_v e + 8) 8 (p_b e) (4 * p_cap e)); [| lia | | lia | lia].
      - replace (p_v e + 8 + 8) with (p_v e + 16) by lia.
        exact (aclient_write_ok_sub H (p_LB e) (p_v e) (p_v e + 24) (p_v e + 8) (p_v e + 16) WO ltac:(lia) ltac:(lia)).
      - intros bb Hb. destruct (BL bb Hb) as [IN|(EQ & _)]; [left; exact IN | right; subst bb; cbn; split; reflexivity]. }
    split; [eapply (pt_afs_LF H (p_LF e) (pLF e)); [exact (afs_write_ok_sub H (p_LF e) (p_v e) (p_v e + 24) (p_v e + 8) (p_v e + 16) FW ltac:(lia) ltac:(lia))
                                                  | intros f Hf; right; exact Hf]|].
    split; [exact (aconst_ok_sub (p_v e) (p_v e + 24) (p_v e + 8) (p_v e + 16) CO ltac:(lia) ltac:(lia))|].
    split.
    { unfold stack0_ok. cbn [fst snd].
      assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      destruct VB as [VB|VB]; [right | left; unfold AHI_LO]; lia. }
    unfold ATP. unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct VL; destruct VF; lia.
  Qed.
End PT9.
