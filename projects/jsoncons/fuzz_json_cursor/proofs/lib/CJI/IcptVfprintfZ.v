(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm8RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel Arr StoreFast.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F8 Require Import F_memset F_memcpy F_fwritex F_pad F_fmt_fp_lib F_fmt_fp F_pop_arg Exit Printf_model Printf_mlib
  F_printf_iface F_printf_core F_printf_snsink F_sn_write F_vfprintf F_vsnprintf.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJM Require Import ShZero QcF IcptCells IcptCellsA RdnCells ShLoads IcptTryinitC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJI Require Import IcptPcomS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac lit_branch := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
  let c' := eval vm_compute in c in change c with c'; cbv iota end.

Lemma rdn1_some : forall (m : word -> option byte) a b0, seg_rom rsegs a = Some b0 -> exists b, rdn rsegs m a 1%nat = Some [b].
Proof. intros m a b0 H. cbn [rdn]. destruct (m a) as [b|]; [exists b; reflexivity | rewrite H; exists b0; reflexivity]. Qed.
Lemma seg_check_printf : seg_rom rsegs (Z_to_bv 64 0x1ee53c) = Some (Z_to_bv 8 0).
Proof. vmc_refl. Qed.

Lemma icpt_cells_xf : xframe icpt_cells.
Proof. intros W m m' HW MU H. exact (icpt_cells_munch W m m' HW MU H). Qed.

Section VF.
Hypothesis PCOM : pcom_stmt.

Theorem vfprintf_icpt_ok : vfprintf_icpt_stmt icpt_cells.
Proof.
  unfold vfprintf_icpt_stmt. intros until o. cbv zeta.
  intros -> -> -> FH FR CKC DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hbufp ST LO GLO QHI SSP MI FRM HA0 HA QF FVA VAHI QCK CKF CKHI DD1 DD2 DD3 GD
         ACX HFM FQ VAT SDq HDq HCKq HX NOS.
  pose proof ACX as (AE0 & ZL0 & ZB0 & ZR0 & XL1 & XL2 & XL3 & XL4 & XL5 & XL6).
  subst fmt. change (zlength FMT_G) with 6 in HA. cbn [zb FMT_G map] in BY. unfold va_area in VAA.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. change F_memcpy.rsegs with rsegs in SSP1, SSP2.
  destruct HX as (G1 & G2 & G3).
  pose proof (ro8_of_rdn rsegs m 0x153128 _ G1 ltac:(lia) ltac:(lia)) as RG1.
  pose proof (ro8_of_rdn rsegs m 0x154fe0 _ G2 ltac:(lia) ltac:(lia)) as RG2.
  unfold VFI_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep.
  carve_frame 48%nat ST.
  do 8 zstep.
  zstep.
  assert (HWx : IcptCellsA.aapp_all [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z)
    by (destruct HDq as [HDq1 HDq2]; IcptCellsA.aapp_tac).
  call (tryinit_callZ (bv_unsigned sp + -48 - lo)).
  1:{ assumption. } 1:{ lia. } 1:{ replace (bv_unsigned sp + -48 - (bv_unsigned sp + -48 - lo))%Z with lo by lia. exact ST. } 1:{ lia. } 1:{ reflexivity. }
  1:{ lazymatch goal with Hm : munch _ m _ |- _ => exact (aenv_ai _ (IcptCellsA.aenv_munch_a _ _ _ HWx Hm AE0)) end. }
  change F_memcpy.rsegs with rsegs in *.
  lazymatch goal with H : stk _ ?mm (bv_unsigned sp + -48 - (bv_unsigned sp + -48 - lo))%Z _ |- _ =>
    replace (bv_unsigned sp + -48 - (bv_unsigned sp + -48 - lo))%Z with lo in H by lia end.
  zstep. lit_branch.
  zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rdn1_some mm (Z_to_bv 64 0x1ee53c) _ seg_check_printf) as (bcp & HCP);
    pose proof (ro1_of_rdn rsegs mm 0x1ee53c bcp HCP ltac:(lia) ltac:(lia)) as RCP end.
  zstep. zstep. zstep.

  assert (TAIL : forall (mm : mem) (rav t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    rw_cells rsegs mm Fp (snfile_head 0 0 0 bufp 0 Exit.z64) -> rw_cells rsegs mm (Fp + 148) (snfile_rest CK) ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] -> rw_cells rsegs mm D [CB dn junkd] ->
    bytes_at rsegs mm A [Z_to_bv 8 37; Z_to_bv 8 49; Z_to_bv 8 46; Z_to_bv 8 42; Z_to_bv 8 103; Z_to_bv 8 0] ->
    bytes_at rsegs mm VA (u64s slots) ->
    rw_cells rsegs mm 1392368 [C8 (Z_to_bv 64 7015056)] -> rw_cells rsegs mm 7015056 [C8 canary] ->
    ro_cells rsegs mm 1396704 [C8 (Z_to_bv 64 1296156)] ->
    rw_cells rsegs mm (bv_unsigned sp + -48) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -48) -> mem_inv rsegs mm ->
    munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m mm -> wmono rsegs m mm ->
    evt rsegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
      (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 A) (Z_to_bv 64 Fp) a0' a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x6ec88) fc None mm (seg_rom rsegs))).
  { clear - FRM HF P1 AOK MODEL FPF ROOM Hn Hbufp LO GLO QHI HA0 HA QF FVA VAHI QCK CKF CKHI DD1 DD2 DD3 GD FQ VAT SDq HDq HCKq NOS
            AE0 ZL0 ZB0 ZR0 XL1 XL2 XL3 XL4 XL5 XL6 Rq HWx.
    intros mm rav t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FH2 FR2 CKC2 DST2 BY2 VAA2 SSP12 SSP22 RG22 FRF ST2 MI2 MU2 WM2.
    do 6 zstep.
    pose proof vfprintf_sn_proof as VF. unfold vfprintf_sn_stmt in VF.
    assert (ACX1 : acxo mm lo (bv_unsigned sp + -48) (bv_unsigned sp + -48 - 352) 80 Fp).
    { eapply acxo_munch; [| exact MU2 | exact HWx].
      split; [exact AE0|]. split; [eapply zsh_sub; [exact ZL0 | lia | lia]|]. split; [eapply zsh_sub; [exact ZL0 | lia | lia]|].
      split; [exact ZR0|]. repeat split; lia. }
    eapply evt_cut.
    { eapply VF with (Fp := Fp) (CK := CK) (D := D) (n := n) (bufp := bufp) (A := A) (VA := VA) (dn := dn) (junkd := junkd) (fmt := FMT_G)
                     (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT.
      all: try reflexivity.
      all: try (change (zlength FMT_G) with 6; lia).
      all: try lia.
      - exact FH2.
      - exact FR2.
      - exact CKC2.
      - exact DST2.
      - cbn [zb FMT_G map]. exact BY2.
      - exact HF.
      - unfold va_area. exact VAA2.
      - eapply args_ok_nos; [exact NOS | exact AOK].
      - exact MODEL.
      - exact FPF.
      - exact ST2.
      - split; [exact SSP12 | exact SSP22].
      - exact MI2.
      - exact FRM.
      - exact ACX1.
      - eapply fmtq_munch; [exact FQ | exact MU2 | apply IcptCellsA.aapp_in_app_all, HWx | lia | change (zlength FMT_G) with 6; lia].
      - eapply shz_transport; [exact SDq | exact MU2 | apply IcptCellsA.aapp_in_app_all, HWx | eapply IcptCellsA.app_sub; [exact (proj2 HDq) | unfold zlength; lia]].
      - exact HDq. }
    cbv beta. intros ms' P. unfold vfprintf_sn_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & fjunk & m4 & -> & MUc & WMc & MI4 & FRM' & FOK & ST4 & SSP4 & DST4 & CK4 & FJ4).
    lazymatch type of MUc with munch _ ?mm0 _ => transport_after_call rsegs mm0 m4 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x6eca0)) with (Z_to_bv 64 0x6eca0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    do 6 zstep.
    release_frame FRF ST4 (bv_unsigned sp).
    apply evt_done. unfold vfprintf_sn_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|]. split; [exact ST4|].
    split; [exact SSP4|]. split; [exact DST4|]. split; [exact CK4 | exact FJ4]. }
  if_cases K1; zify_cond K1.
  2:{
    do 5 zstep.
    eapply evt_cut.
    { eapply PCOM with (A := A) (VA := VA) (lo := lo); cbv zeta; rewrite ?unsigned_lit by lia.
      all: try reflexivity.
      - cbn [zb FMT_G map]. exact BY.
      - lia.
      - lia.
      - lazymatch goal with Hm : munch _ m ?mm |- shk _ ?mm _ _ =>
          pose proof (fmtq_munch _ _ _ _ _ FQ Hm (IcptCellsA.aapp_in_app_all _ HWx) ltac:(lia) ltac:(change (zlength FMT_G) with 6; lia)) as FQ1;
          pose proof (FQ1 0 6 ltac:(lia) ltac:(lia) ltac:(change (zlength FMT_G) with 6; lia)) as SK; rewrite Z.add_0_r in SK; exact SK end.
      - exact POST.
      - unfold PCOM_DEPTH. lia.
      - lia.
      - lia.
      - lazymatch goal with Hm : munch _ m ?mm |- aenv ?mm => exact (IcptCellsA.aenv_munch_a _ _ _ HWx Hm AE0) end.
      - assumption. }
    cbv beta. intros ms' P. unfold pcom_post in P. rewrite ?unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MUc & WMc & MIc & STc).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x6ec88)) with (Z_to_bv 64 0x6ec88) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply TAIL; eassumption. }

  eapply TAIL; eassumption.
Qed.
End VF.
