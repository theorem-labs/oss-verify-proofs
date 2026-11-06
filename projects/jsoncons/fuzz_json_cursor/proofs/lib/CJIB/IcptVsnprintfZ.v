(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm9RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel Arr StoreFast.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F9 Require Import F_memset F_memcpy F_fwritex F_pad F_fmt_fp_lib F_fmt_fp F_pop_arg Exit Printf_model Printf_mlib
  F_printf_iface F_printf_core F_printf_snsink F_sn_write F_vfprintf F_vsnprintf F_fmt_fp_nf.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJMB Require Import ShZero QcF IcptCells IcptCellsA RdnCells ShLoads IcptTryinitC FfpTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJIB Require Import IcptPcomS IcptPcomZ IcptVfprintfZ IcptQcW IcptHapp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac lit_branch := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
  let c' := eval vm_compute in c in change c with c'; cbv iota end.

Lemma lxor_land_ones : forall D, 0 <= D < 2^64 -> Z.lxor (Z.land D 18446744073709551615) 18446744073709551615 = 18446744073709551615 - D.
Proof.
  intros D HD. replace (Z.land D 18446744073709551615) with D.
  - apply zb_lxor_ones. lia.
  - change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia.
Qed.

Definition VSNI_DEPTH : Z := 8064.

Definition vsnprintf_icpt_stmt (X : mem -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells rsegs m D [CB dn junkd] ->
    bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts' y fl p t) (fp_calls (length fmt) fmt args) ->
    r = zlength o -> zlength o < 64 ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk rsegs m lo q -> (lo <= q - VSNI_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->

    IcptCells.aenv m -> ShZero.zsh m lo (q - 2160) -> ShZero.zsh m FfpTac.RODATA_LO FfpTac.RODATA_HI -> (0x10007fff8000 <= lo) -> (q <= 2^47) ->
    fmt = FMT_G -> fmtq m A fmt -> (VA + 8 * zlength slots <= 2^47) ->
    ShZero.shz rsegs m D (zlength o) -> (0x160040 <= D /\ ShZero.app D (Z.of_nat dn)) ->
    QcF.shk rsegs m D (zlength o + 1) ->
    X m ->
    evt rsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6f0a4) fc None m (seg_rom rsegs)).

Theorem vsnprintf_icpt_ok : vsnprintf_icpt_stmt icpt_cells.
Proof.
  unfold vsnprintf_icpt_stmt. intros until o. cbv zeta.
  intros -> -> -> -> DST BY HF P1 VAA NOS AOK MODEL FPF HR HR64 ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD
         AE0 ZL0 ZR0 XL1 XL2 HFM FQ VAT SDq HDq SKD HX.
  pose proof (vsnprintf_proof icpt_cells icpt_cells_xf (vfprintf_icpt_ok pcom_ok)) as VSN.
  subst fmt. change (zlength FMT_G) with 6 in HA. cbn [zb FMT_G map] in BY. unfold va_area in VAA.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. change F_memcpy.rsegs with rsegs in SSP1, SSP2.
  pose proof HX as (G1 & G2 & G3).
  pose proof (ro8_of_rdn rsegs m 0x1544f0 _ G1 ltac:(lia) ltac:(lia)) as RG1.
  pose proof (ro8_of_rdn rsegs m 0x1563b0 _ G3 ltac:(lia) ltac:(lia)) as RG3. clear G1 G2 G3.
  unfold VSNI_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (HWx : happ_all [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z) by (destruct HDq as [HDq1 HDq2]; happ_tac).
  carve_frame 96%nat ST.
  destruct (stk_split rsegs m lo (bv_unsigned sp + -2160) (bv_unsigned sp + -96) ST ltac:(lia)) as [ST0 STu]. clear ST. rename ST0 into ST.
  do 18 zstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j1 :: _ :: CB 8 ?j2 :: _) => set (ja := j1) in FR; set (jb := j2) in FR; clearbody ja jb end.
  call (tryinit_callZ (bv_unsigned sp + -2160 - lo)).
  1:{ assumption. } 1:{ lia. } 1:{ replace (bv_unsigned sp + -2160 - (bv_unsigned sp + -2160 - lo))%Z with lo by lia. exact ST. } 1:{ lia. } 1:{ reflexivity. }
  1:{ lazymatch goal with Hm : munch _ m _ |- _ => exact (aenv_ai _ (aenv_munch_h _ _ _ HWx Hm AE0)) end. }
  change F_memcpy.rsegs with rsegs in *.
  lazymatch goal with H : stk _ ?mm (bv_unsigned sp + -2160 - (bv_unsigned sp + -2160 - lo))%Z _ |- _ =>
    replace (bv_unsigned sp + -2160 - (bv_unsigned sp + -2160 - lo))%Z with lo in H by lia end.
  zstep. lit_branch.
  zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rdn1_some mm (Z_to_bv 64 0x1ef87c) _ seg_check_printf) as (bcp & HCP);
    pose proof (ro1_of_rdn rsegs mm 0x1ef87c bcp HCP ltac:(lia) ltac:(lia)) as RCP end.
  zstep. zstep. zstep.

  assert (TAIL : forall (mm : mem) (rav t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    rw_cells rsegs mm D [CB dn junkd] ->
    bytes_at rsegs mm A [Z_to_bv 8 37; Z_to_bv 8 49; Z_to_bv 8 46; Z_to_bv 8 42; Z_to_bv 8 103; Z_to_bv 8 0] ->
    bytes_at rsegs mm VA (u64s slots) ->
    rw_cells rsegs mm 1397432 [C8 (Z_to_bv 64 7019984)] -> rw_cells rsegs mm 7019984 [C8 canary] ->
    ro_cells rsegs mm 1401776 [C8 (Z_to_bv 64 1327064)] ->
    rw_cells rsegs mm (bv_unsigned sp + -96) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -2160) -> stk rsegs mm (bv_unsigned sp + -2160) (bv_unsigned sp + -96) -> mem_inv rsegs mm ->
    munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m mm -> wmono rsegs m mm ->
    evt rsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0' t1' t2' sp (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 2029608) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x6f11c) fc None mm (seg_rom rsegs))).
  { clear - VSN HF P1 NOS AOK MODEL FPF HR HR64 ROOM Hn Hn1 LO GLO QHI FRM HA0 HA QVA VAHI DD1 DVA GD AE0 ZL0 ZR0 XL1 XL2 FQ VAT SDq HDq SKD HX Rq HWx.
    intros mm rav t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DST2 BY2 VAA2 SSP12 SSP22 RG32 FRF ST2 STu2 MI2 MU2 WM2.
    do 7 zstep.
    eapply evt_cut.
    { eapply VSN with (D := D) (n := n) (A := A) (VA := VA) (dn := dn) (junkd := junkd) (fmt := FMT_G) (slots := slots) (args := args)
                      (lo := lo) (canary := canary) (r := r) (o := o);
        rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT.
      all: try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [CB _ _] => exact DST2
           | |- bytes_at _ _ _ (zb _) => cbn [zb FMT_G map]; exact BY2
           | |- Forall no_s _ => exact NOS
           | |- Forall _ (fp_calls _ _ _) => exact FPF
           | |- Forall _ FMT_G => exact HF
           | |- pass1_ok _ = true => exact P1
           | |- va_area _ _ _ => unfold va_area; exact VAA2
           | |- args_ok _ _ _ _ _ _ _ _ _ => eapply args_ok_nos; [exact NOS | exact AOK]
           | |- printf_model _ _ _ _ _ = _ => exact MODEL
           | |- stk _ _ _ _ => exact ST2
           | |- ssp_cells _ _ => split; [exact SSP12 | exact SSP22]
           | |- mem_inv _ _ => exact MI2
           | |- frm0 _ => exact FRM
           | |- IcptCells.aenv _ => exact (aenv_munch_h _ _ _ HWx MU2 AE0)
           | |- ShZero.zsh _ FfpTac.RODATA_LO _ =>
               eapply zsh_transport_h; [exact ZR0 | exact MU2 | exact HWx | unfold ShZero.app, RODATA_LO, RODATA_HI; left; lia]
           | |- ShZero.zsh _ _ _ =>
               eapply zsh_transport_h; [exact ZL0 | exact MU2 | exact HWx | unfold ShZero.app; right; lia]
           | |- fmtq _ _ _ => eapply fmtq_munch_h; [exact FQ | exact MU2 | exact HWx | lia | change (zlength FMT_G) with 6; lia]
           | |- ShZero.shz _ _ _ _ =>
               eapply shz_transport_h; [exact SDq | exact MU2 | exact HWx | eapply IcptCellsA.app_sub; [exact (proj2 HDq) | unfold zlength; lia]]
           | |- _ /\ ShZero.app _ _ => exact HDq
           | |- icpt_cells _ => exact (icpt_cells_munch_h _ _ _ HWx MU2 HX)
           | _ => idtac
           end.
      all: try (change (zlength FMT_G) with 6; lia).
    }
    cbv beta. intros ms' P. unfold vsnprintf_post in P. rewrite ?unsigned_lit in P by lia.
    destruct P as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & m4 & -> & MUc & WMc & MI4 & FRM' & FOK & ST4 & SSP4 & DST4).
    lazymatch type of MUc with munch _ ?mm0 _ => transport_after_call rsegs mm0 m4 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x6f138)) with (Z_to_bv 64 0x6f138) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (HRr : Z.land r 18446744073709551615 = r)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; unfold zlength in *; lia).
    assert (HR1 : Z.land (r + 1) 18446744073709551615 = r + 1)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; unfold zlength in *; lia).
    assert (HSW : bv_swrap 32 (r + 1) = r + 1).
    { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
      rewrite Z.mod_small by (unfold zlength in *; lia). lia. }
    assert (HDr : 0 <= D /\ D + Z.of_nat dn <= 0x7fffffffff00) by (destruct HDq as [_ [[? ?]|[? ?]]]; lia).
    pose proof (lxor_land_ones D ltac:(lia)) as HDx.
    zstep. if_cases K1; zify_cond K1.
    { exfalso. rewrite ?HRr in K1. unfold zlength in *. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite ?HRr, ?HSW, ?HR1 in K2. unfold zlength in *. lia. }
    do 5 zstep. if_cases K3; zify_cond K3.
    2:{ exfalso. rewrite ?HRr, ?HSW, ?HR1, ?HDx in K3. rewrite ?zb_lxor_ones in K3 by lia. unfold zlength in *. lia. }
    rewrite ?HRr, ?HSW, ?HR1.
    eapply qc_write.
    all: lazymatch goal with
         | |- Pm9RegionPoisoned.rt_layout_globs _ => exact (aenv_rt _ (aenv_munch_h _ _ _ HWx MU2 AE0))
         | |- shk _ _ _ _ =>
             rewrite HR; eapply shk_transport_h; [exact SKD | exact MU2 | exact HWx | eapply IcptCellsA.app_sub; [exact (proj2 HDq) | unfold zlength in *; lia]]
         | |- _ /\ _ => unfold zlength in *; split; lia
         | |- _ <= _ <= _ => unfold zlength in *; lia
         | _ => idtac
         end.

    intros a1'' a2'' a3'' a4'' a5''. change F_memcpy.rsegs with rsegs.
    do 12 zstep.
    pose proof (stk_merge rsegs _ _ _ _ ST4 STu2 ltac:(lia)) as STm. clear ST4 STu2.
    release_frame FRF STm (bv_unsigned sp).
    apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact STm|]. split; [exact SSP4|]. exact DST4. }
  if_cases K1; zify_cond K1.
  2:{
    do 5 zstep.
    eapply evt_cut.
    { eapply pcom_ok with (A := A) (VA := VA) (lo := lo); cbv zeta; rewrite ?unsigned_lit by lia.
      all: try reflexivity.
      all: lazymatch goal with
           | |- bytes_at _ _ _ _ => cbn [zb FMT_G map]; exact BY
           | |- shk _ ?mm _ _ => lazymatch goal with Hm : munch _ _ mm |- _ =>
                 pose proof (fmtq_munch_h _ _ _ _ _ FQ Hm HWx ltac:(lia) ltac:(change (zlength FMT_G) with 6; lia)) as FQ1;
                 pose proof (FQ1 0 6 ltac:(lia) ltac:(lia) ltac:(change (zlength FMT_G) with 6; lia)) as SK; rewrite Z.add_0_r in SK; exact SK end
           | |- stk _ _ _ _ => exact POST
           | |- aenv ?mm => lazymatch goal with Hm : munch _ _ mm |- _ => exact (aenv_munch_h _ _ _ HWx Hm AE0) end
           | |- mem_inv _ _ => assumption
           | |- _ => unfold PCOM_DEPTH; lia
           end. }
    cbv beta. intros ms' P. unfold pcom_post in P. rewrite ?unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MUc & WMc & MIc & STc).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x6f11c)) with (Z_to_bv 64 0x6f11c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply TAIL; eassumption. }

  eapply TAIL; eassumption.
Qed.
