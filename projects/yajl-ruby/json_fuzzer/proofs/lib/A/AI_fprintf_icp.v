(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_monadx AM_syscalls AM_memset AM_memcpy AM_stdio_lib AX_file AM_fwrite AI_shadow AI_globals2 AI_gtrans AI_region_is_poisoned AI_pcommon AP_policy AP_mjx AP_fwritex AP_fwritex_gen AP_pop_arg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_pieces Printf_bridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AP_printf_iface AP_mlibA AP_piecesA AP_printf_core AP_vfprintf AP_stdio_flush AP_fwritex_stderr AP_fprintf1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition fprintf_icp_entry : Z := 0x46914.
Definition FPRINTF_ICP_DEPTH : Z := 5664.    (* [comment removed for export] *)

End RC__1.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma tafr_spec : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x603000 <= lo -> mem_inv asegs m ->
  rw_cells asegs m A_INITED [C1 (Z_to_bv 8 1)] ->
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (fun ms' => exists t0' a1' m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5b0a0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros SK LO LO0 MI GINI PSTK PIMG. unfold A_INITED in GINI.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat SK.
  stepA. stepA. stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. cbv beta. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. if_false. (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -16) _ |- _ => release_frame H SK (bv_unsigned sp) end.
  apply evtA_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.

(* [comment removed for export] *)
Lemma printf_common_call :
  forall (P : acc -> Prop) (ra gp tp t0 t1 t2 s0 s1 ctx a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo A AQ SB : Z) (pre post : list Z) (c : Z) (NF : nat) (SA : Z) (zs : list Z) (NA : nat),
  let fmt := pre ++ 37 :: c :: post in
  Forall (fun x => 0 < x < 256 /\ x <> 37) pre -> Forall (fun x => 0 < x < 256 /\ x <> 37) post ->
  (c = 115 \/ c = 100 \/ c = 117) -> zlength fmt <= 63 ->
  bytes_at asegs m A (zb fmt ++ [Z_to_bv 8 0]) -> 0x10000 <= A /\ A + 64 <= 0x31000 ->
  bytes_at asegs m (shw_lo SB A) (repeat (Z_to_bv 8 0) NF) -> Z.of_nat NF = shw_hi SB A (zlength fmt + 1) - shw_lo SB A ->
  icp_globals asegs m SB -> SB = 0x7fff8000 -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 2320 -> q <= 2^47 - 16 -> mem_inv asegs m ->
  (AQ + 8 <= lo \/ q <= AQ) -> (0 < AQ /\ AQ + 8 < 2^47) ->
  (c = 115 -> rw_cells asegs m AQ [C8 (Z_to_bv 64 SA)]) ->
  (c = 115 -> bytes_at asegs m SA (zb zs ++ [Z_to_bv 8 0])) ->
  (c = 115 -> Forall (fun x => 0 < x < 256) zs) ->
  (c = 115 -> SB + 0x100000000000 <= SA /\ SA + zlength zs + 1 < 2^47 /\ zlength zs + 1 < 2^40) ->
  (c = 115 -> SA + zlength zs + 1 <= lo \/ q <= SA) ->
  (c = 115 -> bytes_at asegs m (shw_lo SB SA) (repeat (Z_to_bv 8 0) NA)) ->
  (c = 115 -> Z.of_nat NA = shw_hi SB SA (zlength zs + 1) - shw_lo SB SA) ->
  (forall a k, lo <= a -> a + Z.of_nat k <= q -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A (zlength fmt + 1) -> P (Z_to_bv 64 a, k)) ->
  (c = 115 -> P (Z_to_bv 64 AQ, 8%nat)) ->
  (c = 115 -> forall a k, SA <= a -> a + Z.of_nat k <= SA + zlength zs + 1 -> P (Z_to_bv 64 a, k)) ->
  (c = 115 -> forall a k, shw_lo SB SA <= a -> a + Z.of_nat k <= shw_hi SB SA (zlength zs + 1) -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (pcm_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 ctx (Z_to_bv 64 A) (Z_to_bv 64 AQ) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 printf_common_entry) fc None m (seg_rom asegs)).
Proof.
  intros until NA. cbv zeta. intros HPRE HPOST HC FL FMT HA FSH FSL G -> SK LOC LO QHI MI AQ1 AQ2 AQC STR RNG SAB SAD ASH NAL P1 P2 P3 P4 P5 P6.
  destruct (Z.eq_dec c 115) as [Hc|Hc].
  - eapply printf_common_spec with (pre := pre) (post := post) (c := c) (zs := zs) (SA := SA) (NA := NA) (NF := NF); eauto; try lia; first [exact (SAB Hc) | exact (SAD Hc) | exact (NAL Hc)].
  - (* [comment removed for export] *)
    eapply printf_common_spec with (pre := pre) (post := post) (c := c) (zs := []) (SA := 2^47 - 2) (NA := 8%nat) (NF := NF); eauto; try (intros X; exfalso; exact (Hc X)).
    all: first [ change (zlength (@nil Z)) with 0; lia | reflexivity | right; change (zlength (@nil Z)) with 0; lia ].
Qed.

(* [comment removed for export] *)
Lemma args_ok_eqaddr : forall Fp B1 B2 BS m lo sp (ap1 ap2 : Z) ws args,
  args_ok Fp B1 BS m lo sp ap1 ws args -> B1 = B2 -> ap1 = ap2 -> args_ok Fp B2 BS m lo sp ap2 ws args.
Proof. intros until args. intros H <- <-. exact H. Qed.

Section Walk.
Context {St : Type}.
Variable P : acc -> Prop.
Hypothesis PSTK : POL_STACK P.
Hypothesis PIMG : POL_IMG P.
Hypothesis PHSH : POL_HSH P.
Hypothesis PLSH : POL_LSH P.
Hypothesis PNUL : POL_NUL P.

Definition fprintf_icp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
  fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ stderr_wfile0 m'
    /\ ssp_cells m' canary
    /\ mjx m'.

Theorem fprintf_icp_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
         (A : Z) (pre post : list Z) (c : Z) (args : list parg) (ps : list (list Z)) (r lo : Z) (canary : word) (zs : list Z),
  let fmt := pre ++ 37 :: c :: post in
  let q := bv_unsigned sp in
  a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
  stderr_wfile m ->
  (* [comment removed for export] *)
  bytes_at asegs m A (zb fmt ++ [Z_to_bv 8 0]) ->
  Forall (fun x => 0 < x < 256 /\ x <> 37) pre -> Forall (fun x => 0 < x < 256 /\ x <> 37) post ->
  (c = 115 \/ c = 100 \/ c = 117) -> zlength fmt <= 63 -> 0x10000 <= A -> A + 64 <= 0x21000 -> pass1_ok (fmt ++ [0]) = true ->
  (* [comment removed for export] *)
  args_ok RSTDERR (q - 112 - 352) 80 m lo q (q - 112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
  printf_pieces (fmt ++ [0]) args = Some (ps, r) -> fp_calls (length (fmt ++ [0])) (fmt ++ [0]) args = [] -> sp_ok (length (fmt ++ [0])) (fmt ++ [0]) args ->
  (* [comment removed for export] *)
  (c = 115 -> bytes_at asegs m (bv_unsigned a2) (zb zs ++ [Z_to_bv 8 0]) /\ Forall (fun x => 0 < x < 256) zs
              /\ q <= bv_unsigned a2 /\ bv_unsigned a2 + zlength zs + 1 < A_STK_HI /\ zlength zs + 1 < 2^40) ->
  (* [comment removed for export] *)
  stk asegs m lo q -> A_CEIL <= lo -> lo <= q - FPRINTF_ICP_DEPTH -> q <= A_STK_HI ->
  ssp_cells m canary -> mem_inv asegs m -> frm0 fc -> mjx m ->
  implMA asegs P (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
    (fun _ bs ms' => fprintf_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 fprintf_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros until zs. cbv zeta. intros -> -> SF FMT HPRE HPOST HC FL HA0 HA1 P1 AOK PP FPC SPOK HS ST LOC LO SPTOP SSP MI FRM MJ.
  unfold FPRINTF_ICP_DEPTH, A_CEIL, A_STK_HI, VF_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
  pose proof (mjx_g _ MJ) as G. pose proof (mjx_g2 _ MJ) as G2.
  pose proof G as G'. icp_globals_open G'.
  pose proof (ig2_vfprintf asegs _ G2) as GRV. pose proof (ig2_cflags asegs _ G2) as GCF. pose proof (ig2_check_printf asegs _ G2) as GCP.
  set (QQ := fun (_ : unit) (bs : list Z * St) (ms' : machine_state) => fprintf_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms').
  unfold fprintf_icp_entry. apply implMA_from_evtA. hideH FMT.
  carve_frame 112%nat ST.
  do 15 stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -112) |- _ => rename H into SK1 end.
  stepA. name_sp sp (-112).
  lazymatch goal with E : bv_unsigned ?spv = bv_unsigned sp + -112 |- _ => rewrite <- E in SK1 end.
  callA (tafr_spec P); [ exact SK1 | lia | lia | assumption | exact GINI
        | intros a k H1 H2; apply PSTK; lia | exact PIMG | ].
  unname_sp. stepA. if_false. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into SK2 end.
  stepA. name_sp sp (-112).
  lazymatch goal with E : bv_unsigned ?spv = bv_unsigned sp + -112 |- _ => rewrite <- ?E in SK2 end.
  callA (tafr_spec P); [ exact SK2 | lia | lia | assumption | match goal with H : rw_cells asegs _ 714840 _ |- _ => exact H end
        | intros a k H1 H2; apply PSTK; lia | exact PIMG | ].
  unname_sp. stepA. if_false. (* [comment removed for export] *)
  (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. cbv beta. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. if_false. (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (mjx_rodata_window0 m A (zlength (pre ++ 37 :: c :: post) + 1) MJ HA0 ltac:(unfold zlength; rewrite length_app; cbn [length]; lia) ltac:(unfold zlength in *; lia)) as [[FSH FSL] _]. rewrite repeat_length in FSL.
  pose proof (shw_geom 0x7fff8000 A (zlength (pre ++ 37 :: c :: post) + 1) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as GF; cbv zeta in GF.
  assert (ASH : c = 115 -> exists NA, bytes_at asegs m (shw_lo 0x7fff8000 (bv_unsigned a2)) (repeat (Z_to_bv 8 0) NA)
                              /\ Z.of_nat NA = shw_hi 0x7fff8000 (bv_unsigned a2) (zlength zs + 1) - shw_lo 0x7fff8000 (bv_unsigned a2)).
  { intros Hc. destruct (HS Hc) as (STR & RNG & SLO & SHI & SLEN).
    pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite length_app, zb_length' in BB. cbn [length] in BB.
    assert (XCE : (A_CEIL <= bv_unsigned a2)%Z) by (unfold A_CEIL; lia). assert (XN : (1 <= zlength zs + 1)%Z) by (unfold zlength; lia). assert (XHI : (bv_unsigned a2 + (zlength zs + 1) <= A_STK_HI)%Z) by (unfold A_STK_HI; lia).
    destruct (mjx_stack_window m (bv_unsigned a2) (zlength zs + 1) MJ XCE XN XHI) as [[X L] _].
    eexists. split; [exact X | rewrite repeat_length in L; exact L]. }
  (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into SK3 end.
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -112) _ |- _ => rename H into FRM' end.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_] _)) in FRM'. destruct FRM' as [FRlo VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAC by lia.
  pose proof VAC as VAC2. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in VAC2. destruct VAC2 as [AQC _].
  stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (Gx : icp_globals asegs mx 0x7fff8000) by
      (unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
         A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL;
       repeat (split; [assumption|]); assumption);
    pose proof (bytes_at_transport asegs _ m mx _ _ FSH MU ltac:(cbn; rewrite ?repeat_length, ?Z2Nat.id by lia; lia)) as FSHx;
    unhideH FMT;
    pose proof (bytes_at_transport asegs _ m mx _ _ FMT MU ltac:(cbn; rewrite length_app, zb_length'; cbn [length]; unfold zlength in *; lia)) as FMTx;
    assert (STRx : c = 115 -> bytes_at asegs mx (bv_unsigned a2) (zb zs ++ [Z_to_bv 8 0]))
      by (intros Hc; destruct (HS Hc) as (STR & RNG & SLO & SHI & SLEN);
          eapply bytes_at_transport; [exact STR | exact MU | cbn; rewrite length_app, zb_length'; cbn [length]; unfold zlength in *; lia])
  end.
  (* [comment removed for export] *)
  assert (XNA : exists NA, c = 115 -> exists mx0 : unit,
            bytes_at asegs m (shw_lo 0x7fff8000 (bv_unsigned a2)) (repeat (Z_to_bv 8 0) NA)
            /\ Z.of_nat NA = shw_hi 0x7fff8000 (bv_unsigned a2) (zlength zs + 1) - shw_lo 0x7fff8000 (bv_unsigned a2)).
  { destruct (Z.eq_dec c 115) as [Hc|Hc].
    - destruct (ASH Hc) as (NA & X & L). exists NA. intros _. exists tt. exact (conj X L).
    - exists 0%nat. intros X. exfalso. exact (Hc X). }
  destruct XNA as [NA XNA].
  rewrite <- (Z_to_bv_bv_unsigned a2) in AQC.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  callA (printf_common_call P _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mx (bv_unsigned sp + -112) lo A (bv_unsigned sp + -48) 0x7fff8000 pre post c _ (bv_unsigned a2) zs NA);
   [ exact HPRE | exact HPOST | exact HC | exact FL | exact FMTx | lia | exact FSHx
   | rewrite <- FSL; unfold zlength; rewrite length_app; cbn [length]; lia
   | exact Gx | reflexivity | exact SK3 | unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | lia | lia | assumption
   | right; lia | lia
   | intros _; exact AQC
   | exact STRx
   | intros Hc; exact (proj1 (proj2 (HS Hc)))
   | intros Hc; destruct (HS Hc) as (STR & RNG & SLO & SHI & SLEN); pose proof (bytes_at_bound _ _ _ _ STR); lia
   | intros Hc; destruct (HS Hc) as (STR & RNG & SLO & SHI & SLEN); right; lia
   | intros Hc; destruct (XNA Hc) as (_ & X & L); eapply bytes_at_transport; [exact X | exact MU | cbn; rewrite repeat_length, L;
       destruct (HS Hc) as (STR & RNG & SLO & SHI & SLEN); pose proof (shw_geom 0x7fff8000 (bv_unsigned a2) (zlength zs + 1) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as GA; cbv zeta in GA; lia]
   | intros Hc; destruct (XNA Hc) as (_ & X & L); exact L
   | intros a k H1 H2; apply PSTK; lia
   | exact PIMG
   | intros a k H1 H2; apply PLSH; lia
   | intros _; apply PSTK; lia
   | intros Hc a k H1 H2; destruct (HS Hc) as (STR & RNG & SLO & SHI & SLEN); apply PSTK; lia
   | intros Hc a k H1 H2; destruct (HS Hc) as (STR & RNG & SLO & SHI & SLEN);
     assert (XCE : (A_CEIL <= bv_unsigned a2)%Z) by (unfold A_CEIL; lia); assert (XN : (1 <= zlength zs + 1)%Z) by (unfold zlength; lia); assert (XHI : (bv_unsigned a2 + (zlength zs + 1) <= A_STK_HI)%Z) by (unfold A_STK_HI; lia);
     pose proof (stack_window_span (bv_unsigned a2) (zlength zs + 1) XCE XN XHI) as (W1 & W2 & W3); pose proof A_HSH_LO_range as HLR; pose proof W2 as W2n; unfold A_HSH_HI in W2n, HLR;
     apply PHSH; lia
   | ]
  end.
  (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into SK4 end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    try clear AQC;
    pose proof (rw_cells_bytes_at' _ _ _ _ ltac:(lazymatch goal with V : rw_cells asegs mx (bv_unsigned sp + -48) [_;_;_;_;_;_] |- _ => exact V end)) as VAA;
    cbn [cells_bytes cbytes] in VAA;
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA;
    assert (MJx : mjx mx) by (eapply mjx_transport; [exact MJ | exact MU | exact WM |];
      unfold mjx_ok_iv, A_CEIL, A_STK_HI; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil);
    try clear FMTx; pose proof (bytes_at_transport asegs _ m mx _ _ FMT MU ltac:(cbn; rewrite length_app, zb_length'; cbn [length]; unfold zlength in *; lia)) as FMTx;
    assert (SFx : stderr_wfile mx) by (destruct SF as (fl & md & e & we & tl & FC & R); exists fl, md, e, we, tl; split; [| exact R];
      eapply rw_cells_transport; [exact FC | exact MU1 | exact WM | cbn; lia]);
    assert (SSPx : ssp_cells mx canary) by (destruct SSP as [Q1 Q2]; unfold ssp_cells, got_ssp, ssp_guard in *;
      split; (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM | cbn; lia]))
  end.
  apply evtA_done. name_sp sp (-112).
  lazymatch goal with E : bv_unsigned ?spv = bv_unsigned sp + -112 |- _ => rewrite <- ?E in SK4 end.
  pose proof (vfprintf_stderr_proof (St:=St) P PSTK PIMG PHSH PLSH PNUL (fwritex_stderr_proof P PSTK PIMG PHSH PLSH PNUL) (stdio_write_flush_proof P PSTK PIMG PNUL)) as VF.
  unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
  eapply implMA_post_evt.
  { eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := (pre ++ 37 :: c :: post) ++ [0]) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, A_STK_HI, zlength; cbn [length].
    all: try reflexivity. all: try lia.
    all: first [ exact SFx
               | unfold zb; rewrite map_app; exact FMTx
               | apply Forall_app; split; [apply Forall_app; split; [eapply Forall_impl; [|exact HPRE]; cbv beta; intros; lia
                                         | constructor; [lia|]; constructor; [lia|]; eapply Forall_impl; [|exact HPOST]; cbv beta; intros; lia]
                                         | constructor; [lia | constructor]]
               | rewrite length_app; cbn [length]; unfold zlength in *; lia
               | exact P1 | exact VAA
               | lazymatch goal with E : bv_unsigned ?spv = ?rhs |- args_ok _ _ _ _ _ ?spx _ _ _ =>
                   rewrite E; eapply args_ok_vf; [| | exact MU]; [eapply args_ok_eqaddr; [exact AOK | lia | lia] | lia] end
               | exact PP | exact FPC | exact SPOK | exact SK4 | exact SSPx | exact FRM | exact MJx
               | unfold zlength in *; lia
               | assumption ]. }
  cbv beta. intros [] [b4 st4] ms' PO. clear VF MU1. cbn [snd] in PO.
  unfold vfprintf_stderr_post in PO. rewrite ?unsigned_lit in PO by lia.
  destruct PO as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3 & MJ3).
  unname_sp.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  ret_pc_lit.
  (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  lazymatch goal with FRl : rw_cells _ ?mm (bv_unsigned sp + -112)%Z ?hd, VAC' : rw_cells _ ?mm (bv_unsigned sp + -48)%Z ?rest |- _ =>
    assert (FALL : rw_cells asegs mm (bv_unsigned sp + -112) (hd ++ rest));
    [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRl|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC' | lia]
    | clear FRl VAC' ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evtA_done. subst QQ. cbn [fst snd]. unfold fprintf_icp_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SF3|]. split; [exact SSP3 | exact MJ3].
Qed.
End Walk.
End RC__2.
