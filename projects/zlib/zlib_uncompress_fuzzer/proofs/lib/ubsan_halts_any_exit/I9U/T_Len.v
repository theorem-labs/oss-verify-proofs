(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_MatchL S_DistL S_LenL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_Dist T_DistL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require TBase.

Module T_LenL.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_LenL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_DistL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_LLOOP1_T : Z := 93844.
Definition L_LL1X_T : Z := 93972.
Definition L_LLOOP2_T : Z := 94088.
Definition L_LL2X_T : Z := 94236.
Definition L_LXLOOP_T : Z := 87344.
Definition L_LXBODY_T : Z := 90464.
Definition L_LVX_LL2_T : Z := 96204.

Definition KS_E1T : list positive := [2; 3; 4; 5; 9; 10; 11; 14; 16; 19; 20; 22; 23; 24; 25; 27; 28; 30; 31; 32]%positive.
Definition KS_E2T : list positive := [2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 25; 27; 28; 29; 30; 31]%positive.   (* the len loop writes s7 (24); 1.3.1's kept s8 stays key 25 *)
Definition KS_XLT : list positive := [2; 3; 4; 5; 8; 9; 10; 11; 12; 13; 15; 17; 19; 20; 21; 22; 23; 25; 28; 29; 30; 31; 32]%positive.
Ltac keptc_closeT ::= cbv [keptc KS_D1T KS_D2T KS_XDT KS_L1T KS_XST KS_E1T KS_E2T KS_XLT]; split_conj; try exact I; zreg.
Ltac keptc_chainT HK ::= cbv [keptc KS_D1T KS_D2T KS_XDT KS_L1T KS_XST KS_E1T KS_E2T KS_XLT] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].

Lemma l_loop1_t {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n la na lb lm c0 b0 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = la -> zget_l Rb l kT4 = lm -> zget_l Rb l kA5 = 1 -> zget_l Rb l kT2 = Z.land lm H ->
  zget_l Rb l kA4 = q + ci -> zget_l Rb l kT1 = q + ci -> zget_l Rb l kA6 = B -> zget_l Rb l kA1 = B ->
  zget_l Rb l kA7 = n - ci -> zget_l Rb l kT0 = 8 * (n - ci) -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kS9 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B <= 40 -> (ci = c0 \/ B <= 22) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb + -1 -> 1 <= lb -> lb <= 15 -> 2 ^ lb <= na -> tab_ok LENS rdL lb na = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na rdL ->
  (forall R' (H' : Z),
     zget R' kS9 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_E1T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_LL1_T (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kA4 = q + ci' -> zget R' kT1 = q + ci' -> zget R' kA6 = B' -> zget R' kA1 = B' ->
     zget R' kA7 = n - ci' -> zget R' kT0 = 8 * (n - ci') -> zget R' kA2 = n - ci' -> zget R' kS9 = H' ->
     zget R' kS4 = cellv (rdL (Z.land lm H')) -> zget R' kT3 = code_bits (rdL (Z.land lm H')) + 256 * code_val (rdL (Z.land lm H')) ->
     zget R' kT2 = code_bits (rdL (Z.land lm H')) ->
     ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 40 -> code_bits (rdL (Z.land lm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_E1T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL1X_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LLOOP1_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lm c0 b0 ci B H fin rdL Hh La3 Lt4 La5 Lt2 La4 Lt1 La6 La1 La7 Lt0 La2 Ls3
    HN Hc0 Hc1 Hc2 Hb0 HB HB40 HB22 HH1 HH2 HBc Hlm Hlb1 Hlb2 Hna TOK Hq1 Hn26 Hq2 Hla1 Hla2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_LLOOP1_T, L_LL1X_T, L_LVX_LL1_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l' H lb ltac:(lia)) as Ri0. rewrite <- Hlm in Ri0.
  set (i := Z.land lm H) in *.
  pose proof (tab_root_entry LENS rdL lb na i TOK Ri0) as (Hbits0 & _ & _ & _).
  pose proof (code_op_range (rdL i)) as Rop. pose proof (code_val_range (rdL i)) as Rval. pose proof (cellv_range (rdL i)) as Rcell.
  assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
  zstep Rfd.
  zsetreg (4 * i) ltac:(symmetry; apply shl_2).
  zstep Rfd.
  tcell Htab i.
  zstep Rfd.
  zsetreg (code_bits (rdL i) + 256 * code_val (rdL i)) ltac:(symmetry; apply cell_shr8).
  zstep Rfd.
  zsetreg (code_bits (rdL i)) ltac:(symmetry; apply bits_and255).
  destruct (Z_lt_dec B (code_bits (rdL i))) as [Hneed | Hok].
  2: { zbr Rfd true.
    subst i.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx ci B H) end; try zreg; try lia.
    keptc_closeT. }
  zbr Rfd false.
  assert (HB14 : B <= 14) by lia.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_closeT. }
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_l' H' lb ltac:(lia)) as Ri1. rewrite <- Hlm in Ri1.
  zstep Rfd.
  zsetreg (4 * Z.land lm H') ltac:(symmetry; apply shl_2).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zbool.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  zstep Rfd.
  tstep1 Rfd.
  zbr Rfd true.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IH Rx lx Mx MD T q n la na lb lm c0 b0 (ci + 1) (B + 8) H' fin rdL Hh) end;
    try zreg; try lia; try eassumption.
  intros R' ci' B' H'' G15 G7 G17 G12 G18 G6 G13 G20 G21 G29 G8 X0 X1 X2 X3 X4 X5 X6 X7 HK.
  eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainT HK.
Qed.

Lemma l_loop2_t {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n la na lb lo v m2 c1 b1 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = la -> zget_l Rb l kT5 = m2 -> zget_l Rb l kT2 = lb -> zget_l Rb l kT4 = v -> zget_l Rb l kA5 = 1 ->
  zget_l Rb l kS4 = v + Z.land H m2 / 2 ^ lb ->
  zget_l Rb l kT6 = q + ci -> zget_l Rb l kT1 = q + ci -> zget_l Rb l kS5 = B -> zget_l Rb l kS3 = lb - 8 * (ci - c1) ->
  zget_l Rb l kA2 = n - ci -> zget_l Rb l kS9 = H ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B <= 40 -> (ci = c1 \/ B <= 37) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (lb + lo) - 1 -> 1 <= lb -> lb <= 15 -> 1 <= lo -> lo <= 15 - lb -> 0 <= v -> v + 2 ^ lo <= na -> na <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdL (v + j))) = false /\ term_ok LENS (15 - lb) (rdL (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na rdL ->
  (forall R' (H' : Z),
     zget R' kS9 = H' -> 0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_E2T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_LL2_T (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kT6 = q + ci' -> zget R' kT1 = q + ci' -> zget R' kS5 = B' -> zget R' kS3 = lb - 8 * (ci' - c1) ->
     zget R' kA2 = n - ci' -> zget R' kS9 = H' ->
     zget R' kS4 = cellv (rdL (v + Z.land H' m2 / 2 ^ lb)) ->
     zget R' kS6 = code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) + 256 * code_val (rdL (v + Z.land H' m2 / 2 ^ lb)) ->
     zget R' kS7 = code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) + lb ->   (* the len loop keeps s7 (region map s7 -> s7) *)
     ci <= ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 40 -> lb + code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_E2T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL2X_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LLOOP2_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lo v m2 c1 b1 ci B H fin rdL Hh La3 Lt5 Lt2 Lt4 La5 Ls4
    Lt6 Lt1 Ls6 Ls1 La2 Ls3 HN Hc0 Hc1 Hc2 Hb0 HB HB40 HB37 HH1 HH2 HBc Hm2 Hlb1 Hlb2 Hlo1 Hlo2 Hv1 Hv2 Hna SUB
    Hq1 Hn26 Hq2 Hla1 Hla2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_LLOOP2_T, L_LL2X_T, L_LVX_LL2_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_15 lo ltac:(lia)) as HPlo.
  assert (HPm : 1 <= 2 ^ (lb + lo) <= 32768) by (apply pow2_15; lia).
  assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ lb < 2 ^ lo).
  { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. rewrite <- Hm2 in A.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
  pose proof (JR H) as Rj0.
  set (j0 := Z.land H m2 / 2 ^ lb) in *.
  destruct (SUB _ Rj0) as [_ TM0]. apply term_ok_LENS in TM0 as [Hbits0 _].
  pose proof (code_op_range (rdL (v + j0))) as Rop. pose proof (code_val_range (rdL (v + j0))) as Rval. pose proof (cellv_range (rdL (v + j0))) as Rcell.
  assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
  zstep Rfd.
  zsetreg (4 * (v + j0)) ltac:(symmetry; apply shl_2).
  zstep Rfd.
  tcell Htab (v + j0).
  zstep Rfd.
  zsetreg (code_bits (rdL (v + j0)) + 256 * code_val (rdL (v + j0))) ltac:(symmetry; apply cell_shr8).
  zstep Rfd.
  zsetreg (code_bits (rdL (v + j0))) ltac:(symmetry; apply bits_and255).
  zstep Rfd.
  destruct (Z_lt_dec B (code_bits (rdL (v + j0)) + lb)) as [Hneed | Hok].
  2: { zbr Rfd true.
    subst j0.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx ci B H) end; try zreg; try lia.
    keptc_closeT. }
  zbr Rfd false.
  assert (HB29 : B <= 29) by lia.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b1 + 8 * (n - c1)) with B by lia. lia.
    - keptc_closeT. }
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_r H' (lb + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  zstep Rfd.
  zsetreg (Z.land H' m2 / 2 ^ lb) ltac:(symmetry; apply srlw_small; lia).
  pose proof (JR H') as Rj1.
  zstep Rfd.
  zsetreg (v + Z.land H' m2 / 2 ^ lb) ltac:(lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (4 * (v + Z.land H' m2 / 2 ^ lb)) ltac:(symmetry; apply zext32_shift30; lia).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zstep Rfd.
  tstep1 Rfd.
  zbr Rfd true.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IH Rx lx Mx MD T q n la na lb lo v m2 c1 b1 (ci + 1) (B + 8) H' fin rdL Hh) end;
    try zreg; try lia; try eassumption.
  intros R' ci' B' H'' G32 G7 G23 G10 G13 G20 G21 G22 G24 X0 X1 X2 X3 X4 X5 X6 X7 HK.
  eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainT HK.
Qed.

Lemma x_loop_l {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n ext c0 b0 ci B H : Z) (fin : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA6 = ext -> zget_l Rb l kA2 = n - c0 -> zget_l Rb l kA4 = q + c0 -> zget_l Rb l kS3 = b0 ->
  zget_l Rb l kS7 = n - ci -> zget_l Rb l kA7 = q + ci -> zget_l Rb l kT0 = q + ci ->
  zget_l Rb l kA3 = B -> zget_l Rb l kA5 = B -> zget_l Rb l kS9 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < ext -> ext <= 15 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (forall R' (H' : Z),
     zget R' kS9 = H' -> zget R' kS7 = 0 -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_XLT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_XL_T (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS10 = q + ci' -> zget R' kT0 = q + ci' -> zget R' kS7 = n - ci' -> zget R' kA3 = B' -> zget R' kA5 = B' -> zget R' kS9 = H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> ext <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_XLT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LXBODY_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LXLOOP_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n ext c0 b0 ci B H fin Hh La6 La2 La4 Ls1 Ls7 La7 Lt0 La3 La5 Ls3
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hext HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  zkeys. unfold L_LXLOOP_T, L_LXBODY_T, L_LVX_XL_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_closeT. }
  zbr Rfd true.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd true.
  zstep Rfd.
  zbr Rfd true.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia).
  tstep1 Rfd.
  zstep Rfd.
  destruct (Z_lt_dec (B + 8) ext) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n ext c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin Hh) end;
      try zreg; try lia; try eassumption.
    intros R' ci' B' H'' G26 G6 G24 G14 G16 G20 X0 X1 X2 X3 X4 X5 X6 X7 HK.
    eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainT HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end;
      try zreg; try lia. keptc_closeT.
Qed.

Lemma st_rest_le {RCa1 : RunCtx}  : forall cx st M m len ex,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st len (t_offset st) ex) M -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_le st m len ex) M.
Proof. intros cx st M m len ex H. destruct cx, st. exact H. Qed.
End T_LenL.

Module T_LenX.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_LenL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.T_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.T_DistX OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.
Import T_LenL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_LXNB_T : Z := 87308.
Definition L_LEEC_T : Z := 94360.
Definition L_LEF8_T : Z := 94372.

Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS3 kS4 kS5 kS6 kS9 kS8 kS7 kS10 kS11 kS0 kT3 kT4 kT5 kT6] in H.
Ltac st_cbn_in H := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in H.
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- x_regs _ _ _ _ _ _ => close_xregs
  | |- keptc _ _ _ _ => keptc_closeT
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => first [assumption | lia]
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- mem_u32 _ _ _ _ => first [assumption | idtac]
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- _ => first [assumption | lia]
  end.

Theorem len_ef8_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf (m len bk : Z),
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> 1 <= len -> len < 65536 ->
  d_entry cx st Rb l -> zget_l Rb l kA3 = c_p cx + 7160 ->
  s_std cx fin M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) m -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st len (t_offset st) (t_extra st)) M ->
  s_ret cx st M -> s_lo cx st M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 7164) bk -> 0 <= bk -> bk <= 128 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEF8_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf m len bk CX Hh Hfin Hmd SI Hl1 Hl2 RG La3 STD Hm SREST SRET SLO BK Hbk1 Hbk2 Hlens Hcodes HP0 K.
  pose proof (sinv_to_dist cx st lf cf len SI Hmd Hl1 Hl2) as [SI1 ME1].
  pose proof (st_rest_le cx st M DIST len (t_extra st) SREST) as SR1. clear SREST.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode. unfold st_le in SI1, ME1, SR1. st_cbn_in SI1. st_cbn_in ME1. st_cbn_in SR1.
  unfold d_entry, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. destruct SLO as [LFT OUT]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_LEF8_T, L_DIST in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof SR1 as C92. unfold st_rest in C92. icx_cbn. dand C92 as (_ & _ & _ & _ & C92 & _).
  pose proof (proj1 SI1) as R. unfold RNG in R. icx_cbn. dand R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [RL1 RL2] & _).
  tstep1 Rfd.
  clear C92.
  zstep Rfd. zlit.
  clear Hm.
  tstep1 Rfd.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (dist_t _ fin MD T M0 Rx lx Mx
              (IST DIST last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold d_entry, s_vars; icx_cbn; zkeys; split_conj; zreg.
  - unfold k_mem, st_at, s_lo; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [DIST]; assumption | exact SR1 | exact SRET | exact HAG
               | eapply s_bk_intro; [eassumption | lia | cbn [t_mode]; cbv [DIST LENEXT]; lia | cbn [t_mode]; cbv [DIST LENEXT]; lia] ].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

Theorem len_eec_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf (bk : Z),
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS2 = c_u cx -> zget_l Rb l kRA = 16209 ->
  zget_l Rb l kA4 = c_q cx + t_cin st -> zget_l Rb l kA2 = c_n cx - t_cin st ->
  zget_l Rb l kS1 = c_ob cx + t_cout st -> zget_l Rb l kS9 = t_hold st -> zget_l Rb l kS3 = t_bits st ->
  s_std cx fin M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) LENEXT -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  s_ret cx st M -> s_lo cx st M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 7164) bk -> 0 <= bk -> bk <= 128 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEEC_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf bk CX Hh Hfin Hmd SI Lsp Lgp Ltp Ls11 Ls0 Lra La4 La2 Ls2 Ls3 Ls1
    STD Hm SREST SRET SLO BK Hbk1 Hbk2 Hlens Hcodes HP0 K.
  assert (HLE : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { dand SI as (_ & _ & _ & Mo). clear - Mo Hmd. unfold MODE in Mo.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  dand HLE as (HX15 & HL1 & HL32).
  pose proof CX as CX0. pose proof STD as STD0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  open_std STD. icx_cbn.
  zkeysb. unfold L_LEEC_T, L_LEF8_T in *. cbv [JTAB_ADDR] in *.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q56 & _).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_ef8_t _ fin MD T M0 Rx lx Mx
              (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf LENEXT length bk CX0 Hh Hfin eq_refl SI) end.
  - lia.
  - lia.
  - unfold d_entry, s_vars; icx_cbn; zkeys; split_conj; zreg.
  - icx_cbn. zreg.
  - exact STD0.
  - exact Hm.
  - unfold st_w3; icx_cbn. exact SREST.
  - exact SRET.
  - exact SLO.
  - icx_cbn. exact BK.
  - exact Hbk1.
  - exact Hbk2.
  - exact Hlens.
  - exact Hcodes.
  - exact HP0.
  - exact K.
Qed.

Theorem lenext_body_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf (bk : Z),
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> t_extra st <> 0 ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS2 = c_u cx -> zget_l Rb l kRA = 16209 ->
  zget_l Rb l kA4 = c_q cx + t_cin st -> zget_l Rb l kA2 = c_n cx - t_cin st ->
  zget_l Rb l kS1 = c_ob cx + t_cout st -> zget_l Rb l kS9 = t_hold st -> zget_l Rb l kS3 = t_bits st ->
  zget_l Rb l kA1 = t_extra st ->
  s_std cx fin M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) LENEXT -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  s_ret cx st M -> s_lo cx st M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 7164) bk -> 0 <= bk -> bk <= 64 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LXNB_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf bk CX Hh Hfin Hmd SI Hx1 Lsp Lgp Ltp Ls11 Ls0 Lra La4 La2 Ls2 Ls3 Ls1 La1
    STD Hm SREST SRET SLO BK Hbk1 Hbk2 Hlens Hcodes HP0 K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HLE : extra <= 15 /\ 1 <= length /\ length <= 32768)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : LENEXT = LENEXT -> _ |- _ => exact (H eq_refl) end).
  dand HLE as (HX15 & HL1 & HL32). clear MODE_.
  open_std STD. destruct SLO as [LFT OUT]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  prune_rng.
  zkeysb. unfold L_LXNB_T, L_LEF8_T, L_LXLOOP_T, L_LXBODY_T, L_LVX_XL_T, L_LEAVE_LD2 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KRD KRD1 KB0 KB5 KB5B KB1 KL KLL KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q56 & _).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  assert (JC0 : forall R' (ci H B : Z),
    x_regs u p ob K0 cout R' ->
    zget R' kS10 = q + ci -> zget R' kS7 = n - ci -> zget R' kA3 = B -> zget R' kS9 = H -> zget R' kA1 = extra ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 90464 (zupd R' []) M MD) T).
  { intros R' ci H B XR G26 G24 G14 G20 G12 Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    open_xregs XR. kcbv_in G26; kcbv_in G24; kcbv_in G14; kcbv_in G20; kcbv_in G12. clear KLL2.
    repeat match goal with H : forall i : Z, _ |- _ => lazymatch H with Hfin => fail | _ => clear H end end.
    pose proof SREST as C92. unfold st_rest in C92. icx_cbn. dand C92 as (_ & _ & _ & _ & C92 & _).
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    tstep1 Rfd.
    clear C92.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ extra - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (H / 2 ^ extra) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    zstep Rfd.
    st_prestore_k st_rest_set92 13%positive SREST.
    tstep1 Rfd.
    clear BK.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ extra) (B - extra) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (len_ef8_t _ fin MD T M0 Rx lx Mx
                (IST LENEXT last flags ci cout (H / 2 ^ extra) (B - extra) out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf LENEXT (length + Z.land H (2 ^ extra - 1)) (bk + extra) CX0 Hh Hfin eq_refl SI1) end.
    - lia.
    - lia.
    - unfold d_entry, s_vars; icx_cbn; zkeys; split_conj; zreg.
    - icx_cbn. zreg.
    - close_std.
    - icx_cbn. exact Hm.
    - unfold st_w3; icx_cbn. exact SREST.
    - exact SRET.
    - unfold s_lo; icx_cbn; split; assumption.
    - icx_cbn. assumption.
    - lia.
    - lia.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG.
    - eapply KALL_mono; [| exact K]. clear - ME1. lia. }
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop_l (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n extra cin bits cin bits hold fin Hh) end.
    all: jfin.
    +
      intros R' H' G20 G24 HH1 HH2 HB14 HBn KP. cbv [keptc KS_XLT] in KP. kcbv_in G20; kcbv_in G24. destr_conj KP. zimps.
      eapply (stub_X_t 96180 R' [] M MD T q n cin bits); [right; split; [reflexivity | zreg] | exact Hh | zreg | zreg | lia | lia | lia | lia | lia | lia |].
      intros R9 E26 E10 HK9. cbv [keptc KS_XST] in HK9. kcbv_in E26; kcbv_in E10. destr_conj HK9. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. st_cbn_in SI1.
      unfold KLEAVE_LD2 in KLL2.
      eapply (KLL2 R9 M _ lf cf SI1).
      * unfold s_regs_leave_ld2; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hm | exact SREST].
      * exact SRET.
      * unfold s_lo; icx_cbn; split; assumption.
      * eapply s_bk_intro; [exact BK | lia | cbn [t_mode]; cbv [DIST LENEXT]; lia | cbn [t_mode]; cbv [DIST LENEXT]; lia].
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' ci' B' H' G26 G6 G24 G14 G16 G20 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_XLT] in KP.
      kcbv_in G26; kcbv_in G6; kcbv_in G24; kcbv_in G14; kcbv_in G16; kcbv_in G20. destr_conj KP. zimps.
      eapply (JC0 R' ci' H' B'); try assumption; try lia. close_xregs.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JC0 Rx cin hold bits) end; try zreg; try lia.
    close_xregs.
Qed.

Theorem arm_LENEXT_t {RCa1 : RunCtx}  : arm_stmt L_LENEXT LENEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SBK as SBK0. dand SBK as (bk & BK & Rbk & Hbk64 & _). specialize (Hbk64 Hmd).
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & _). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  pose proof VARS as VARS0. unfold s_vars in VARS. destr_conj VARS.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { clear - Mo Hmd. unfold MODE in Mo. repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  assert (HX0 : 0 <= t_extra st) by (unfold RNG in R; destr_conj R; assumption). clear R Mo.
  zkeysb. unfold L_LENEXT, L_LXNB_T, L_LEEC_T in *.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  destruct (Z.eq_dec (t_extra st) 0) as [Hx0 | Hx1].
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_eec_t cx fin MD T M0 Rx lx M st lf cf bk CX Hh Hfin Hmd SI) end;
      try zreg; try assumption; try lia.
    all: first [rewrite <- Hmd; exact Hmode | exact SREST].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (lenext_body_t cx fin MD T M0 Rx lx M st lf cf bk CX Hh Hfin Hmd SI Hx1) end;
      try zreg; try assumption; try lia.
    all: first [rewrite <- Hmd; exact Hmode | exact SREST].
Qed.
End T_LenX.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_ClDefs.

Module T_LenF.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_ClDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.T_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_FRET : Z := 93660.
Definition L_LSLOW : Z := 93740.

Definition len_slow_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = LEN -> sinv cx st lf cf ->
    d_entry cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LSLOW (zupd Rb l) M MD) T.

Ltac st_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
Ltac modes_cbv := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_get Mo := clear - Mo; unfold MODE in Mo; icx_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption.
Ltac mode_vacuous := let HE := fresh "HE" in intros HE; exfalso;
  repeat match goal with H : _ |- _ => lazymatch H with HE => fail | _ => clear H end end;
  unfold codes_liveP in *; modes_cbv; lia_std.
Ltac prog_transfer P :=
  first [ exact P
        | let P1 := fresh in let P2 := fresh in let P3 := fresh in
          dand P as (P1 & P2 & P3); unfold PROG; icx_cbn; split; [exact P1 | split; [exact P2 |]];
          first [ exact P3
                | let E := fresh in let C := fresh in
                  destruct P3 as [E | [E C]];
                  first [ left; exact E
                        | right; split; [exact E | clear - C; modes_cbv; lia_std]
                        | exfalso; clear - C; modes_cbv; lia_std ] ] ].
Ltac prune_rng :=
  repeat match goal with
  | H : _ < 4294967296 |- _ => clear H | H : 0 <= _ < 18446744073709551616 |- _ => clear H | H : _ < 18446744073709551616 |- _ => clear H
  | H : - 2147483648 <= _ |- _ => clear H | H : _ < 2147483648 |- _ => clear H | H : - 2147483648 <= _ < 2147483648 |- _ => clear H
  end.


Lemma pow2_15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(lia_std) ltac:(lia_std)); lia_std | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia_std]. Qed.

Definition st_fast (st : ist) (m ci co H B : Z) : ist :=
  IST m (t_last st) (t_flags st) ci co H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_after_fast : forall cx st lf cf m ci co H B,
  sinv cx st lf cf -> t_mode st = LEN ->
  0 <= ci -> ci <= c_n cx -> t_cout st <= co -> co <= c_osz cx ->
  0 <= B -> B <= 7 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B + (c_osz cx - co) < 8 * (c_n cx - t_cin st) + t_bits st + (c_osz cx - t_cout st) ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (m = LEN \/ m = TYPE \/ m = BAD) ->
  sinv cx (st_fast st m ci co H B) lf cf /\ meas cx (st_fast st m ci co H B) < meas cx st.
Proof.
  intros cx st lf cf m ci co H B SI Hm Hci1 Hci2 Hco1 Hco2 HB1 HB2 HH1 HH2 HBc HW HI Hm'.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_fast, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  dand P as (P1 & P2 & P3). unfold PROG, Wm in P1, P2, P3 |- *. icx_cbn.
  split; [split; [| split; [exact W | split]] |].
  - clear W Mf Mlive P1 P2 P3. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - clear W Mf Mlive Hm'. split; [lia_std | split; [lia_std |]].
    first [ exact P3 | destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std] ].
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros HL; destruct Hm' as [-> | [-> | ->]];
              [ apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std ]
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
  - clear - HW Hm'. pose proof (rank_range m) as RR. change (rank LEN) with 18. lia_std.
Qed.

Lemma win_arr {RCa1 : RunCtx}  : forall M w, 0 < w \/ w = 0 -> w + 32768 <= two64 -> (w <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M w 32768) ->
  exists fw, (w <> 0 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M w 32768 fw) /\ (forall i, 0 <= i < 32768 -> 0 <= fw i < 256).
Proof.
  intros M w Hw Hw2 Ww. destruct (Z.eq_dec w 0) as [E|NE].
  - exists (fun _ => 0). split; [intros C; contradiction | intros; lia_std].
  - destruct (out_arr_t M w 32768 (Ww NE) ltac:(lia_std) ltac:(lia_std) Hw2) as (fw & A & B).
    exists fw. split; [intros _; exact A | exact B].
Qed.

Section LenF.
Context {RCa1 : RunCtx}.
Hypothesis IFAST : ifast_spec_t.
Hypothesis LEN_SLOW : len_slow_stmt.

Theorem len_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  d_entry cx st Rb l -> zget_l Rb l kA3 = c_u cx -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEN (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG RA3 KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_).
  pose proof KM as KM0. pose proof RG as RG0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV MODE_ PROG_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold d_entry, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  destruct SLO as [LFT OUT]. icx_cbn.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) dc) as da eqn:Eda.
  remember (rdc cf lc) as rdL eqn:ErdL. remember (rdc cf dc) as rdD eqn:ErdD. clear ErdL ErdD.
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _). pose proof (tab_ok_root _ _ _ _ TOKD) as (Hdb1 & Hnd1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_15 db ltac:(lia)) as HPdb.
  prune_rng.
  zkeysb. unfold L_LEN, L_LSLOW, L_FRET, L_DISP, L_IFAST in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zstep Rfd.
  destruct (Z_lt_dec (n - cin) 6) as [Hh6 | Hh6].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (LEN_SLOW _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold d_entry, s_vars; icx_cbn; zkeys; split_conj; zreg. }
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  destruct (Z_lt_dec (osz - cout) 258) as [Hl258 | Hl258].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (LEN_SLOW _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold d_entry, s_vars; icx_cbn; zkeys; split_conj; zreg. }
  zbr Rfd false.
  (* the fast path also needs bits < 8 (li a1,7; bltu a1,s3 -> the slow path), as plain S_LenF *)
  zstep Rfd.                          (* li a1,7 *)
  destruct (Z_lt_dec 7 bits) as [Hb8 | Hb8].
  { zbr Rfd true.                     (* bits >= 8: the slow path *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (LEN_SLOW _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold d_entry, s_vars; icx_cbn; zkeys; split_conj; zreg. }
  zbr Rfd false.
  clear KM0 RG0.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KRD KRD1 KB0 KB5 KB5B KB1 KL KLL KLL2 KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C136 & _ & _ & _ & _ & C80 & _ & C56 & _).
  pose proof CST as CS. unfold i_cst in CS. icx_cbn. dand CS as (S64u & _ & _ & _ & _ & _ & C60 & C72 & C7144).
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136b & C140 & C144).
  rewrite <- Ela in C104. rewrite <- Eda in C112. clear SREST.
  clear LFT.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (out_arr_t Mx ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo);
    destruct (win_arr Mx w ltac:(lia) ltac:(rewrite TW64; lia) ltac:(intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X; exact X)) as (fw & Hwin & Rfw) end.
  pose proof WIN_ as WIN'. unfold WIN in WIN'. icx_cbn. cbv [WIN_SIZE] in WIN'. destruct WIN' as [WIN0 WIN1].
  unfold ifast_spec_t, ifast_spec_at in IFAST.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IFAST Rx lx Mx MD T u p q n ob osz w whave wnext cin cout hold bits out lb db la na da nd (u + -256) 93660 139264 zc rdL rdD fin fo fw Hh) end.
  all: first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- ZSEP _ => first [ assumption | exact (sep_ob_u _ _ SEP) | exact (sep_p_ob _ _ SEP) | exact (sep_p_q _ _ SEP) | exact (sep_ob_q _ _ SEP)
                            | exact (sep_w_p _ _ SEP) | exact (sep_w_q _ _ SEP) | exact (sep_w_ob _ _ SEP) ]
       | |- tab_ok _ _ _ _ = true => assumption
       | |- _ mod _ = _ => first [ assumption | exact (proj1 AL) | exact (proj1 (proj2 AL))
                                 | pose proof (proj1 AL) as ALu; clear - ALu; cbn in ALu; Z.to_euclidean_division_equations; lia ]
       | |- _ \/ _ => destruct (Z.eq_dec w 0) as [Ew|Nw]; [left; exact Ew | right; split; [lia | split; [cbv [WIN_SIZE ]; lia | exact (proj2 (proj2 AL))]]]
       | |- _ -> mem_wr _ _ _ _ => intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X |- *; exact X
       | |- _ -> mem_arr _ _ _ _ _ _ => exact Hwin
       | |- _ -> _ /\ _ => first [exact WIN0 | cbv [WIN_SIZE]; exact WIN1]
       | |- mem_wr _ _ _ _ => first [assumption | exact Wstk]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => assumption
       | |- mem_u32 _ _ _ _ => first [assumption | exact C60 | cbv [LEN]; assumption]
       | |- forall i : Z, _ => first [exact Hfin | exact Rfo | exact Rfw]
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE WIN_SIZE FR_IF FR_INF]; first [assumption | lia]
       end | match goal with |- ?G => idtac "IFAIL" G end ].
  intros R' M' cin' cout' hold' bits' mode' fo' Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3 HWlt HIle Hm' HP E8 E16 E32 E40 P80 P88 P8 HOB' Rfo' KE.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hmode HOB Hwin C60 C72 C7144 S64u HtL HtD.
  repeat match goal with
         | H : mem_u64 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u64 _ _ (u) _ => clear H | mem_u64 _ _ (u + 24) _ => clear H | mem_u64 _ _ (p + 96) _ => clear H end end
         | H : mem_u32 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u32 _ _ (u + 8) _ => clear H | mem_u32 _ _ (u + 32) _ => clear H | mem_u32 _ _ (p + 104) _ => clear H end end
         end.
  unfold if_fp in HP. cbv [FR_IF] in HP. zreattachL HP.
  assert (Hmv : 0 <= mode' < 2147483648) by (clear - Hm'; cbv [LEN TYPE BAD] in Hm'; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  zstep Rfd.
  unfold KDISP in KD. zkeys.
  assert (JD : forall R9 M9 (m9 : Z),
    (m9 = LEN \/ m9 = TYPE \/ m9 = BAD) -> m9 = mode' \/ (m9 = TYPE /\ mode' = TYPE) ->
    zget R9 3 = u + -256 -> zget R9 4 = K0 4%positive -> zget R9 5 = K0 5%positive -> zget R9 9 = p ->
    zget R9 14 = u -> zget R9 19 = u -> zget R9 12 = 0 -> zget R9 2 = 16209 ->
    zget R9 27 = q + cin' -> zget R9 24 = n - cin' -> zget R9 10 = ob + cout' -> zget R9 26 = hold' -> zget R9 20 = bits' ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M9 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (p + 8) m9 ->
    st_rest (run_segments R_segs rc_inp rc_sp rc_mb) (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (u + -144) (osz - cout') -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (u + -168) out ->
    s_bk (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST m9 last flags cin' cout' hold' bits' out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (p + 168) 320 lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (p + 1384) 1444 cf ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M9 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 87064 (zupd R9 []) M9 MD) T).
  { intros R9 M9 m9 Hm9 _ G3 G4 G5 G28 G14 G9 G12 G2 G26 G24 G19 G20 G10 STD9 Hmo9 SR9 RET9 LFT9 OUT9 SBK9 HL9 HC9 HAG9.
    pose proof (sinv_after_fast _ _ lf cf m9 cin' cout' hold' bits' SI0 eq_refl Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3
                  ltac:(cbn; lia) ltac:(cbn; lia) Hm9) as [SI9 ME9].
    unfold st_fast in SI9, ME9. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI9, ME9.
    eapply (KD R9 M9 _ lf cf SI9 ME9).
    - unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; split_conj; assumption.
    - unfold k_mem, st_at, s_lo; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption. all: first [exact SR9 | exact RET9 | exact SBK9]. }
  pose proof Hm' as Hm''. cbv [LEN TYPE BAD] in Hm''.
  destruct (Z.eq_dec mode' TYPE) as [HmT | HmT]; cbv [TYPE] in HmT.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JD Rx Mx mode' Hm' ltac:(left; reflexivity)) end.
    all: try zreg.
    all: first [ close_std | assumption
               | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]
               | unfold s_ret in *; icx_cbn; assumption
               | sbk ].
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JD Rx Mx mode' Hm' ltac:(left; reflexivity)) end.
    all: try zreg.
    all: first [ close_std | assumption
               | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]
               | unfold s_ret in *; icx_cbn; assumption
               | sbk ].
Qed.

Theorem arm_LEN_t : arm_stmt L_LEN LEN.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  dand RG as (FIX & VARS & _). pose proof FIX as FIX'. unfold s_fix in FIX'.
  dand FIX' as (Gsp & Ggp & Gtp & Gs11 & Ga3 & Gs0 & Ga1 & Gra).
  eapply len_t; try eassumption. unfold d_entry. split_conj; assumption.
Qed.

Definition st_mode (st : ist) (m : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_len_ : forall cx st lf cf,
  sinv cx st lf cf -> t_mode st = LEN_ ->
  sinv cx (st_mode st LEN) lf cf /\ meas cx (st_mode st LEN) < meas cx st.
Proof.
  intros cx st lf cf SI Hm.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_mode, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN_ = HEAD \/ LEN_ = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN_ -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  split; [split; [exact R | split; [exact W | split; [prog_transfer P|]]] |].
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Theorem lenu_t : lenu_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof (sinv_len_ cx st lf cf SI Hmd) as [SI1 ME1].
  open_kmem KM. destruct SAT as [Hmode SREST].
  dand RG as (FIX & VARS).
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_fix, s_vars in FIX, VARS. icx_cbn. destr_conj FIX. destr_conj VARS.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold st_mode in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
  zkeysb. unfold L_LEN_, L_LEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  clear Hmode.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_t _ fin MD T M0 Rx lx Mx
              (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold d_entry, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LEN]; assumption | exact SREST | exact SRET | exact SLO | exact HAG | sbk].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

Theorem arm_LEN__t : arm_stmt L_LEN_ LEN_.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply lenu_t; try eassumption. dand RG as (A & B & _). split; [exact A | exact B].
Qed.
End LenF.
End T_LenF.

Module T_LenT.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_LenL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.T_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.T_DistX OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist T_LenL T_LenX.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_LTAIL_T : Z := 94268.
Definition L_LLIT_T : Z := 95556.
Definition L_LTYPE_T : Z := 95576.
Definition L_LBADC_T : Z := 95600.

Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS3 kS4 kS5 kS6 kS9 kS8 kS7 kS10 kS11 kS0 kT3 kT4 kT5 kT6] in H.
Ltac st_cbn_in H := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in H.

Lemma bits_and63 : forall e, code_bits e < 64 -> Z.land (code_bits e + 256 * code_val e) 63 = code_bits e.
Proof.
  intros e Hb. pose proof (code_bits_range e). pose proof (code_val_range e).
  replace (code_bits e + 256 * code_val e) with (code_bits e + code_val e * 2 ^ 8) by (change (2 ^ 8) with 256; lia).
  rewrite land_add_high by (try lia; change (2 ^ 8) with 256; lia).
  change 63 with (2 ^ 6 - 1). apply land_ones_id; [lia | change (2 ^ 6) with 64; lia].
Qed.

Definition t_regs (cx : ictx) (st : ist) (ci B H e bk0 : Z) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kS2 = c_u cx /\ zget_l Rb l kRA = 16209 /\
  zget_l Rb l kS1 = c_ob cx + t_cout st /\
  zget_l Rb l kT4 = code_op e /\ zget_l Rb l kT3 = code_bits e + 256 * code_val e /\ zget_l Rb l kS4 = cellv e /\
  zget_l Rb l kA4 = c_q cx + ci /\ zget_l Rb l kA1 = B /\ zget_l Rb l kT2 = bk0 /\
  zget_l Rb l kA2 = c_n cx - ci /\ zget_l Rb l kS9 = H.

Theorem len_tail_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf (ci B H e bk0 : Z),
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  t_regs cx st ci B H e bk0 Rb l ->
  1 <= code_bits e ->
  ((code_op e = 0 /\ code_val e < 256)
   \/ (16 <= code_op e < 32 /\ 3 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 258 /\ code_op e <= 21)
   \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0)) ->
  0 <= bk0 -> bk0 <= 15 ->
  t_cin st <= ci -> ci <= c_n cx -> code_bits e <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  PM cx fin M0 LEN st lf cf M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 7164) bk0 ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LTAIL_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf ci B H e bk0 CX Hh Hfin Hmd SI RG Hbe CLS Hk1 Hk2 Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm HPM BK K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_ MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold t_regs in RG; icx_cbn; destr_conj RG.
  dand HPM as (STD & Hmode & SREST & SRET & SLO & Hlens & Hcodes & HP0). icx_cbn.
  open_std STD. destruct SLO as [LFT OUT]. icx_cbn.
  prune_rng.
  zkeysb. unfold L_LTAIL_T, L_LLIT_T, L_LTYPE_T, L_LBADC_T, L_LXNB_T, L_LEEC_T, L_REDISP, L_BADMSG_A5, L_BADMSG_A5B in *.
  cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KRD1 KB0 KB1 KL KLL KLL2 KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & _ & _ & Q56 & _).
  pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
  pose proof (cellv_range e) as Rcell.
  assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
  zstep Rfd.
  zsetreg 0 ltac:(symmetry; apply bits_and192; lia).
  zbr Rfd false.
  zstep Rfd.
  zsetreg (code_val e) ltac:(symmetry; apply cell_shr16).
  zstep Rfd.
  zsetreg (code_bits e) ltac:(symmetry; apply bits_and63; lia).
  zstep Rfd.
  zsetreg (H / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold_cell H B); lia).
  pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  clear BK.
  tstep1 Rfd.
  st_prestore st_rest_set92 (code_val e) SREST.
  tstep1 Rfd.
  pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
  unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
  unfold KREDISP in KRD. unfold KBADMSG_A5 in KB5. unfold KBADMSG_A5B in KB5B. zkeys.
  destruct CLS as [[Hop0 Hv256] | [(Hop16 & Hv3 & Hv258 & Hop21) | [H64 H16]]].
  -
    zbr Rfd true.
    zstep Rfd. zlit.
    clear Hmode.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_len_set _ _ lf cf LIT (code_val e) SI1 eq_refl ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
    unfold st_le in SI2. st_cbn_in SI2.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KRD Rx Mx (IST LIT last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                            lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI2) end.
    + clear - ME1. unfold meas, Wm in *. icx_cbn. change (rank LIT) with 13 in *. change (rank LEN) with 18 in *. lia.
    + unfold s_regs_redisp; icx_cbn; zkeys; split_conj; zreg.
    + unfold k_mem, st_at, s_lo; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [LIT]; assumption | exact SREST | exact SRET | exact HAG | sbk].
  -
    pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    rewrite shiftl_1_pow in Hv258 by lia. pose proof (pow2_15 (code_op e - 16) ltac:(lia)) as HPx.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zsetreg (code_op e + -16) ltac:(lia).
    zstep Rfd. zlit.
    st_prestore_k st_rest_set100 12%positive SREST.
    tstep1 Rfd.
    clear Hmode.
    tstep1 Rfd.
    pose proof (sinv_to_lenext _ _ lf cf (code_val e) (code_op e + -16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
    unfold st_le in SI2, ME2. st_cbn_in SI2. st_cbn_in ME2.
    destruct (Z.eq_dec (code_op e + -16) 0) as [Hx0 | Hx1].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (len_eec_t _ fin MD T M0 Rx lx Mx
                  (IST LENEXT last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e + -16)
                       lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf (bk0 + code_bits e) CX0 Hh Hfin eq_refl SI2) end;
        try zreg; try lia.
      all: first [ close_std | cbv [LENEXT]; assumption | exact SREST | exact SRET
                 | unfold s_lo; icx_cbn; split; assumption | exact Hlens | exact Hcodes | exact HAG
                 | eapply KALL_mono; [| exact K]; clear - ME1 ME2; lia | icx_cbn; assumption ].
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (lenext_body_t _ fin MD T M0 Rx lx Mx
                  (IST LENEXT last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e + -16)
                       lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf (bk0 + code_bits e) CX0 Hh Hfin eq_refl SI2) end;
        try zreg; try lia.
      all: first [ icx_cbn; exact Hx1 | close_std | cbv [LENEXT]; assumption | exact SREST | exact SRET
                 | unfold s_lo; icx_cbn; split; assumption | exact Hlens | exact Hcodes | exact HAG
                 | eapply KALL_mono; [| exact K]; clear - ME1 ME2; lia | icx_cbn; assumption ].
  -
    assert (Tnz : code_op e <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
    pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64. pose proof (land_range_r (code_op e) 32 ltac:(lia)) as R32.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_len_set _ _ lf cf LEN (code_val e) SI1 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
    unfold st_le in SI2. st_cbn_in SI2.
    destruct (Z.eq_dec (Z.land (code_op e) 32) 0) as [H32 | H32].
    +
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KB5 Rx Mx (IST LEN last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                            lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
      * apply (sinv_bad_of _ _ _ _ SI2).
      * pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                      (IST LEN last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                           lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
        clear - MB ME1. unfold bad_of, SBase.bad_of, meas, Wm in *. icx_cbn. change (rank LEN) with 18 in *. change (rank BAD) with 0 in *. lia.
      * unfold s_fix; icx_cbn; zkeys; split_conj; zreg.
      * zreg. * zreg. * zreg. * zreg. * zreg.
      * cbv [kA5]. lazymatch goal with |- 0 <= ?x < _ => replace x with 66608 by (symmetry; zreg) end. rewrite TW64. lia.
      * unfold k_mem, st_at, s_lo; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [exact SREST | exact SRET | exact HAG | sbk].
    +
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd. zlit.
      clear Hmode.
      tstep1 Rfd.
      zstep Rfd.
      repeat match goal with Hd : mem_u32 _ _ (p + 7164) _ |- _ => clear Hd end.
      tstep1 Rfd.
      zstep Rfd.
      pose proof (sinv_len_set _ _ lf cf TYPE (code_val e) SI1 eq_refl ltac:(right; right; reflexivity) ltac:(lia) ltac:(lia)) as SI3.
      unfold st_le in SI3. st_cbn_in SI3.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KB5B Rx Mx (IST TYPE last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                             lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI3) end.
      * clear - HWm Hbe. unfold meas, Wm. icx_cbn. change (rank TYPE) with 24. change (rank LEN) with 18. lia.
      * unfold s_fix; icx_cbn; zkeys; split_conj; zreg.
      * zreg. * zreg. * zreg. * zreg. * zreg.
      * unfold k_mem, st_at, s_lo; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [cbv [TYPE]; assumption | exact SREST | exact SRET | exact HAG | sbk].
Qed.
End T_LenT.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S Require Import S_MatchL S_DistL S_LenL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_Dist. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.T_MatchL. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import T_DistL. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_Dist. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Dist.T_DistX. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import T_Dist. Import T_LenL. Import T_LenX. Import T_LenF.
Import T_LenT.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS3 kS4 kS5 kS6 kS9 kS8 kS7 kS10 kS11 kS0 kT3 kT4 kT5 kT6] in H.
Ltac st_cbn_in H := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in H.
Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
Ltac gcbn := cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K
                  t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                  t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => gcbn; zreg
  | |- x_regs _ _ _ _ _ _ => close_xregs
  | |- t_regs _ _ _ _ _ _ _ _ _ => unfold t_regs; gcbn;
       cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7 kS1 kS3 kS4 kS5 kS6 kS9 kS8 kS7 kS10 kS11 kS0 kT3 kT4 kT5 kT6];
       split_conj; zreg
  | |- keptc _ _ _ _ => keptc_closeT
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => first [assumption | lia]
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- mem_u32 _ _ _ _ => gcbn; first [assumption | idtac]
  | |- PM _ _ _ _ _ _ _ _ => first [assumption | idtac]
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- ctx_ok _ _ => assumption
  | |- sinv _ _ _ _ => assumption
  | |- KALL _ _ _ _ _ _ => assumption
  | |- _ => gcbn; first [assumption | lia]
  end.

Ltac zbool0 := zsetreg 0 ltac:(rewrite ?mod_small_u64 by zlia;
  lazymatch goal with |- 0 = Z.b2z ?b' => replace b' with false; [reflexivity | symmetry; first [apply Z.ltb_ge; zlia | apply Z.eqb_neq; zlia]] end).
Ltac zbool1 := zsetreg 1 ltac:(rewrite ?mod_small_u64 by zlia;
  lazymatch goal with |- 1 = Z.b2z ?b' => replace b' with true; [reflexivity | symmetry; first [apply Z.ltb_lt; zlia | apply Z.eqb_eq; zlia]] end).

Definition ZHID (P : Prop) : Prop := P.
Ltac zhide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (ZHID (A \/ B)) in H end.
Ltac zunhide_disj := repeat match goal with H : ZHID ?T |- _ => change T in H end.

Theorem len_slow_t {RCa1 : RunCtx}  : len_slow_stmt.
Proof.
  unfold len_slow_stmt. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  pose proof KM as KM0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode. clear MODE_.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold d_entry, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. destruct SLO as [LFT OUT]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof SBK as SBK0. dand SBK as (bk & BK & Rbk & _ & _). icx_cbn.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  clear HtD TOKD Cda1 Cda2 Cnd ALda Sdaob Sdap Sdap2.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (rdc cf lc) as rdL eqn:ErdL. clear ErdL.
  prune_rng.
  zkeysb. unfold L_LSLOW, L_LTAIL_T, L_LLOOP1_T, L_LL1X_T, L_LLOOP2_T, L_LL2X_T, L_LVX_LL1_T, L_LVX_LL2_T,
    L_LEAVE, L_LEAVE_LD2 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KRD KRD1 KB0 KB5 KB5B KB1 KLL KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & _ & _ & Q56 & _).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _).
  rewrite <- Ela in C104. clear Ela.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  clear BK SBK0.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => rename Mx into M1 end.
  match goal with Hb : mem_u32 _ M1 (p + 7164) 0 |- _ => rename Hb into BK0 end.
  assert (HPM1 : PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 LEN
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf M1)
    by (unfold PM, s_lo; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; exact HAG).
  assert (KX1 : forall R' (H' : Z),
    zget R' kS9 = H' -> 0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    x_regs u p ob K0 cout R' -> zget R' kT5 = Z.shiftl (n - cin) 32 -> zget R' kS7 = n - cin -> zget R' kS10 = q + cin -> zget R' kS3 = bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96020 (zupd R' []) M1 MD) T).
  { intros R' H' G20 HH1 HH2 HB14 HBn XR G31 G24 G26 G10. open_xregs XR. kcbv_in G20; kcbv_in G31; kcbv_in G24; kcbv_in G26; kcbv_in G10.
    clear KLL2.
    pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn.
    eapply (stub_L1_t 96020 R' [] M1 MD T q n cin bits u ret);
      [right; split; [reflexivity | zreg] | exact Hh | zreg | zreg | zreg | zreg | zreg | lia | lia | lia | lia | lia | lia | lia | lia | exact SRET' | exact Q136 |].
    intros R9 E26 E24 E10 E27 E14 E12 KP. cbv [keptc KS_L1T] in KP. kcbv_in E26; kcbv_in E24; kcbv_in E10; kcbv_in E27; kcbv_in E14; kcbv_in E12.
    destr_conj KP. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. st_cbn_in SI1.
    unfold KLEAVE in KL.
    eapply (KL R9 M1 _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - unfold s_lo; icx_cbn; split; assumption.
    - eapply s_bk_intro; [exact BK0 | lia | cbn [t_mode]; cbv [LEN LENEXT]; lia | cbn [t_mode]; cbv [LEN DIST]; lia].
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  assert (JL1 : forall R' (ci B H : Z),
    x_regs u p ob K0 cout R' -> zget R' kA3 = la -> zget R' kT4 = 2 ^ lb + -1 -> zget R' kA5 = 1 ->
    zget R' kA4 = q + ci -> zget R' kT1 = q + ci -> zget R' kA6 = B -> zget R' kA1 = B ->
    zget R' kA7 = n - ci -> zget R' kT0 = 8 * (n - ci) -> zget R' kA2 = n - ci -> zget R' kS9 = H ->
    zget R' kS4 = cellv (rdL (Z.land (2 ^ lb + -1) H)) ->
    zget R' kT3 = code_bits (rdL (Z.land (2 ^ lb + -1) H)) + 256 * code_val (rdL (Z.land (2 ^ lb + -1) H)) ->
    zget R' kT2 = code_bits (rdL (Z.land (2 ^ lb + -1) H)) ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> B <= 40 -> code_bits (rdL (Z.land (2 ^ lb + -1) H)) <= B ->
    0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 93972 (zupd R' []) M1 MD) T).
  { intros R' ci B H XR G14 G30 G16 G15 G7 G17 G12 G18 G6 G13 G20 G21 G29 G8 Hc1 Hc2 HB HB40 HbB HH1 HH2 HBc.
    open_xregs XR. kcbv_in G14; kcbv_in G30; kcbv_in G16; kcbv_in G15; kcbv_in G7; kcbv_in G17; kcbv_in G12; kcbv_in G18;
    kcbv_in G6; kcbv_in G13; kcbv_in G20; kcbv_in G21; kcbv_in G29; kcbv_in G8.
    clear KX1 KL.
    set (i := Z.land (2 ^ lb + -1) H) in *.
    pose proof (land_mask_l' H lb ltac:(lia)) as Ri. fold i in Ri.
    pose proof (tab_root_entry LENS rdL lb na i TOKL Ri) as (Hbits & _ & _ & CASES).
    pose proof (code_op_range (rdL i)) as Rop. pose proof (code_val_range (rdL i)) as Rval. pose proof (cellv_range (rdL i)) as Rcell.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zsetreg (code_op (rdL i)) ltac:(symmetry; apply cell_and255).
    zstep Rfd.
    zstep Rfd.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      apply term_ok_LENS in TM as [Hb1 CLS].
      apply is_linkop_false in NL.
      assert (Hterm : code_op (rdL i) = 0 \/ 16 <= code_op (rdL i)).
      { destruct CLS as [(A & _) | [(A & _) | (A64 & _)]]; [lia | lia |].
        pose proof (land_range_r (code_op (rdL i)) 64 ltac:(lia)).
        destruct (Z.eq_dec (code_op (rdL i)) 0) as [E|E]; [left; exact E|]. right.
        destruct (Z_lt_dec (code_op (rdL i)) 16); [|lia]. exfalso. apply NL. lia. }
      destruct Hterm as [E | E];
        [ assert (Hbr : (code_op (rdL i) + -1) mod 18446744073709551616 = 18446744073709551615) by (rewrite E; reflexivity)
        | idtac ];
        zbr Rfd true;
        zstep Rfd;
        zstep Rfd;
        subst i;
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (len_tail_t _ fin MD T M0 Rx lx Mx
                    (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf ci B H (rdL (Z.land (2 ^ lb + -1) H)) 0 CX0 Hh Hfin eq_refl SI0) end;
        jfin.
    -
      rewrite L2 in G29, G8, HbB.
      pose proof (op_link_tests (code_op (rdL i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (lb + code_op (rdL i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdL i)) ltac:(lia)) as HPlo.
      zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      zsetreg 0 ltac:(symmetry; apply cell_and_e000; lia).
      zbr Rfd false.
      zstep Rfd.
      zsetreg (code_op (rdL i)) ltac:(symmetry; apply cell_and255).
      zstep Rfd.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (code_val (rdL i)) ltac:(symmetry; apply cell_shr16).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zsetreg (2 ^ (lb + code_op (rdL i)) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
      set (m2 := 2 ^ (lb + code_op (rdL i)) - 1) in *.
      set (v := code_val (rdL i)) in *. set (lo := code_op (rdL i)) in *.
      assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ lb < 2 ^ lo).
      { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. fold m2 in A.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      zstep Rfd.
      pose proof (land_mask_r H (lb + lo) ltac:(lia)) as Rm. fold m2 in Rm.
      zstep Rfd.
      zsetreg (Z.land H m2 / 2 ^ lb) ltac:(symmetry; apply srlw_small; lia).
      pose proof (JR H) as Rj.
      zstep Rfd.
      zsetreg (v + Z.land H m2 / 2 ^ lb) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zsetreg (4 * (v + Z.land H m2 / 2 ^ lb)) ltac:(symmetry; apply zext32_shift30; lia).
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd. zbool0.
      zstep Rfd. zlit.
      zbr Rfd false.
      zstep Rfd. zext32.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (l_loop2_t (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n la na lb lo v m2 ci B ci B H fin rdL Hh) end.
      all: jfin.
      +
        intros R5 H' Q20 HH1' HH2' HB29 HBn KP. cbv [keptc KS_E2T] in KP. kcbv_in Q20. destr_conj KP. zimps.
        clear SUB JR. unfold L_LVX_LL2_T.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
        unfold st_pull in SI1. st_cbn_in SI1.
        unfold KLEAVE_LD2 in KLL2. zkeys.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KLL2 Rx M1 _ lf cf SI1) end.
        * unfold s_regs_leave_ld2; icx_cbn; zkeys; split_conj; zreg.
        * close_std.
        * split; [exact Hmode | exact SREST].
        * exact SRET.
        * unfold s_lo; icx_cbn; split; assumption.
        * eapply s_bk_intro; [exact BK0 | lia | cbn [t_mode]; cbv [LEN LENEXT]; lia | cbn [t_mode]; cbv [LEN DIST]; lia].
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
      +
        intros R5 ci' B' H' Q32 Q7 Q23 Q10 Q13 Q20 Q21 Q22 Q24 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_E2T] in KP.
        kcbv_in Q32; kcbv_in Q7; kcbv_in Q23; kcbv_in Q10; kcbv_in Q13; kcbv_in Q20; kcbv_in Q21; kcbv_in Q22; kcbv_in Q24.
        destr_conj KP. zimps.
        clear KLL2. unfold L_LL2X_T.
        pose proof (JR H') as Rj2.
        set (j2 := Z.land H' m2 / 2 ^ lb) in *.
        destruct (SUB _ Rj2) as [NL3 TM3].
        assert (HPB2 : 1 <= 2 ^ B' <= 2 ^ 40) by (split; [pose proof (pow2_pos B' ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdL (v + j2))) as Rb2. pose proof (code_op_range (rdL (v + j2))) as Rop2.
        pose proof (code_val_range (rdL (v + j2))) as Rval2. pose proof (cellv_range (rdL (v + j2))) as Rcell2.
        zstep Rfd.
        zsetreg (code_op (rdL (v + j2))) ltac:(symmetry; apply cell_and255).
        tstep1 Rfd.
        zstep Rfd.
        zsetreg lb ltac:(rewrite <- L2; symmetry; apply bits_and31; lia).
        zstep Rfd.
        zsetreg (H' / 2 ^ lb) ltac:(symmetry; apply (srl_hold H' B'); lia).
        pose proof (hold_shr_bound H' B' lb ltac:(lia) ltac:(lia)) as HH2'.
        zstep Rfd.
        clear BK0.
        zhide_disj. pose proof Slap2 as DSEP; unfold ZSEP in DSEP.
        tstep1 Rfd.
        clear DSEP. zunhide_disj.
        apply term_ok_LENS in TM3 as [Hbits3 CLS3].
        zstep Rfd.
        zstep Rfd.
        subst j2.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (len_tail_t _ fin MD T M0 Rx lx Mx
                    (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf ci' (B' - lb) (H' / 2 ^ lb) (rdL (v + Z.land H' m2 / 2 ^ lb)) lb CX0 Hh Hfin eq_refl SI0) end.
        all: jfin.
        unfold PM, s_lo; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; exact HAG. }
  clear KL KLL2.
  zbr Rfd false.
  zstep Rfd.
  clear C104 C120.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ lb + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
  zstep Rfd.
  pose proof (land_mask_l' hold lb ltac:(lia)) as Ri0.
  pose proof (tab_root_entry LENS rdL lb na (Z.land (2 ^ lb + -1) hold) TOKL Ri0) as (Hbits0 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land (2 ^ lb + -1) hold) ltac:(symmetry; apply shl_2).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zbool1.
  zstep Rfd. zbool0.
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd. zext32.
  zstep Rfd.
  zsetreg (8 * (n - cin)) ltac:(symmetry; apply zext32_shift29; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (l_loop1_t (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n la na lb (2 ^ lb + -1) cin bits cin bits hold fin rdL Hh) end.
  all: jfin.
  - intros R' H' G20 HH1' HH2' HB14 HBn KP. cbv [keptc KS_E1T] in KP. kcbv_in G20. destr_conj KP. zimps.
    eapply (KX1 R' H'). all: jfin.
  - intros R' ci' B' H' G15 G7 G17 G12 G18 G6 G13 G20 G21 G29 G8 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_E1T] in KP.
    kcbv_in G15; kcbv_in G7; kcbv_in G17; kcbv_in G12; kcbv_in G18; kcbv_in G6; kcbv_in G13; kcbv_in G20; kcbv_in G21; kcbv_in G29; kcbv_in G8.
    destr_conj KP. zimps.
    eapply (JL1 R' ci' B' H'). all: jfin.
Qed.
