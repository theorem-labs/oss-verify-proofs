(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_libiface I_lift X_atexit L_hkit L_harn_defs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_merge.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mod11_regK : forall len, 0 <= len < 2 ^ 32 ->
  bv_swrap 32 (len - (((len * 3353953467947191203) ≫ 64 mod 18446744073709551616) ≫ 1 * 11) mod 18446744073709551616) = len mod 11.
Proof.
  intros len H. change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change 3353953467947191203 with M11.
  assert (B : 0 <= len * M11 / 2 ^ 64 < 2 ^ 64).
  { unfold M11. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small _ _ B). change (2 ^ 1) with 2. rewrite div11_magic by exact H.
  pose proof (Z.mod_pos_bound len 11 ltac:(lia)). pose proof (Z.div_mod len 11 ltac:(lia)).
  rewrite Z.mod_small by lia. rewrite Str_merge.swrap32_small by lia. lia.
Qed.

Lemma hz_wC : forall (usp spa Fr d n zb : Z)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= n < 2^26 -> 0 <= zb < 2^64 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a7' : word),
      ms = entry_st (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 zb)
             (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 d) (Z_to_bv 64 n) (Z_to_bv 64 (bs_of n)) (Z_to_bv 64 0) (Z_to_bv 64 (wf_of n)) a7'
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11
             t3 t4 t5 t6 F fc e_b2bc m)
    (MS (mkR (Z_to_bv 64 0x81434) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 zb) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x81434)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros N0 ZB MI.
  unfold entry_st, e_b2bc, RA_B2BC in *.
  replace (ret_pc (Z_to_bv 64 0x81434)) with (Z_to_bv 64 0x81434) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 7 lstep. rewrite (mod11_regK n) by lia.
  pose proof (Z.mod_pos_bound n 11 ltac:(lia)) as M11B.
  lstep. lstep. lstep.
  assert (WF : forall X, X = n / 251 * 251 -> n + - X = wf_of n)
    by (intros X ->; unfold wf_of; pose proof (Z.div_mod n 251 ltac:(lia)); lia).
  assert (Q0 : 0 <= n * M251 / 2 ^ 64 <= n).
  { unfold M251. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  assert (D251 : ((n - n * M251 / 2 ^ 64) / 2 + n * M251 / 2 ^ 64) / 2 ^ 7 = n / 251) by (exact (div251_magic n ltac:(lia))).
  assert (WFX : (((((n + - ((n * 367465021388636487) ≫ 64 mod 18446744073709551616)) mod 18446744073709551616) ≫ 1 + (n * 367465021388636487) ≫ 64)
                  mod 18446744073709551616) ≫ 7 * 251) mod 18446744073709551616 = n / 251 * 251).
  { change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change 367465021388636487 with M251.
    rewrite (Z.mod_small (n * M251 / 2 ^ 64) (2 ^ 64)) by lia.
    replace (n + - (n * M251 / 2 ^ 64)) with (n - n * M251 / 2 ^ 64) by lia.
    rewrite (Z.mod_small (n - n * M251 / 2 ^ 64) (2 ^ 64)) by lia. change (2 ^ 1) with 2.
    assert (B2 : 0 <= (n - n * M251 / 2 ^ 64) / 2 + n * M251 / 2 ^ 64 <= n).
    { pose proof (Z.div_pos (n - n * M251 / 2 ^ 64) 2 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (n - n * M251 / 2 ^ 64) 2 (n - n * M251 / 2 ^ 64) ltac:(lia) ltac:(lia)). lia. }
    rewrite (Z.mod_small ((n - n * M251 / 2 ^ 64) / 2 + n * M251 / 2 ^ 64) (2 ^ 64)) by lia.
    rewrite D251. pose proof (Z.div_mod n 251 ltac:(lia)). pose proof (Z.mod_pos_bound n 251 ltac:(lia)). rewrite Z.mod_small by lia. reflexivity. }
  assert (BS : forall b : bool, (n mod 11 <? 8) = b -> (if b then n mod 11 + 1 else 8 + 1) = bs_of n).
  { intros b Hb. unfold bs_of. destruct b; [apply Z.ltb_lt in Hb| apply Z.ltb_ge in Hb]; lia. }
  if_cases BR; unfold bv_ltu in BR; rewrite !unsigned_lit in BR by lia.
  - do 17 lstep. rewrite WFX, (WF _ eq_refl). change (n mod 11 + 1) with (if true then n mod 11 + 1 else 8 + 1). rewrite (BS true BR).
    replace (n + 0) with n by lia. rewrite Str_merge.swrap32_small by lia.
    apply evt_done. eexists. reflexivity.
  - do 18 lstep. rewrite WFX, (WF _ eq_refl).
    replace (Z_to_bv 64 9) with (Z_to_bv 64 (bs_of n)) by (rewrite <- (BS false BR); reflexivity).
    replace (n + 0) with n by lia. rewrite Str_merge.swrap32_small by lia.
    apply evt_done. eexists. reflexivity.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_libiface I_lift X_atexit
  L_hkit L_harn_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_merge.

(* [comment removed for export] *)
Lemma mod11_regK : forall len, 0 <= len < 2 ^ 32 ->
  bv_swrap 32 (len - (((len * 3353953467947191203) ≫ 64 mod 18446744073709551616) ≫ 1 * 11) mod 18446744073709551616) = len mod 11.
Proof.
  intros len H. change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change 3353953467947191203 with M11.
  assert (B : 0 <= len * M11 / 2 ^ 64 < 2 ^ 64).
  { unfold M11. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small _ _ B). change (2 ^ 1) with 2. rewrite div11_magic by exact H.
  pose proof (Z.mod_pos_bound len 11 ltac:(lia)). pose proof (Z.div_mod len 11 ltac:(lia)).
  rewrite Z.mod_small by lia. rewrite Str_merge.swrap32_small by lia. lia.
Qed.

Lemma hz_wC : forall (usp spa Fr d n zb : Z)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= n < 2^26 -> 0 <= zb < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a7' : word),
      ms = entry_st (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 zb)
             (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 d) (Z_to_bv 64 n) (Z_to_bv 64 (bs_of n)) (Z_to_bv 64 0) (Z_to_bv 64 (wf_of n)) a7'
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11
             t3 t4 t5 t6 F fc e_b2bc m)
    (MS (mkR (Z_to_bv 64 0x819e8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 zb) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x819e8)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros N0 ZB MI.
  unfold entry_st, e_b2bc, RA_B2BC in *.
  replace (ret_pc (Z_to_bv 64 0x819e8)) with (Z_to_bv 64 0x819e8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 7 lstep. rewrite (mod11_regK n) by lia.
  pose proof (Z.mod_pos_bound n 11 ltac:(lia)) as M11B.
  lstep. lstep. lstep.
  assert (WF : forall X, X = n / 251 * 251 -> n + - X = wf_of n)
    by (intros X ->; unfold wf_of; pose proof (Z.div_mod n 251 ltac:(lia)); lia).
  assert (Q0 : 0 <= n * M251 / 2 ^ 64 <= n).
  { unfold M251. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  assert (D251 : ((n - n * M251 / 2 ^ 64) / 2 + n * M251 / 2 ^ 64) / 2 ^ 7 = n / 251) by (exact (div251_magic n ltac:(lia))).
  assert (WFX : (((((n + - ((n * 367465021388636487) ≫ 64 mod 18446744073709551616)) mod 18446744073709551616) ≫ 1 + (n * 367465021388636487) ≫ 64)
                  mod 18446744073709551616) ≫ 7 * 251) mod 18446744073709551616 = n / 251 * 251).
  { change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change 367465021388636487 with M251.
    rewrite (Z.mod_small (n * M251 / 2 ^ 64) (2 ^ 64)) by lia.
    replace (n + - (n * M251 / 2 ^ 64)) with (n - n * M251 / 2 ^ 64) by lia.
    rewrite (Z.mod_small (n - n * M251 / 2 ^ 64) (2 ^ 64)) by lia. change (2 ^ 1) with 2.
    assert (B2 : 0 <= (n - n * M251 / 2 ^ 64) / 2 + n * M251 / 2 ^ 64 <= n).
    { pose proof (Z.div_pos (n - n * M251 / 2 ^ 64) 2 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (n - n * M251 / 2 ^ 64) 2 (n - n * M251 / 2 ^ 64) ltac:(lia) ltac:(lia)). lia. }
    rewrite (Z.mod_small ((n - n * M251 / 2 ^ 64) / 2 + n * M251 / 2 ^ 64) (2 ^ 64)) by lia.
    rewrite D251. pose proof (Z.div_mod n 251 ltac:(lia)). pose proof (Z.mod_pos_bound n 251 ltac:(lia)). rewrite Z.mod_small by lia. reflexivity. }
  assert (BS : forall b : bool, (n mod 11 <? 8) = b -> (if b then n mod 11 + 1 else 8 + 1) = bs_of n).
  { intros b Hb. unfold bs_of. destruct b; [apply Z.ltb_lt in Hb| apply Z.ltb_ge in Hb]; lia. }
  if_cases BR; unfold bv_ltu in BR; rewrite !unsigned_lit in BR by lia.
  - do 17 lstep. rewrite WFX, (WF _ eq_refl). change (n mod 11 + 1) with (if true then n mod 11 + 1 else 8 + 1). rewrite (BS true BR).
    replace (n + 0) with n by lia. rewrite Str_merge.swrap32_small by lia.
    apply evt_done. eexists. reflexivity.
  - do 18 lstep. rewrite WFX, (WF _ eq_refl).
    replace (Z_to_bv 64 9) with (Z_to_bv 64 (bs_of n)) by (rewrite <- (BS false BR); reflexivity).
    replace (n + 0) with n by lia. rewrite Str_merge.swrap32_small by lia.
    apply evt_done. eexists. reflexivity.
Qed.
