(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj IfA_base IfAKit IfA_lit IfA_direct IfA_wcopy.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_f8 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Hypothesis WNZ : wsz <> 0.
  Notation CST := (cst FR fc gp tp SP Zs S D n OB osz lb la da).
  Notation WINV := (winv SP Zs S OB osz Wd wsz whave wnext lb db la da bo fw m1 sd id ni ai no ao msg mode hw bw).
  Notation SRC_OK := (src_ok OB osz Wd).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).

  Lemma if_w9c : forall (m : amem) (v0 : word) (fo : Z -> Z) (x10 x11 x13 x15 x16 x21 x29 : word) (fa cob rem ci ca hold bits : Z),
    WINV m v0 fo -> 3 <= rem <= 258 -> SRC_OK fa rem -> 0 <= cob -> cob + rem <= osz ->
    evtF asegs RNG (AT_LATCH ci (cob + rem) hold bits) (CST x10 x11 x13 x15 x16 x21 x29 fa cob rem ci ca hold bits 0x97540 m).
  Proof using All.
    intros until bits. intros INV0 REM SRC COB COBR.
    unfold cst, gms.
    zs.
    eapply evtF_cut.
    { eapply (if_c3loop RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                        sd id ni ai no ao msg mode hw bw CX WNZ (Z.to_nat rem) m v0 fo _ _ _ _ _ _ fa cob rem 0 rem ci ca hold bits INV0); try lia. exact SRC. }
    cbv beta. intros ms2 (m2 & y10 & y11 & y15 & y16 & y21 & y29 & fo2 & i2 & rem2 & -> & INV2 & REM2 & IL2 & I3).
    unfold cst, gms.
    zs. zs. setreg 7 (Z_to_bv 64 (OB + (cob + i2))) ltac:(f_equal; lia).
    zs. zbr0 K2.
    + replace (cob + rem) with (cob + i2 + rem2) by lia.
      eapply (if_wtail12 RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                         sd id ni ai no ao msg mode hw bw CX WNZ m2 v0 fo2 _ _ _ _ _ _ _ (fa + i2) (cob + i2) rem2 ci _ hold bits INV2); try lia.
      unfold src_ok in *. destruct SRC as [SRC|SRC]; [left| right]; lia.
    + replace (cob + rem) with (cob + i2) by lia.
      eapply (if_wtail0 RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                        sd id ni ai no ao msg mode hw bw CX WNZ m2 v0 fo2 _ _ _ _ _ _ _ (fa + i2) (cob + i2) rem2 ci _ hold bits INV2); lia.
  Qed.

  Lemma if_w10 : forall (m : amem) (v0 : word) (fo : Z -> Z) (x10 x11 x13 x15 x16 x21 x29 : word) (fa cob rem ci ca hold bits : Z),
    WINV m v0 fo -> 0 <= rem <= 2 -> SRC_OK fa rem -> 0 <= cob -> cob + rem <= osz ->
    evtF asegs RNG (AT_LATCH ci (cob + rem) hold bits) (CST x10 x11 x13 x15 x16 x21 x29 fa cob rem ci ca hold bits 0x974b4 m).
  Proof using All.
    intros until bits. intros INV0 REM SRC COB COBR.
    unfold cst, gms.
    zs. zbr0 K2.
    + replace (cob + rem) with cob by lia.
      eapply (if_wtail0 RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                        sd id ni ai no ao msg mode hw bw CX WNZ m v0 fo _ _ _ _ _ _ _ fa cob rem ci ca hold bits INV0); lia.
    + eapply (if_wtail12 RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                         sd id ni ai no ao msg mode hw bw CX WNZ m v0 fo _ _ _ _ _ _ _ fa cob rem ci ca hold bits INV0); try lia. exact SRC.
  Qed.
End P.
End CANSEC1.
