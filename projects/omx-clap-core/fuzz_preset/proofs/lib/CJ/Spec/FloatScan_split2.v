(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import FloatScan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

Section FinalK.
  Variables (bits emin sign emax : Z) (bias0 : Z).

  (* [comment removed for export] *)
  Definition fin_K3 (y frac bias e2 : Z) : option Z :=
    let y := f128_add y frac in
    let y := f128_sub y bias in
    let '(y, e2) :=
      if emax - 5 <? Z.land (u32 (e2 + LDBL_MANT_DIG_)) INT_MAX_ then
        let ay := m_fabsl y in
        let two := f128_of_i32 2 in
        let lim := f128_div two C_LDBL_EPS in
        if 0 <=? f128_ge ay lim then
          let half := f128_of_d (bv_unsigned D_05) in
          let y := f128_mul y half in (y, e2 + 1)
        else (y, e2)
      else (y, e2) in
    Some (m_scalbnl y e2).

  (* [comment removed for export] *)
  Definition fin_K2 (a z : Z) (x : list Z) (i bits' y frac bias e2 : Z) : option Z :=
    let r :=
      if negb (Z.land (a + i) MASK =? z) then
        let t := znth x (Z.land (a + i) MASK) in
        let signd := fcvt_d_w RNE (Z_to_bv 64 sign) in
        let od :=
          if (t <? 500000000) && (nz t || negb (Z.land (a + i + 1) MASK =? z))
          then Some (fmul_d RNE D_025 signd)
          else if 500000000 <? t
          then Some (fmul_d RNE D_075 signd)
          else if t =? 500000000 then
            (if Z.land (a + i + 1) MASK =? z
             then Some (fmul_d RNE D_05 signd)
             else Some (fmul_d RNE D_075 signd))
          else None in
        let frac := match od with
          | Some d => let e := f128_of_d (bv_unsigned d) in f128_add frac e
          | None => frac end in
        if 2 <=? LDBL_MANT_DIG_ - bits' then
          let one := f128_of_i32 1 in
          match m_fmodl frac one with
          | None => None
          | Some rr => if f128_le rr 0 =? 0 then Some (f128_add frac C_ONE) else Some frac
          end
        else Some frac
      else Some frac in
    match r with
    | None => None
    | Some frac => fin_K3 y frac bias e2
    end.

  (* [comment removed for export] *)
  Definition fin_K1 (a z : Z) (x : list Z) (i y e2 : Z) : option Z :=
    let sf := f128_of_i32 sign in
    let y := f128_mul y sf in
    let '(bits', denormal) :=
      if LDBL_MANT_DIG_ + e2 - emin <? bits then
        let b := LDBL_MANT_DIG_ + e2 - emin in ((if b <? 0 then 0 else b), 1)
      else (bits, 0) in
    let r :=
      if bits' <? LDBL_MANT_DIG_ then
        let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (2 * LDBL_MANT_DIG_ - bits' - 1) in
        let t := f128_of_d (bv_unsigned d) in
        let bias := m_copysignl t y in
        let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (LDBL_MANT_DIG_ - bits') in
        let t := f128_of_d (bv_unsigned d) in
        match m_fmodl y t with
        | None => None
        | Some frac => Some (f128_add (f128_sub y frac) bias, frac, bias)
        end
      else Some (y, bias0, bias0) in
    match r with
    | None => None
    | Some (y, frac, bias) => fin_K2 a z x i bits' y frac bias e2
    end.

  Lemma df_final_split : forall a z x e2,
    df_final a z x e2 bits emin sign emax bias0 bias0 =
    match df_asm_loop 5%nat a (mkAS 0 (f128_of_i32 0) z x) with
    | None => None
    | Some (mkAS i y z x) => fin_K1 a z x i y e2
    end.
  Proof.
    intros a z x e2. unfold df_final, fin_K1, fin_K2, fin_K3.
    destruct (df_asm_loop _ _ _) as [[i y z1 x1]|]; reflexivity.
  Qed.

  Lemma df_asm_loop_step : forall n a s,
    df_asm_loop (S n) a s = if as_i s <? LD_B1B_DIG then df_asm_loop n a (df_asm_body a s) else Some s.
  Proof. reflexivity. Qed.
End FinalK.
