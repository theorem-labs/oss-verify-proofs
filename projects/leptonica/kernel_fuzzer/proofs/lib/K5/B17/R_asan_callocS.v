(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Arr Walk Image.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import R_small R_m2s R_thread R_cache_defs R_prim_defs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import R_leaves I_ikit R_unwind_defs R_unwindimpl R_depot_defs R_asan_defs R_allocate1 R_prim_kit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import R_asan_malloc R_setshadow R_allocate1C R_allocate3 F_memset.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import R_asan_calloc.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Definition calloc_Bs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (UB n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(UB, UB + n); (bv_unsigned sp - 2192, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma calloc_Bs_spec : forall ra sp gp tp t0 t1 t2 s1' a1 a2 a3 a4 a5 a6 a7 s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 s6 v1 v2 v3 (F : bvmap 5 word) fc (m : mem) (UB n SB lo : Z) (ws : list word) (w : word)
    (jp jq j1 uj : list byte),
  (0 < UB < 2^64)%Z -> (1 <= n <= 2^31)%Z -> (0 <= SB)%Z -> (SB + 2^37 < 2^64)%Z -> (UB < SB \/ SB + 2^37 <= UB)%Z -> (UB + n <= lo)%Z ->
  stk asegs m lo (bv_unsigned sp + -2192) -> (lo <= bv_unsigned sp + -2192)%Z -> (0x62a000 <= lo)%Z ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jp] ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))] ->
  u64arr asegs m (bv_unsigned sp + -2120) ws -> length ws = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jq] ->
  rw_cells asegs m (bv_unsigned sp + -2192) [CB 8 j1; C8 v3; C8 v2; C8 v1; C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x5e9ac)] ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> setshadow_cells m ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  mem_inv asegs m ->
  evt asegs (calloc_Bs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc UB n lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1' (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 INST) (Z_to_bv 64 1) s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d32c) fc None m (seg_rom asegs)).
Proof.
  intros until uj. intros HUB Hn HSB0 HSB1 HPR HUBlo ST HLO HIMG FRs FRp FRt TB HTB FRb FRq FRa SBC SS UJ MI.
  destruct SS as (SS1 & SS2). unfold i_spacebeg, INST, g_instance, g_got_real_memset, g_real_memset, musl_memset_entry in *.
  change (856024 + 32)%Z with 856056%Z in SBC.
  move SBC at bottom. move SS1 at bottom. move SS2 at bottom.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(UB, UB + n); (SP - 2192, SP)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply u64arr_rw_ma in TB. rewrite HTB in TB.
  zhide.
  zstep. ifF.
  zstep.
  destruct HPR as [HPR | HPR].
  - (* [comment removed for export] *)
    zstep. ifT.
    do 7 zstep.
    do 10 zstep.
    release_frame FRa ST (SP + -2144)%Z. release_frame FRq ST (SP + -2136)%Z. release_frame FRb ST (SP + -2120)%Z.
    release_frame TB ST (SP + -80)%Z. release_frame FRt ST (SP + -72)%Z. release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
    zstep.
    finish.
    all: rewrite ?(unsigned_lit SP) by lia; try assumption.
  - (* [comment removed for export] *)
    zstep. ifF.
    zstep. zstep.
    zstep. ifT.
    do 7 zstep.
    do 10 zstep.
    release_frame FRa ST (SP + -2144)%Z. release_frame FRq ST (SP + -2136)%Z. release_frame FRb ST (SP + -2120)%Z.
    release_frame TB ST (SP + -80)%Z. release_frame FRt ST (SP + -72)%Z. release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
    zstep.
    finish.
    all: rewrite ?(unsigned_lit SP) by lia; try assumption.
Qed.
