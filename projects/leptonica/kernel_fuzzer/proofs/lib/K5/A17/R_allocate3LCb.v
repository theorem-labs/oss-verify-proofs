(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Arr Walk Image.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import R_small R_m2s R_setshadow R_thread R_cache_defs R_prim_defs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import R_classid R_leaves F_memset R_depot_defs R_asan_defs R_allocate1 R_allocate2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import R_allocate1C R_allocate3 R_allocate3C.
Import ListNotations.
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
(* [comment removed for export] *)
Local Definition zmin (x y : Z) : Z := Z.min x y.
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

Lemma allocate_p3b_tailL0 : forall sp gp ra0 t0 t1 t2 a0v a1 a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s6v s9v s3v
    fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12
    (F : bvmap 5 word) fc (m : mem) (n AB B T lo b1 : Z) (h0 uj lj j0 : list byte) (ctx : word),
  (1 <= n <= 2^31)%Z -> (0x629000 < AB)%Z -> (AB + needed2 n <= kHighMemEnd + 1)%Z -> (0 <= b1 < 256)%Z ->
  alloc_frame0 m (bv_unsigned sp) fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 -> rw_cells asegs m (bv_unsigned sp) [CB 8 j0] ->
  rw_cells asegs m (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells asegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [CB 16 lj])%Z ->
  rw_cells asegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] ->
  rw_cells asegs m (g_asan_flags + 44) [C4 (Z_to_bv 64 4096)] -> rw_cells asegs m (g_asan_flags + 52) [C4 (Z_to_bv 64 190)] ->
  setshadow_cells m ->
  rw_cells asegs m 0xcacb0 [C8 (Z_to_bv 64 16)] -> rw_cells asegs m (tpA + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m g_MFHooks [C8 (Z_to_bv 64 0)] ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0x629000 <= lo)%Z -> (bv_unsigned sp + 128 <= 2^63)%Z ->
  (AB + needed2 n <= lo)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_post0 fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 sp gp (Z_to_bv 64 tpA) F fc n AB b1 ctx uj lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0v a1 a2v a3 a4 a5
             a6 a7 (Z_to_bv 64 AB) s3v
             (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) s6v (Z_to_bv 64 B) (Z_to_bv 64 0) s9v
             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x3ce38) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros Hn HAB HABl Hb1 FR FRj HD UJ LJ GAF FL1 FL2 SS GLS TLS MFH ST HLO HIMG HSP HABlo MI.
  change (Z.min n 4096) with (zmin n 4096) in *.
  assert (Hzmn : (1 <= zmin n 4096 <= 4096 /\ zmin n 4096 <= n)%Z) by (unfold zmin; lia).
  pose proof (needed2_range n Hn) as NR. pose proof (needed2_ge n ltac:(lia)) as NG. pose proof (rz_size_range n) as RZR.
  pose proof (rz_size_mod16 n) as RZM.
  unfold alloc_frame0 in FR. destruct SS as (SS1 & SS2).
  unfold kHighShadowEnd, kHighMemEnd, g_GOT_asan_flags, g_asan_flags, g_MFHooks, tpA, g_got_real_memset, g_real_memset,
    musl_memset_entry in *.
  change (856504 + 44)%Z with 856548%Z in FL1. change (856504 + 52)%Z with 856556%Z in FL2. change (6318984 + 16)%Z with 6319000%Z in TLS.
  move GAF at bottom. move SS1 at bottom. move GLS at bottom. move SS2 at bottom. move FL1 at bottom. move FL2 at bottom.
  move MFH at bottom. move TLS at bottom.
  pose proof (munch_refl [(AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (bv_unsigned sp - 32, bv_unsigned sp + 128)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (bv_unsigned sp - 32, bv_unsigned sp + 128)]%Z m) as MU3.
  zhide.
  (* [comment removed for export] *)
  do 6 zstep. fold_reg 10%Z.
  zstep.
  do 6 zstep.
  replace (bv_unsigned (Z_to_bv 8 b1)) with b1 by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256%Z;
                                                   rewrite Z.mod_small by lia; reflexivity).
  zstep. sb_fix.
  zstep. zstep; fix_lit_store.
  zstep.
  destruct (Z.eq_dec (rz_size n) 16) as [R16|R16].
  - ifT. p3b_hooks sp FR FRj ST.
    rewrite R16 in *. lia.
  - ifF.
    pose proof (rw_cells_transport asegs _ m _ AB _ (LJ ltac:(lia)) MU3 WM ltac:(cbn [disjoint_from]; simpl_sizes; slia)) as LJC.
    clear LJ MU3.
    zstep. zstep. ifF.
    let mm := amem in
    let bs := eval vm_compute in (option.default [] (image_bytes asegs 0x10338 8)) in
    assert (RCM : ro_cells asegs mm 0x10338 [CB (length bs) bs])
      by (apply ro_cells_image; [eassumption| vm_compute; reflexivity| lia| cbn; lia]).
    cbn [length] in RCM.
    zstep. zstep. fold_reg 10%Z. clear RCM.
    zstep. zstep. zstep; fix_lit_store.
    p3b_hooks sp FR FRj ST.
    all: try (intros _; eassumption).
Qed.
