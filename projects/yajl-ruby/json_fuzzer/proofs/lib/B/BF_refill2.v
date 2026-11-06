(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac cstep := stepA; try first [if_true | if_false].

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition kMtxWriter : Z := 0x1000000000000000.
Definition rrow (mtx nf mfa au mu na nfr : Z) : list cell :=
  [C8 (Z_to_bv 64 mtx); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
   C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nfr);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Section GFA.
Variable P : acc -> Prop.
(* [comment removed for export] *)
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo INST STAT c CH n SB RI RP FA : Z).
Hypothesis HRP : RP = RI + kRegSize * c.
Hypothesis HFA : FA = SB + c * 2^32 + 0xE0000000.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 128.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis HC : 1 <= c <= 30.
Hypothesis HN : 1 <= n <= 16.
Hypothesis HINST : 0xa5000 <= INST /\ INST + 64 <= 0x603000.
Hypothesis HSB : 0x10007fff8000 <= SB /\ SB + 2^37 + 4096 <= alloc_ceiling /\ SB mod 4096 = 0.
Hypothesis HRI : RI = SB + 2^37.
Hypothesis HCH : (0x1000 <= CH /\ (CH + 64 <= 0x10000 \/ 0x603000 <= CH)) /\ CH + 64 <= alloc_ceiling /\ CH mod 4 = 0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis HCS : CH + 64 <= SB \/ SB + 2^37 + 4096 <= CH.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRI : forall a k, RI <= a -> a + Z.of_nat k <= RI + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, CH <= a -> a + Z.of_nat k <= CH + 64 -> P (Z_to_bv 64 a, k).

Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -128)).
(* [comment removed for export] *)
Definition gfa_W : list (Z * Z) := [(bv_unsigned sp - 128, bv_unsigned sp); (RP, RP + 24); (RP + 72, RP + 80); (CH, CH + 4 * n)].

(* [comment removed for export] *)
Definition gfa_locked (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) (nf mfa au mu na nfr : Z) : machine_state -> Prop :=
  fun ms' => exists m' (fj : list byte),
    ms' = MS (mkR ra SP' gp tp (Z_to_bv 64 0) (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 0) (Z_to_bv 64 RP) (Z_to_bv 64 INST) (Z_to_bv 64 (RP + 8))
                 (Z_to_bv 64 STAT) (Z_to_bv 64 c) (Z_to_bv 64 CH) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                 s2 (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 FA) (Z_to_bv 64 0x10000000000) (Z_to_bv 64 0x10000000000fffff)
                 (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 1500) (Z_to_bv 64 0xdfffffffffffffff) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37a4c) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (RP, RP + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells bsegs m' (bv_unsigned sp + -128) [CB 24 fj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' RP (rrow kMtxWriter nf mfa au mu na nfr).

Lemma gfa_lock : forall (t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) (nf mfa au mu na nfr : Z),
  stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
  rw_cells bsegs m (INST + 32) [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells bsegs m RP (rrow 0 nf mfa au mu na nfr) ->
  evtA bsegs P (gfa_locked s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m nf mfa au mu na nfr)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 STAT) (Z_to_bv 64 c) (Z_to_bv 64 CH) (Z_to_bv 64 n) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x378fc) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until nfr. intros SK MI IROW RROW. unfold rrow in RROW.
  pose proof LOC as LOCu. aceil.
  pose proof HSB as (SB1 & SB2 & SB3). aceil. pose proof HCH as (CH1 & CH2 & CH4). aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MU : munch [(bv_unsigned sp - 128, bv_unsigned sp); (RP, RP + 8)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (HRP' : RP = SB + 2^37 + 128 * c) by (rewrite HRP, HRI; unfold kRegSize; lia).
  assert (PRP : forall a k, RP <= a -> a + Z.of_nat k <= RP + 128 -> P (Z_to_bv 64 a, k)) by (intros a k H1 H2; apply PRI; rewrite HRP' in H1, H2; lia).
  clear HRP. unfold kMtxWriter.
  carve_frame 128%nat SK.
  do 15 zstepA.            (* [comment removed for export] *)
  do 5 zstepA.             (* [comment removed for export] *)
  do 12 zstepA.            (* [comment removed for export] *)
  replace (RI + c ≪ 7) with RP by (rewrite HRP', HRI, Z.shiftl_mul_pow2 by lia; lia).
  replace (SB + (c ≪ 32 + 3758096384)) with FA by (rewrite HFA, !Z.shiftl_mul_pow2 by lia; lia).
  zstepA.                  (* [comment removed for export] *)
  do 5 zstepA.             (* [comment removed for export] *)
  zstepA.                  (* [comment removed for export] *)
  cstep.                   (* [comment removed for export] *)
  zstepA. zstepA.          (* [comment removed for export] *)
  zstepA.                  (* [comment removed for export] *)
  cstep.                   (* [comment removed for export] *)
  zstepA.                  (* [comment removed for export] *)
  cstep.                   (* [comment removed for export] *)
  cstep.                   (* [comment removed for export] *)
  apply evtA_done. unfold gfa_locked, gfa_W, rrow, kMtxWriter. do 2 eexists.
  split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try eassumption.
Qed.
End GFA.
End RC__1.
