(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_allocA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.

Ltac cstep := stepA; try first [if_true | if_false].
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ True => split; [lia| exact I] | |- _ /\ _ => split; [lia| first [exact I| lia]] end | lia ].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hdr_b1 : forall J, 0 <= J -> Z.land ((Z.lor (Z.land (Z.lor (Z.land J 18446744073709551612) 1) 143) 16) mod 256) 115 = 17.
Proof.
  intros J HJ.
  rewrite <- (Z.land_ones _ 8) by (repeat (apply Z.lor_nonneg; split); try apply Z.land_nonneg; lia).
  change (Z.ones 8) with 255. rewrite <- Z.land_assoc. change (Z.land 255 115) with 115.
  rewrite Z.land_lor_distr_l. change (Z.land 16 115) with 16. rewrite <- Z.land_assoc. change (Z.land 143 115) with 3.
  rewrite Z.land_lor_distr_l. change (Z.land 1 3) with 1. rewrite <- Z.land_assoc. change (Z.land 18446744073709551612 3) with 0.
  rewrite Z.land_0_r. reflexivity.
Qed.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ALLOC.
Variable P : acc -> Prop.
(* [comment removed for export] *)
Variables (xra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
          (os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 ora : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (junk : list byte).
Variables (lo hi n B A len : Z) (CTX T ab : Z).
Variables (j0 j1 : bv 8) (j2 j3 j4 : word).
Definition INST : Z := 0xaa518.
Definition rz : Z := rz_size n.
Definition ub : Z := ab + rz.                 (* [comment removed for export] *)
Definition cb : Z := ab + rz + -16.           (* [comment removed for export] *)
#[local] Notation usp := (bv_unsigned sp).

Hypothesis SK : stk asegs m lo (bv_unsigned sp + -128).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 512.
Hypothesis SPH : bv_unsigned sp <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis MI : mem_inv asegs m.
Hypothesis Hn : 1 <= n <= 2^27.
Hypothesis HB : bv_unsigned sp <= B /\ B + 16 <= hi.
Hypothesis FRAME : rw_cells asegs m (bv_unsigned sp + -128)
    [CB 8 junk; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ora].
Hypothesis HDR : rw_cells asegs m cb [C1 j0; C1 j1; C2 j2; C4 j3; C8 j4].
Hypothesis TCTX : rw_cells asegs m T [C8 (Z_to_bv 64 CTX)].                   (* [comment removed for export] *)
Hypothesis TID : rw_cells asegs m (CTX + 8) [C4 (Z_to_bv 64 0)].             (* [comment removed for export] *)
Hypothesis BOBJ : rw_cells asegs m B [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 len)].        (* [comment removed for export] *)
Hypothesis HT : 0x1000 <= T /\ T + 4096 <= alloc_ceiling.
Hypothesis HCTX : 0x603000 <= CTX /\ CTX + 4096 <= alloc_ceiling.
Hypothesis HAB : 0x603000 <= ab /\ ab + needed n <= alloc_ceiling /\ ab mod 8 = 0.
Hypothesis DBT : ab + needed n <= T \/ T + 4096 <= ab.                   (* [comment removed for export] *)
Hypothesis DBC : ab + needed n <= CTX \/ CTX + 160 <= ab.                (* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k).
Hypothesis PTHR : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : forall a k, CTX <= a -> a + Z.of_nat k <= CTX + 160 -> P (Z_to_bv 64 a, k).
Hypothesis PBLK : forall a k, ab <= a -> a + Z.of_nat k <= ab + needed n -> P (Z_to_bv 64 a, k).

Definition segB5_post : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (b1 : Z),
    ms = MS (mkR (Z_to_bv 64 0x32fac) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 len) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 ub) (Z_to_bv 64 cb) (Z_to_bv 64 INST) (Z_to_bv 64 B)
                 (Z_to_bv 64 0) (Z_to_bv 64 (ub + n)) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
            F (Z_to_bv 64 0x73f64) fc None m' (seg_rom asegs)
    /\ munch [(cb, cb + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ 0 <= b1 < 256 /\ Z.land b1 115 = 17
    /\ rw_cells asegs m' cb [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 j4]
    /\ rw_cells asegs m' (bv_unsigned sp + -128)
         [CB 8 junk; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ora].


Lemma alloc5_segB :
  evtA asegs P segB5_post
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n)
             (Z_to_bv 64 ab) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed n)) (Z_to_bv 64 rz) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) s8
             (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x32ea0) fc None m (seg_rom asegs)).
Proof.
  pose proof LOC as LOCu. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rz_size_pos n) as RZP. change (rz_size n) with rz in RZP.
  pose proof (needed_range n Hn) as NR. assert (N1 : needed1 n = rounded n + rz) by reflexivity.
  pose proof (rounded_ge n) as (RG1 & RG2 & _).
  pose proof (bv_unsigned_in_range 8 j1) as J8. change (bv_modulus 8) with 256 in J8.
  unfold INST, cb in *.
  assert (MU : munch [(ab + rz + -16, ab + rz + -16 + 8)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA. zstepA; if_cases KA; zify_cond KA; [kill KA| clear KA].   (* [comment removed for export] *)
  do 3 zstepA.                        (* [comment removed for export] *)
  try rewrite (Z.mod_small (ab + rz) 18446744073709551616) by arith.
  replace (Z.land (ab + rz) 7) with 0
    by (change 7 with (Z.ones 3); rewrite Z.land_ones by arith; change (2^3) with 8;
        pose proof (rz_size_mod16 n) as M16; change (rz_size n) with rz in M16; destruct HAB as (_ & _ & M8); clear -M8 M16 RZP; symmetry;
        apply Z.mod_divide; [lia|]; apply Z.mod_divide in M8; [|lia]; apply Z.mod_divide in M16; [|lia];
        destruct M8 as [p Hp]; destruct M16 as [q Hq]; exists (p + 2 * q); lia).
  cstep.                              (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA; if_cases KB; zify_cond KB; [kill KB| clear KB].   (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  do 5 zstepA.                        (* [comment removed for export] *)
  try rewrite (Z.mod_small n 18446744073709551616) by arith. rewrite !Z.shiftr_div_pow2 by (clear; lia).
  change (2 ^ 32) with 4294967296. change (2 ^ 48) with 281474976710656.
  rewrite (Z.div_small n 4294967296) by arith. rewrite (Z.div_small n 281474976710656) by arith.
  set (v1 := Z.lor (Z.land (bv_unsigned j1) 18446744073709551612) 1).
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  do 4 zstepA.                        (* [comment removed for export] *)
  set (v2 := Z.lor (Z.land v1 143) 16).
  zstepA.                             (* [comment removed for export] *)
  zstepA; if_cases KT; zify_cond KT; [kill KT| clear KT].   (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  try change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  zstepA.                             (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  zstepA. zstepA.                     (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  apply evtA_done; unfold segB5_post, ub, INST. do 14 eexists. exists (v2 mod 256).
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [apply Z.mod_pos_bound; clear; lia|]. split; [subst v2 v1; apply hdr_b1; clear -J8; lia|].
  split; eassumption.
Qed.
End ALLOC.
End RC__1.
