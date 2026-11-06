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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_lkit AF_gbb.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
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
Fixpoint list_setn {X} (l : list X) (i : nat) (x : X) : list X :=
  match l, i with [], _ => [] | _ :: l', O => x :: l' | y :: l', S i' => y :: list_setn l' i' x end.

Section LDPRE.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo PA : Z) (cs : list (Z * Z)) (junk : list word) (i : nat) (c : Z * Z).
Variables (ptrc na nf cur mx ga gm : Z) (nd3 : word).
(* [comment removed for export] *)
Hypothesis SK : stk asegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 32.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv asegs m.
Hypothesis NTH : nth_error cs i = Some c.
Hypothesis SEC : rw_cells asegs m 0xaa558 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA)].
Hypothesis NRS : rw_cells asegs m 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs))); C1 (Z_to_bv 8 0)].
Hypothesis SST : rw_cells asegs m 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)].
Hypothesis MTX : rw_cells asegs m 0xaa7c0 [C4 (Z_to_bv 64 0)].
Hypothesis GST : rw_cells asegs m 0xaa7d8 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)].
Hypothesis ARR : u64arr asegs m PA (gws cs junk).
Hypothesis HPA : 0x603000 <= PA /\ PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= alloc_ceiling.
Hypothesis HDRS : forall j c', nth_error cs j = Some c' ->
  exists w3, rw_cells asegs m (fst c') [C8 (Z_to_bv 64 (fst c')); C8 (Z_to_bv 64 (snd c')); C8 w3; C8 (Z_to_bv 64 (Z.of_nat j))].
Hypothesis HDRC : rw_cells asegs m (fst c) [C8 (Z_to_bv 64 (fst c)); C8 (Z_to_bv 64 (snd c)); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))].
Hypothesis RNG : Forall (fun c => 0x603000 <= fst c /\ fst c mod 4096 = 0 /\ 4096 <= snd c /\ fst c + snd c <= alloc_ceiling) cs.
Hypothesis DISJ : forall j k cj ck, nth_error cs j = Some cj -> nth_error cs k = Some ck -> j <> k ->
  fst cj + snd cj <= fst ck \/ fst ck + snd ck <= fst cj.
Hypothesis DISJPA : forall j c', nth_error cs j = Some c' -> PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= fst c' \/ fst c' + snd c' <= PA.
Hypothesis HV : 0 <= nf < 2^64 /\ 0 <= cur < 2^64 /\ 0 <= ga < 2^64 /\ 0 <= gm < 2^64.
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PARR : forall a n, PA <= a -> a + Z.of_nat n <= PA + 8 * Z.of_nat (length cs) -> P (Z_to_bv 64 a, n).
Hypothesis PHDR : forall j c' a n, nth_error cs j = Some c' -> fst c' <= a -> a + Z.of_nat n <= fst c' + 32 -> P (Z_to_bv 64 a, n).

Definition lastc : Z * Z := List.last cs c.
Definition cs' : list (Z * Z) := removelast (list_setn cs i lastc).

(* [comment removed for export] *)
Notation ldpreW usp :=
  [(usp - 32, usp); (0xaa7c0, 0xaa7c4); (0xaa590, 0xaa599); (0xaa5a8, 0xaa5b8); (0xaa7d8, 0xaa7e8);
   (PA + 8 * Z.of_nat i, PA + 8 * Z.of_nat i + 8); (fst lastc + 24, fst lastc + 32)].

(* [comment removed for export] *)
Notation ldAW usp :=
  [(usp - 32, usp); (0xaa7c0, 0xaa7c4); (0xaa590, 0xaa599); (0xaa5a8, 0xaa5b8); (PA + 8 * Z.of_nat i, PA + 8 * Z.of_nat i + 8)].

Lemma ldpre_A :
  (forall m1 (t1' : word),
     mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp - 32) -> wmono asegs m m1 ->
     munch (ldAW (bv_unsigned sp)) m m1 ->
     rw_cells asegs m1 (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells asegs m1 0xaa7c0 [C4 (Z_to_bv 64 1)] ->
     rw_cells asegs m1 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1)); C1 (Z_to_bv 8 0)] ->
     rw_cells asegs m1 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (nf + 1)); C8 (Z_to_bv 64 (cur - snd c)); C8 (Z_to_bv 64 mx)] ->
     rw_cells asegs m1 0xaa7d8 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)] ->
     u64arr asegs m1 PA (upd (gws cs junk) i (Z_to_bv 64 (fst lastc))) ->
     rw_cells asegs m1 (fst c) [C8 (Z_to_bv 64 (fst c)); C8 (Z_to_bv 64 (snd c)); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 (cur - snd c)) t1' t2 (Z_to_bv 64 (fst c)) s1
                            (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 (PA + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i))
                            (Z_to_bv 64 0xaa7d8) (Z_to_bv 64 (fst lastc)) (Z_to_bv 64 (0 - snd c)) (Z_to_bv 64 (snd c))
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x354e0) fc None m1 (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 (fst c + 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35424) fc None m (seg_rom asegs)).
Proof. aceil.
  intros CONT.
  aceil.
  pose proof (nth_error_lt _ _ _ NTH) as LT.
  pose proof (proj1 (Forall_forall _ _) RNG c (nth_error_In _ _ NTH)) as (R1 & R2 & R3 & R4). aceil.
  pose proof (DISJPA i c NTH) as PAC.
  assert (PHC : forall a n, fst c <= a -> a + Z.of_nat n <= fst c + 32 -> P (Z_to_bv 64 a, n)) by (intros; eapply PHDR; [exact NTH| lia| lia]).
  assert (LEN : (length (gws cs junk) = length cs + length junk)%nat) by (unfold gws; rewrite length_app, length_map; reflexivity).
  assert (MU : munch (ldAW (bv_unsigned sp)) m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 32%nat SK.
  do 5 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  replace (Z.land 4095 (fst c + 4096)) with 0.
  2:{ rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
      rewrite <- Zplus_mod_idemp_r, Z_mod_same_full, Z.add_0_r. symmetry. exact R2. }
  cstep.         (* [comment removed for export] *)
  do 4 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  do 4 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  replace (fst c + 4096 - 4096) with (fst c) by lia.
  cstep.         (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 (Z.of_nat i) 3) by lia.
  replace (PA + Z.of_nat i * 2 ^ 3) with (PA + 8 * Z.of_nat i) by lia.
  assert (NTHW : nth_error (gws cs junk) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (fst c))).
  { unfold gws. rewrite Nat2Z.id. rewrite nth_error_app1 by (rewrite length_map; exact LT). rewrite nth_error_map, NTH. reflexivity. }
  pose proof (u64arr_read asegs _ PA (gws cs junk) (Z.of_nat i) (Z_to_bv 64 (fst c)) (Z_to_bv 64 (PA + 8 * Z.of_nat i)) ARR NTHW ltac:(lia) ltac:(reflexivity)) as RD.
  zstepA. clear RD.  (* [comment removed for export] *)
  cstep.             (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA. zstepA.    (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CSNE : cs <> []) by (destruct cs; [cbn in LT; lia| discriminate]).
  assert (NTHL : nth_error cs (length cs - 1) = Some lastc).
  { unfold lastc. clear -CEILB CSNE. induction cs as [|x l IH]; [congruence|]. destruct l as [|y l']; [reflexivity|].
    cbn [length]. replace (S (S (length l')) - 1)%nat with (S (length (y :: l') - 1))%nat by (cbn; lia). cbn [nth_error].
    rewrite (IH ltac:(discriminate)). cbn. reflexivity. }
  assert (NTHWL : nth_error (gws cs junk) (Z.to_nat (Z.of_nat (length cs) - 1)) = Some (Z_to_bv 64 (fst lastc))).
  { unfold gws. rewrite nth_error_app1 by (rewrite length_map; lia). rewrite nth_error_map.
    replace (Z.to_nat (Z.of_nat (length cs) - 1)) with (length cs - 1)%nat by lia. rewrite NTHL. reflexivity. }
  rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length cs)) 3) by lia.
  replace (Z.of_nat (length cs) * 2 ^ 3 + PA) with (PA + 8 * Z.of_nat (length cs)) by lia.
  pose proof (u64arr_read asegs _ PA (gws cs junk) (Z.of_nat (length cs) - 1) (Z_to_bv 64 (fst lastc)) (Z_to_bv 64 (PA + 8 * Z.of_nat (length cs) + -8)) ARR NTHWL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. clear RD.  (* [comment removed for export] *)
  zstepA. zstepA.    (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA.            (* [comment removed for export] *)
  zstepA. zstepA.    (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok asegs mx PA (gws cs junk) (Z.of_nat i) (Z_to_bv 64 (PA + 8 * Z.of_nat i)) ARR ltac:(rewrite LEN; lia) ltac:(reflexivity)) as SOK;
    pose proof (u64arr_write asegs mx PA (gws cs junk) (Z.of_nat i) (Z_to_bv 64 (fst lastc)) ARR ltac:(rewrite LEN; lia)) as ARR' end.
  stepA.
  all: lazymatch goal with |- P _ => apply PARR; lia | _ => idtac end.
  clear ARR. store_done. rename ARR' into ARR.
  rewrite Nat2Z.id in ARR.
  eapply CONT; [exact MI| exact SK| exact WM| exact MU| exact FR| exact MTX| | | exact GST| exact ARR| exact HDRC].
  - replace (Z.of_nat (length cs) - 1) with (Z.of_nat (length cs) + -1) by lia. exact NRS.
  - exact SST.
Qed.

(* [comment removed for export] *)
Lemma ldpre_B2 : forall m1 (t1x : word) (w3l : word),
  (S i < length cs)%nat ->
  mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp - 32) ->
  rw_cells asegs m1 0xaa7c0 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m1 0xaa7d8 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)] ->
  rw_cells asegs m1 (fst c) [C8 (Z_to_bv 64 (fst c)); C8 (Z_to_bv 64 (snd c)); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
  rw_cells asegs m1 (fst lastc) [C8 (Z_to_bv 64 (fst lastc)); C8 (Z_to_bv 64 (snd lastc)); C8 w3l; C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1))] ->
  (forall m2 (a3' a4' a5' a6' a7' t1' : word),
     mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp - 32) -> wmono asegs m1 m2 ->
     munch [(0xaa7c0, 0xaa7c4); (0xaa7d8, 0xaa7e8); (fst lastc + 24, fst lastc + 32)] m1 m2 ->
     rw_cells asegs m2 0xaa7c0 [C4 (Z_to_bv 64 0)] ->
     rw_cells asegs m2 0xaa7d8 [C8 (Z_to_bv 64 (ga - snd c)); C8 (Z_to_bv 64 (gm - snd c))] ->
     rw_cells asegs m2 (fst c) [C8 (Z_to_bv 64 (fst c)); C8 (Z_to_bv 64 (snd c)); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
     rw_cells asegs m2 (fst lastc) [C8 (Z_to_bv 64 (fst lastc)); C8 (Z_to_bv 64 (snd lastc)); C8 w3l; C8 (Z_to_bv 64 (Z.of_nat i))] ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 (cur - snd c)) t1' t2 (Z_to_bv 64 (fst c)) (Z_to_bv 64 (fst c))
                            (Z_to_bv 64 (fst c)) (Z_to_bv 64 (snd c)) (Z_to_bv 64 0) a3' a4' a5' a6' a7'
                            (Z_to_bv 64 (snd c)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35514) fc None m2 (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 (cur - snd c)) t1x t2 (Z_to_bv 64 (fst c)) s1
                            (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 (PA + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i))
                            (Z_to_bv 64 0xaa7d8) (Z_to_bv 64 (fst lastc)) (Z_to_bv 64 (0 - snd c)) (Z_to_bv 64 (snd c))
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x354e0) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros m1 t1x w3l HSI MI1 SK1 MTX1 GST1 HDRC1 HDRL1 CONT.
  clear SK MI SEC NRS SST MTX GST ARR HDRC.
  aceil.
  pose proof (nth_error_lt _ _ _ NTH) as LT.
  pose proof (proj1 (Forall_forall _ _) RNG c (nth_error_In _ _ NTH)) as (R1 & R2 & R3 & R4). aceil.
  assert (CSNE : cs <> []) by (destruct cs; [cbn in LT; lia| discriminate]).
  assert (NTHL : nth_error cs (length cs - 1) = Some lastc).
  { unfold lastc. clear -CEILB CSNE. induction cs as [|x l IH]; [congruence|]. destruct l as [|y l']; [reflexivity|].
    cbn [length]. replace (S (S (length l')) - 1)%nat with (S (length (y :: l') - 1))%nat by (cbn; lia). cbn [nth_error].
    rewrite (IH ltac:(discriminate)). cbn. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) RNG lastc (nth_error_In _ _ NTHL)) as (L1 & L2 & L3 & L4). aceil.
  pose proof (DISJ i (length cs - 1)%nat c lastc NTH NTHL ltac:(lia)) as DCL.
  assert (PHC : forall a n, fst c <= a -> a + Z.of_nat n <= fst c + 32 -> P (Z_to_bv 64 a, n)) by (intros; eapply PHDR; [exact NTH| lia| lia]).
  assert (PHL : forall a n, fst lastc <= a -> a + Z.of_nat n <= fst lastc + 32 -> P (Z_to_bv 64 a, n)) by (intros; eapply PHDR; [exact NTHL| lia| lia]).
  clear PHDR.
  assert (MU : munch [(0xaa7c0, 0xaa7c4); (0xaa7d8, 0xaa7e8); (fst lastc + 24, fst lastc + 32)] m1 m1) by apply munch_refl.
  assert (WM : wmono asegs m1 m1) by apply wmono_refl.
  zstepA.   (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTXB : rw_cells asegs mx 0xaa7c0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)])
      by (eapply rw_cells_reshape; [| | exact MTX1]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTX1.
  zstepA.   (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTX' : rw_cells asegs mx 0xaa7c0 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_reshape; [| | exact MTXB]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTXB.
  do 5 zstepA. (* [comment removed for export] *)
  replace (ga + (0 - snd c)) with (ga - snd c) in GST1 by lia.
  replace (gm + (0 - snd c)) with (gm - snd c) in GST1 by lia.
  eapply CONT; [exact MI1| exact SK1| exact WM| exact MU| exact MTX'| exact GST1| exact HDRC1| exact HDRL1].
Qed.
(* [comment removed for export] *)
Lemma ldpre_B1 : forall m1 (t1x : word),
  (S i = length cs)%nat ->
  mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp - 32) ->
  rw_cells asegs m1 0xaa7c0 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m1 0xaa7d8 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)] ->
  rw_cells asegs m1 (fst c) [C8 (Z_to_bv 64 (fst c)); C8 (Z_to_bv 64 (snd c)); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
  (forall m2 (a3' a4' a5' a6' a7' t1' : word),
     mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp - 32) -> wmono asegs m1 m2 ->
     munch [(0xaa7c0, 0xaa7c4); (0xaa7d8, 0xaa7e8); (fst c + 24, fst c + 32)] m1 m2 ->
     rw_cells asegs m2 0xaa7c0 [C4 (Z_to_bv 64 0)] ->
     rw_cells asegs m2 0xaa7d8 [C8 (Z_to_bv 64 (ga - snd c)); C8 (Z_to_bv 64 (gm - snd c))] ->
     rw_cells asegs m2 (fst c) [C8 (Z_to_bv 64 (fst c)); C8 (Z_to_bv 64 (snd c)); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 (cur - snd c)) t1' t2 (Z_to_bv 64 (fst c)) (Z_to_bv 64 (fst c))
                            (Z_to_bv 64 (fst c)) (Z_to_bv 64 (snd c)) (Z_to_bv 64 0) a3' a4' a5' a6' a7'
                            (Z_to_bv 64 (snd c)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35514) fc None m2 (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 (cur - snd c)) t1x t2 (Z_to_bv 64 (fst c)) s1
                            (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 (PA + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i))
                            (Z_to_bv 64 0xaa7d8) (Z_to_bv 64 (fst c)) (Z_to_bv 64 (0 - snd c)) (Z_to_bv 64 (snd c))
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x354e0) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros m1 t1x HSI MI1 SK1 MTX1 GST1 HDRC1 CONT.
  clear SK MI SEC NRS SST MTX GST ARR HDRC.
  aceil.
  pose proof (nth_error_lt _ _ _ NTH) as LT.
  pose proof (proj1 (Forall_forall _ _) RNG c (nth_error_In _ _ NTH)) as (R1 & R2 & R3 & R4). aceil.
  assert (CSNE : cs <> []) by (destruct cs; [cbn in LT; lia| discriminate]).
  assert (NTHL : nth_error cs (length cs - 1) = Some lastc).
  { unfold lastc. clear -CEILB CSNE. induction cs as [|x l IH]; [congruence|]. destruct l as [|y l']; [reflexivity|].
    cbn [length]. replace (S (S (length l')) - 1)%nat with (S (length (y :: l') - 1))%nat by (cbn; lia). cbn [nth_error].
    rewrite (IH ltac:(discriminate)). cbn. reflexivity. }
  assert (PHC : forall a n, fst c <= a -> a + Z.of_nat n <= fst c + 32 -> P (Z_to_bv 64 a, n)) by (intros; eapply PHDR; [exact NTH| lia| lia]).
  clear PHDR.
  assert (MU : munch [(0xaa7c0, 0xaa7c4); (0xaa7d8, 0xaa7e8); (fst c + 24, fst c + 32)] m1 m1) by apply munch_refl.
  assert (WM : wmono asegs m1 m1) by apply wmono_refl.
  zstepA.   (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  zstepA.   (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTXB : rw_cells asegs mx 0xaa7c0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)])
      by (eapply rw_cells_reshape; [| | exact MTX1]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTX1.
  zstepA.   (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTX' : rw_cells asegs mx 0xaa7c0 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_reshape; [| | exact MTXB]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTXB.
  do 5 zstepA. (* [comment removed for export] *)
  replace (ga + (0 - snd c)) with (ga - snd c) in GST1 by lia.
  replace (gm + (0 - snd c)) with (gm - snd c) in GST1 by lia.
  eapply CONT; [exact MI1| exact SK1| exact WM| exact MU| exact MTX'| exact GST1| exact HDRC1].
Qed.
End LDPRE.
End RC__1.
