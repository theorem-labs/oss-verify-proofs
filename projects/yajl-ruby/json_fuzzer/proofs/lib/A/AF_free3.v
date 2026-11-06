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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_free_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

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
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section DRAIN.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo T : Z) (cnt first last qb gcnt gfirst glast gqb qmin : Z).
Notation INST := 0xaa518.

Hypothesis SK : stk asegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv asegs m.
Hypothesis HT : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
Hypothesis QMTX : rw_cells asegs m 0xaa888 [C4 (Z_to_bv 64 0)].                       (* [comment removed for export] *)
Hypothesis GQ : rw_cells asegs m 0xaa890 [C8 (Z_to_bv 64 gcnt); C8 (Z_to_bv 64 gfirst); C8 (Z_to_bv 64 glast); C8 (Z_to_bv 64 gqb)].
Hypothesis QMAX : rw_cells asegs m 0xaa830 [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 qmin); C8 (Z_to_bv 64 0x100000)].
Hypothesis QC : rw_cells asegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)].
Hypothesis HCNT : 0 < cnt /\ 0 <= gcnt /\ gcnt + cnt < 2^63.
Hypothesis HQB : 0 <= qb /\ 0 <= gqb /\ gqb + qb < 2^63.
Hypothesis HGL : gcnt <> 0 -> kHighMemBeg <= glast /\ glast + 8192 <= alloc_ceiling /\ (glast + 8192 <= T \/ T + 4096 <= glast).
Hypothesis GLB : gcnt <> 0 -> rw_cells asegs m glast [C8 (Z_to_bv 64 0)].            (* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PGLB : gcnt <> 0 -> forall a k, glast <= a -> a + Z.of_nat k <= glast + 8192 -> P (Z_to_bv 64 a, k).

Definition gfirst' : Z := if gcnt =? 0 then first else gfirst.
Definition drainW : list (Z * Z) := [(bv_unsigned sp - 48, bv_unsigned sp); (0xaa888, 0xaa88c); (0xaa890, 0xaa8b0); (T + 80, T + 112)] ++ (if gcnt =? 0 then [] else [(glast, glast + 8)]).

(* [comment removed for export] *)
Lemma drain_walk :
  (forall m' (a1' a4' a5' a6' a7' t0' t1' : word),
     mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> wmono asegs m m' -> munch drainW m m' ->
     rw_cells asegs m' 0xaa888 [C4 (Z_to_bv 64 0)] ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (gcnt + cnt)); C8 (Z_to_bv 64 gfirst'); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 (gqb + qb))] ->
     rw_cells asegs m' (T + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
     (gcnt <> 0 -> rw_cells asegs m' glast [C8 (Z_to_bv 64 first)]) ->
     gqb + qb <= 0x10000000 ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (INST + 728)) a1' a2 a3 a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (forall m' (a4' a5' a6' a7' t0' t1' : word),
     mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> wmono asegs m m' -> munch drainW m m' ->
     rw_cells asegs m' 0xaa888 [C4 (Z_to_bv 64 256)] ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (gcnt + cnt)); C8 (Z_to_bv 64 gfirst'); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 (gqb + qb))] ->
     rw_cells asegs m' (T + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
     (gcnt <> 0 -> rw_cells asegs m' glast [C8 (Z_to_bv 64 first)]) ->
     0x10000000 < gqb + qb ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 qmin) a2 a3 a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x349b8) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80)) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34814) fc None m (seg_rom asegs)).
Proof. aceil.
  intros CONT1 CONT2.
  pose proof LOC as LOC0. aceil. rewrite kHighMemBeg_val in HGL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  unfold drainW, gfirst' in CONT1, CONT2.
  (* [comment removed for export] *)
  destruct (Z.eqb_spec gcnt 0) as [G0|G1].
  - clear HGL GLB PGLB.
    assert (MU : munch ([(bv_unsigned sp - 48, bv_unsigned sp); (0xaa888, 0xaa88c); (0xaa890, 0xaa8b0); (T + 80, T + 112)] ++ []) m m) by apply munch_refl.
    cbn [app] in MU, CONT1, CONT2.
    carve_frame 48%nat SK.
    frame_stores 6 FR. (* [comment removed for export] *)
    do 4 zstepA. (* [comment removed for export] *)
    replace (Z.land (697624 + 728 + 152) 18446744073709551612) with 698504 by reflexivity.
    zstepA. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    do 4 zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1.
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?unsigned_lit by lia; lia]. clear K2.
    (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. zstepA. zstepA. (* [comment removed for export] *)
    zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (QMB : rw_cells asegs mx 0xaa888 [C1 (Z_to_bv 8 1); C1 zb0; C2 (Z_to_bv 64 0)])
        by (eapply rw_cells_reshape; [| | exact QMTX]; [cells_wf_triv| vm_compute; reflexivity]) end.
    clear QMTX.
    zstepA. (* [comment removed for export] *)
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (QMTX : rw_cells asegs mx 0xaa888 [C4 (Z_to_bv 64 0)])
        by (eapply rw_cells_reshape; [| | exact QMB]; [cells_wf_triv| vm_compute; reflexivity]) end.
    clear QMB.
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. if_cases KR; zify_cond KR.
    + (* [comment removed for export] *)
      do 6 zstepA. (* [comment removed for export] *)
      release_frame FR SK (bv_unsigned sp).
      zstepA. (* [comment removed for export] *)
      eapply CONT1; [exact MI| exact SK| exact WM| exact MU| exact QMTX| rewrite G0; exact GQ| exact QC| intros X; exfalso; exact (X G0)
        | revert KR; rewrite ?unsigned_lit by lia; intros KR; lia].
    + (* [comment removed for export] *)
      do 8 zstepA. (* [comment removed for export] *)
      change (bv_swrap 32 65280) with 65280. change (bv_swrap 32 256) with 256.
      replace (Z.land (697624 + 728 + 153) 18446744073709551612) with 698504 by reflexivity.
      zstepA. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
      do 4 zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      cstep. (* [comment removed for export] *)
      zstepA. zstepA. (* [comment removed for export] *)
      cstep. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      do 6 zstepA. (* [comment removed for export] *)
      release_frame FR SK (bv_unsigned sp).
      zstepA. (* [comment removed for export] *)
      eapply CONT2; [exact MI| exact SK| exact WM| exact MU| exact QMTX| rewrite G0; exact GQ| exact QC| intros X; exfalso; exact (X G0)
        | revert KR; rewrite ?unsigned_lit by lia; intros KR; lia].
  - specialize (HGL G1). specialize (GLB G1). specialize (PGLB G1).
    assert (MU : munch ([(bv_unsigned sp - 48, bv_unsigned sp); (0xaa888, 0xaa88c); (0xaa890, 0xaa8b0); (T + 80, T + 112)] ++ [(glast, glast + 8)]) m m) by apply munch_refl.
    cbn [app] in MU, CONT1, CONT2.
    carve_frame 48%nat SK.
    frame_stores 6 FR. (* [comment removed for export] *)
    do 4 zstepA. (* [comment removed for export] *)
    replace (Z.land (697624 + 728 + 152) 18446744073709551612) with 698504 by reflexivity.
    zstepA. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    do 4 zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1.
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. } clear K2.
    (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. zstepA. zstepA. (* [comment removed for export] *)
    zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (QMB : rw_cells asegs mx 0xaa888 [C1 (Z_to_bv 8 1); C1 zb0; C2 (Z_to_bv 64 0)])
        by (eapply rw_cells_reshape; [| | exact QMTX]; [cells_wf_triv| vm_compute; reflexivity]) end.
    clear QMTX.
    zstepA. (* [comment removed for export] *)
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (QMTX : rw_cells asegs mx 0xaa888 [C4 (Z_to_bv 64 0)])
        by (eapply rw_cells_reshape; [| | exact QMB]; [cells_wf_triv| vm_compute; reflexivity]) end.
    clear QMB.
    zstepA. zstepA. (* [comment removed for export] *)
    replace (gcnt =? 0) with false in CONT1, CONT2 by (symmetry; apply Z.eqb_neq; exact G1).
    zstepA. if_cases KR; zify_cond KR.
    + do 6 zstepA. release_frame FR SK (bv_unsigned sp). zstepA.
      eapply CONT1; [exact MI| exact SK| exact WM| exact MU| exact QMTX| exact GQ| exact QC| intros _; exact GLB
        | revert KR; rewrite ?unsigned_lit by lia; intros KR; lia].
    + do 8 zstepA.
      change (bv_swrap 32 65280) with 65280. change (bv_swrap 32 256) with 256.
      replace (Z.land (697624 + 728 + 153) 18446744073709551612) with 698504 by reflexivity.
      zstepA. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
      do 4 zstepA. zstepA. cstep. zstepA. zstepA. cstep.
      zstepA. do 6 zstepA. release_frame FR SK (bv_unsigned sp). zstepA.
      eapply CONT2; [exact MI| exact SK| exact WM| exact MU| exact QMTX| exact GQ| exact QC| intros _; exact GLB
        | revert KR; rewrite ?unsigned_lit by lia; intros KR; lia].
Qed.
End DRAIN.
End RC__1.
