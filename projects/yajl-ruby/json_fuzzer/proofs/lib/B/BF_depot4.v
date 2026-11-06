(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA MmStep AImages AImageFacts LazyModel NodesA ImplRzA NodesA_mm.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_lalloc1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
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
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition a_mmap_nrdie : Z := 0x67630.     (* [comment removed for export] *)
Definition a_mmap_die : Z := 0x670f8.       (* [comment removed for export] *)
Definition a_report_spin : Z := 0x612a4.
Definition MAP_ANON_NR : Z := 16418.        (* [comment removed for export] *)

Section X.
Variable P : acc -> Prop.
Hypothesis PDATA : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Definition die_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : Z) (lo : Z) (m : mem) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool), R a r u /\
    (if u then exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (bv_unsigned r, bv_unsigned r + L)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp) /\ statics m'
      /\ rw_cells bsegs m' (bv_unsigned r) [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
     else exists R' m', ms' = MS R' F (Z_to_bv 64 a_report_spin) fc None m' (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_nrdie_specA : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (L : Z) (lo : Z),
  mod_dec_ok dec R L lo ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 320 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> statics m ->
  a0 = Z_to_bv 64 L -> bv_unsigned a1 <> 0 ->
  L mod 4096 = 0 -> 0 < L -> L <= 2^40 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  implA bsegs (at_nodeA bsegs) P (enode (NMmap 0 L 3 MAP_ANON_NR) dec)
       (epost (die_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 a_mmap_nrdie) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until lo. intros DEC ST LOC LO SPH MI STA -> NAME LA L0 L40 PSTK. unfold a_mmap_nrdie, MAP_ANON_NR.
  pose proof LOC as LOC'. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  open_statics STA.
  apply implA_enode.
  carve_frame 48%nat ST.
  do 5 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  do 2 stepA.                                   (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA. if_true.                              (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA.               (* [comment removed for export] *)
  rewrite land_m4096_up by lia.
  zstepA. zstepA. stepA.                        (* [comment removed for export] *)
  do 3 stepA.                                   (* [comment removed for export] *)
  stepA. call_spA (named_fd_specA P PDATA); [exact ST| exact LOC'| lia| exact MI| close_statics| exact NAME| intros; apply PSTK; lia|].
  rename PC into ST. clear G1 G2 G3 V1 V2 V3 V4. lazymatch goal with H : statics _ |- _ => rename H into STA end.
  ret_pc_lit.
  zstepA.                                       (* [comment removed for export] *)
  do 5 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  step_ecallA.
  split. { at_nodeA_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & -> & SIDE). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  open_statics STA.
  destruct u.
  - (* [comment removed for export] *)
    destruct SIDE as [RLO RHI]. unfold b_image_end in RLO.
    assert (ROF : forall xw : word, (bv_unsigned r <= bv_unsigned xw < bv_unsigned r + L)%Z -> ro_addr bsegs xw = false)
      by (intros xw Hxw; apply both_ro_addr_false; lia).
    lazymatch goal with |- context [MSsvc _ _ _ _ _ _ ?mx _] =>
      assert (MU' : munch [(bv_unsigned sp - 320, bv_unsigned sp); (bv_unsigned r, bv_unsigned r + L)] m mx)
        by (eapply munch_weaken; [| exact MU]; intros y Hy; cbn in Hy |- *; lia) end.
    clear MU. rename MU' into MU.
    unfold ashape. cbv iota. rewrite <- (Z_to_bv_lit_self r). sys_nret.
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K; zify_cond K; [| exfalso; revert K; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia].
    zstepA.                                     (* [comment removed for export] *)
    replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    stepA.                                      (* [comment removed for export] *)
    zstepA. if_false.                           (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    stepA. callA (itm_walk P PDATA); [lazymatch goal with H : mem_inv _ ?mm |- mem_inv _ ?mm => exact H end| close_statics|].
    stepA.                                      (* [comment removed for export] *)
    do 5 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rewrite ?(Z_to_bv_lit_self r).
    lazymatch goal with |- evtA _ _ _ (MS ?Rg ?Fg ?pc ?fcg _ ?mm _) =>
      apply evtA_done; unfold die_post; exists r, true; split; [exact HR|]; do 14 eexists; exists mm end.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [close_statics| exact ZNEW].
  - (* [comment removed for export] *)
    subst r. unfold ashape. cbv iota. sys_nret.
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by lia; lia|].   (* [comment removed for export] *)
    zstepA. if_true.                            (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? 18446744073709551604)) with 1 by reflexivity.
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; lia|].
    zstepA. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?unsigned_lit by lia; lia|].   (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? 18446744073709551604)) with 1 by reflexivity.
    stepA.                                      (* [comment removed for export] *)
    zstepA. if_true.                            (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    zstepA. zstepA. stepA. stepA. zstepA.       (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    clear FR. carve_frame 48%nat ST.
    do 6 stepA.                                 (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_false.                           (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_false.                           (* [comment removed for export] *)
    apply evtA_done. unfold die_post. exists (Z_to_bv 64 (2^64 - 12)), false. split; [exact HR|]. eexists _, _. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_die_specA : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (L : Z) (lo : Z),
  mod_dec_ok dec R L lo ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 320 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> statics m ->
  a0 = Z_to_bv 64 L -> bv_unsigned a1 <> 0 -> a2 = Z_to_bv 64 0 ->
  L mod 4096 = 0 -> 0 < L -> L <= 2^40 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  implA bsegs (at_nodeA bsegs) P (enode (NMmap 0 L 3 MAP_ANON_RW) dec)
       (epost (die_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 a_mmap_die) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until lo. intros DEC ST LOC LO SPH MI STA -> NAME -> LA L0 L40 PSTK. unfold a_mmap_die, MAP_ANON_RW.
  pose proof LOC as LOC'. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  open_statics STA.
  apply implA_enode.
  carve_frame 48%nat ST.
  do 6 stepA.                                   (* [comment removed for export] *)
  stepA. stepA.                                 (* [comment removed for export] *)
  do 2 stepA.                                   (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA. if_true.                              (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA.               (* [comment removed for export] *)
  rewrite land_m4096_up by lia.
  stepA. stepA.                                 (* [comment removed for export] *)
  do 3 stepA.                                   (* [comment removed for export] *)
  stepA. call_spA (named_fd_specA P PDATA); [exact ST| exact LOC'| lia| exact MI| close_statics| exact NAME| intros; apply PSTK; lia|].
  rename PC into ST. clear G1 G2 G3 V1 V2 V3 V4. lazymatch goal with H : statics _ |- _ => rename H into STA end.
  ret_pc_lit.
  zstepA.                                       (* [comment removed for export] *)
  do 5 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  step_ecallA.
  split. { at_nodeA_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & -> & SIDE). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  open_statics STA.
  destruct u.
  - (* [comment removed for export] *)
    destruct SIDE as [RLO RHI]. unfold b_image_end in RLO.
    assert (ROF : forall xw : word, (bv_unsigned r <= bv_unsigned xw < bv_unsigned r + L)%Z -> ro_addr bsegs xw = false)
      by (intros xw Hxw; apply both_ro_addr_false; lia).
    lazymatch goal with |- context [MSsvc _ _ _ _ _ _ ?mx _] =>
      assert (MU' : munch [(bv_unsigned sp - 320, bv_unsigned sp); (bv_unsigned r, bv_unsigned r + L)] m mx)
        by (eapply munch_weaken; [| exact MU]; intros y Hy; cbn in Hy |- *; lia) end.
    clear MU. rename MU' into MU.
    unfold ashape. cbv iota. rewrite <- (Z_to_bv_lit_self r). sys_nret.
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K; zify_cond K; [| exfalso; revert K; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia].
    zstepA.                                     (* [comment removed for export] *)
    replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    stepA.                                      (* [comment removed for export] *)
    zstepA. if_false.                           (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    stepA. callA (itm_walk P PDATA); [lazymatch goal with H : mem_inv _ ?mm |- mem_inv _ ?mm => exact H end| close_statics|].
    stepA.                                      (* [comment removed for export] *)
    do 6 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rewrite ?(Z_to_bv_lit_self r).
    lazymatch goal with |- evtA _ _ _ (MS ?Rg ?Fg ?pc ?fcg _ ?mm _) =>
      apply evtA_done; unfold die_post; exists r, true; split; [exact HR|]; do 14 eexists; exists mm end.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [close_statics| exact ZNEW].
  - (* [comment removed for export] *)
    subst r. unfold ashape. cbv iota. sys_nret.
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by lia; lia|].   (* [comment removed for export] *)
    zstepA. if_true.                            (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? 18446744073709551604)) with 1 by reflexivity.
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    do 2 stepA.                                 (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; lia|].
    zstepA. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?unsigned_lit by lia; lia|].   (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? 18446744073709551604)) with 1 by reflexivity.
    stepA.                                      (* [comment removed for export] *)
    zstepA. if_true.                            (* [comment removed for export] *)
    zstepA.                                     (* [comment removed for export] *)
    zstepA. zstepA. stepA. stepA. stepA.        (* [comment removed for export] *)
    stepA.                                      (* [comment removed for export] *)
    clear FR. carve_frame 48%nat ST.
    do 6 stepA.                                 (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_false.                           (* [comment removed for export] *)
    zstepA. zstepA.                             (* [comment removed for export] *)
    zstepA. if_false.                           (* [comment removed for export] *)
    apply evtA_done. unfold die_post. exists (Z_to_bv 64 (2^64 - 12)), false. split; [exact HR|]. eexists _, _. reflexivity.
Qed.

End X.
End RC__1.
