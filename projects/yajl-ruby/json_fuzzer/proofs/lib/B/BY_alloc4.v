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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BI_globals2 BI_region_is_poisoned BI_asan_memset BYajlRep BYajl_iface BY_hand BY_alloc1 BY_alloc2 BY_alloc3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AAL_RET7 : Z := 0x8269c.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma aal7_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9v : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff lo H CBK CFGP CX L D : Z) (pew pad DBJ SBK SZ U YF : word) (shH wsS : list byte),
  stk bsegs m1 lo SQ -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 2224 <= SQ -> SQ + 192 <= 2^47 ->
  rw_cells bsegs m1 H (hcells15 CBK CX L pew (Z_to_bv 64 0) pad DBJ SBK SZ U YF) ->
  u8arr bsegs m1 (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 -> 0 <= ff < 2^47 -> 0 <= D < 2^64 ->
  shadow_window bsegs m1 2147450880 (H + 48) 16 wsS -> range_clean 2147450880 (H + 48) 16 wsS -> shw_hi 2147450880 (H + 48) 16 <= 17594333495296 ->
  icp_globals bsegs m1 2147450880 ->
  pol P lo (SQ + 56) -> pol P 0x10000 0x603000 ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) -> pol P (shw_lo 2147450880 (H + 48)) (shw_hi 2147450880 (H + 48) 16) ->
  evtA bsegs P (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAL_RET7) (Z_to_bv 64 SQ) gp tp t0' t1' t2' sp (Z_to_bv 64 SQ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 128) (Z_to_bv 64 AY_REALLOC_W) a4' a5' a6' a7'
                   (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (H + 48)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (H + 60)) (Z_to_bv 64 (H + 96))
                   (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3' t4' t5' t6')
               F (Z_to_bv 64 AY_REALLOC_W) fc None m' (seg_rom bsegs)
      /\ munch [(SQ - 2224, SQ); (H, H + 104)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SQ
      /\ rw_cells bsegs m' H (hcells15 CBK CX L pew (Z_to_bv 64 0) pad (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 128) (Z_to_bv 64 0) (Z_to_bv 64 (H + 72)))
      /\ u8arr bsegs m' (2147450880 + H / 8) shH /\ icp_globals bsegs m' 2147450880)
    (MS (mkR (Z_to_bv 64 AAL_RET5) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) (Z_to_bv 64 (H + 72)) s9v (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_RET5) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until wsS. intros ST MI CEIL LOQ SQH HC HS HSeq HR1 HR2 H16 FFR DR SWS RCS WSH IG PSTK PIMG PH PHS PWS.
  unfold pol, AAL_RET5, AAL_RET7, AY_REALLOC_W, hcells15, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  assert (H8 : H mod 8 = 0) by lia.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (SHHR : 2147450880 <= 2147450880 + H / 8 /\ 2147450880 + H / 8 + 13 <= 17594333495296) by (clear -CEILB HR1 HR2; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SQ - 2224, SQ); (H, H + 104)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 40) 8.                      (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 48) 8.                      (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 56) 4.                      (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 60) 4.                      (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 64) 8.                      (* [comment removed for export] *)
  stepA. zstepA.                                          (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  ugd. zstepA. ugd.                                       (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 80) 8.                      (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 96) 8.                      (* [comment removed for export] *)
  zstepA. zstepA. stepA.                                  (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  shadow_addr.
  apply evtA_done. lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _ m', MS _ _ _ _ _ ?mx _ = _ /\ _ =>
    eexists _, _, _, _, _, _, _, _, _, _, _, mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  split; [lazymatch goal with H1 : rw_cells bsegs _ H _ |- _ => exact H1 end|].
  split; [assumption|].
  eapply icp_globals_transport; [exact IG| exact MU| exact WM| cbv [disjoint_from fst snd]; lia].
Qed.
End RC__2.
