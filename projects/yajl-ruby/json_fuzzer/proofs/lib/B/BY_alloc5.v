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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BYajlRep BYajl_iface BY_hand BY_alloc1 BY_alloc2 BY_alloc3 BY_alloc4.
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
Definition AAL_EPI : Z := 0x8273c.    (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma aal8_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff H CBK CX L D NS : Z) (nj : list byte) (pew pad : word) (shH shN : list byte),
  mem_inv bsegs m1 -> alloc_ceiling <= SQ -> SQ + 192 <= 2^47 ->
  rw_cells bsegs m1 H (hcells15 CBK CX L pew (Z_to_bv 64 0) pad (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 128) (Z_to_bv 64 0) (Z_to_bv 64 (H + 72))) ->
  u8arr bsegs m1 (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 ->
  rw_cells bsegs m1 NS [CB 128 nj] -> u8arr bsegs m1 (2147450880 + NS / 8) shN -> shN = blk_shadow 128 ->
  17594333495296 <= NS -> NS + 128 <= alloc_ceiling -> NS mod 16 = 0 -> (NS + 128 <= H \/ H + 104 <= NS) ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) ->
  pol P NS (NS + 128) -> pol P (2147450880 + NS / 8) (2147450880 + NS / 8 + 16) ->
  evtA bsegs P (fun ms' => exists (a0' a1' a2' a3' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAL_RET7) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0' a1' a2' a3' a4 a5 a6 a7
                   (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (H + 48)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (H + 60)) (Z_to_bv 64 (H + 96))
                   (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
               F (Z_to_bv 64 AAL_EPI) fc None m' (seg_rom bsegs)
      /\ munch [(H, H + 104); (NS, NS + 128)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' H (hcells15 CBK CX L pew (Z_to_bv 64 0) pad (Z_to_bv 64 D) (Z_to_bv 64 NS) (Z_to_bv 64 128) (Z_to_bv 64 1) (Z_to_bv 64 (H + 72)))
      /\ u8arr bsegs m' NS (upd nj 0 (Z_to_bv 8 0))
      /\ u8arr bsegs m' (2147450880 + H / 8) shH /\ u8arr bsegs m' (2147450880 + NS / 8) shN)
    (MS (mkR (Z_to_bv 64 AAL_RET7) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 NS) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (H + 48)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (H + 60)) (Z_to_bv 64 (H + 96))
             (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_RET7) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until shN. intros MI SQL SQH HC HS HSeq HR1 HR2 H16 NC NSH NSeq NR1 NR2 N16 SEPNH PH PHS PN PNS.
  unfold pol, AAL_RET7, AAL_EPI, hcells15, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  pose proof (blk_shadow_length 128 ltac:(lia)) as NSlen. rewrite <- NSeq in NSlen.
  assert (H8 : H mod 8 = 0) by lia. assert (N8 : NS mod 8 = 0) by lia.
  assert (LNJ : length nj = 128%nat) by (destruct NC as [[WF _] _]; cbn in WF; tauto).
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (SHHR : 2147450880 <= 2147450880 + H / 8 /\ 2147450880 + H / 8 + 13 <= 17594333495296) by (clear -CEILB HR1 HR2; Z.div_mod_to_equations; lia).
  assert (SHNR : 2147450880 <= 2147450880 + NS / 8 /\ 2147450880 + NS / 8 + 16 <= 17594333495296) by (clear -CEILB NR1 NR2; Z.div_mod_to_equations; lia).
  pose proof (u8arr_of_rw_cells bsegs _ _ _ _ NC) as ARR. clear NC.
  pose proof (munch_refl [(H, H + 104); (NS, NS + 128)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + 48) 8 ltac:(lia) ltac:(lia) ltac:(rewrite <- HSeq; assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear -CEILB H8; Z.div_mod_to_equations; lia)) as HR end.
  replace (2147450880 + (H + 48) / 8) with ((H + 48) / 8 + 2147450880) in HR by lia.
  zstepA. clear HR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
  zstepA. if_false.                                       (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + 48) 8 ltac:(lia) ltac:(lia) ltac:(rewrite <- HSeq; assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear -CEILB H8; Z.div_mod_to_equations; lia)) as HR end.
  replace (2147450880 + (H + 48) / 8) with ((H + 48) / 8 + 2147450880) in HR by lia.
  zstepA. clear HR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
  zstepA. if_false.                                       (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + 60) 4 ltac:(lia) ltac:(lia) ltac:(rewrite <- HSeq; assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear -CEILB H8; Z.div_mod_to_equations; lia)) as HR end.
  replace (2147450880 + (H + 60) / 8) with ((H + 60) / 8 + 2147450880) in HR by lia.
  zstepA. clear HR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_false.                                       (* [comment removed for export] *)
  zstepA. rewrite ?yzx32_small, ?ysx32_small by lia.      (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  replace (NS + 0) with NS by lia.
  ugd. zstepA. zstepA. zstepA. ugd. ugd.                  (* [comment removed for export] *)
  assert (G8 : NS mod 8 + 1 <= 8) by (clear -CEILB N8; Z.div_mod_to_equations; lia).
  shadow_fast NSH NS 1.                                   (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at bsegs mx NS _ 0 ARR ltac:(lia)) as SOK end.
  stepA.                                                  (* [comment removed for export] *)
  lazymatch type of ARR with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write bsegs mx NS _ 0 (Z_to_bv 8 0) ARR ltac:(lia)) as ARR' end.
  rewrite le1_wz by lia. clear ARR. store_done.
  stepA.                                                  (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with |- exists _ _ _ _ m', MS _ _ _ _ _ ?mx _ = _ /\ _ => eexists _, _, _, _, mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H2 : rw_cells bsegs _ H _ |- _ => exact H2 end|].
  split; [replace (NS + 0) with NS in ARR' by lia; exact ARR'|].
  split; assumption.
Qed.
End RC__2.
