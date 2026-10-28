(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit F_aunwind.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation unwind_impl_W sp S t :=
  ([(bv_unsigned sp - 160, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056); (S + 2056, S + 2064); (t + 3168, t + 3169)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Lemma unwind_fast_spec0 : forall RNG (raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp top bot lo : Z) (tb : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= S ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 top -> a4 = Z_to_bv 64 bot -> a5 = Z_to_bv 64 30 ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (exists szj, rw_cells bsegs m (S + 8) [C4 szj]) -> u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  0 <= bot -> bot < bp -> top - 16 <= bp -> bot < top -> 4096 <= top <= 2^47 -> bp < 2^47 -> S + 2072 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bp - lo) ->
  evtF bsegs RNG (unwind_fast_post S pc top sp raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo tb [] m)
    (MS (mkR raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x753d4) fc None m (seg_rom bsegs)).
Proof.
  intros until tb. intros ST CEIL LO SPS MI -> -> -> -> -> -> GPG PG [szj SZC] TB LTB B0 BB BT BT2 TOP BP47 SB PC RIMG RR.
  unfold GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. do 3 zstep.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 3 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok bsegs mm (S + 16) tb 0 (wa (S + 16)) TB ltac:(lia) ltac:(f_equal; lia)) as SOK end.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u64arr_write bsegs mm (S + 16) tb 0 (Z_to_bv 64 pc) TB ltac:(lia)) as TB2;
    rewrite Z.mul_0_r, Z.add_0_r in TB2 end.
  clear TB. store_done. rename TB2 into TB. cbn [Z.to_nat upd] in TB.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
  step. if_cases K1; zify_cond K1. { exfalso. lia. }     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. step. if_cases K3; zify_cond K3. 2: { exfalso. lia. }   (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_fast_post.
  do 6 eexists. eexists. exists (upd tb 0 (Z_to_bv 64 pc)). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [cbn [length]; exact SZC|]. split; [exact TB|]. split; [rewrite upd_length; exact LTB|].
  destruct tb as [|w0 tb0]; [cbn in LTB; lia|]. cbn [upd firstn map length]. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma unwind_impl_spec0 : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp ctx t top bot lo : Z) (tb : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= S ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 30 ->
  (* [comment removed for export] *)
  rw_cells bsegs m AINITED [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  (exists szj, rw_cells bsegs m (S + 8) [C4 szj]) -> u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  (exists bpj, rw_cells bsegs m (S + 2056) [C8 bpj]) ->
  (* [comment removed for export] *)
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  0 <= bot -> bot < bp -> top - 16 <= bp -> bot < top -> 4096 <= top <= 2^47 -> bp < 2^47 -> S + 2080 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (unwind_impl_post S pc bp t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [] m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5c91c) fc None m (seg_rom bsegs)).
Proof.
  intros until tb. intros ST CEIL LO SPS MI TP -> -> -> -> -> -> INI TI TK T88 TSD CT GPG PG TT SW UW [szj SZC] TB LTB [bpj BPJ]
         C0 C1 T0 T1 CT2 B0 BB BT BT2 TOP BP47 SB PC RIMG RR RCTX RT. unfold sclr, iclr, KLS, AIMG_LO in *.   (* [comment removed for export] *)
  unfold AIMG_HI, AINITED, ATSDI, ATSDK, ATP88, ATSD, GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl (unwind_impl_W sp S t) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.        (* [comment removed for export] *)
  box RT.   (* [comment removed for export] *)
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI end.
  step. if_cases K; zify_cond K; [exfalso; lia|].     (* [comment removed for export] *)
  zstep. lstep. step. step.                           (* [comment removed for export] *)
  step. if_lit.                                       (* [comment removed for export] *)
  step. step. callp stack_top_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  do 3 step. callp stack_bottom_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  step. step. if_lit.                                 (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 8 step.                                          (* [comment removed for export] *)
  do 6 zstep.                                         (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615.
  rewrite (land_ones_l bp) by lia.
  step.                                               (* [comment removed for export] *)
  step. if_lit. step. if_lit. step. if_lit.           (* [comment removed for export] *)
  do 5 step.                                          (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -80).
  step.                                               (* [comment removed for export] *)
  name_sp sp (-80). rewrite <- Hsp in ST.
  eapply evtF_cut.
  { eapply unwind_fast_spec0;
    [ exact ST | exact CEIL | | | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact GPG | exact PG | eexists; exact SZC | exact TB | exact LTB | | | | | | | | exact PC
    | exact RIMG | ].
    all: try lia. exact RR. }
  cbv beta. unfold unwind_fast_post.
  lazymatch goal with |- forall ms', _ -> evtF _ _ _ _ => idtac end.
  lazymatch type of MU with munch _ _ ?mcur => post_call bsegs mcur end.
  unname_sp.
  rename PC0 into ST. rename PC1 into SZ'. rename PC2 into TB'. rename PC3 into LTB'. rename POST into TR'.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI' end.
  (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  do 12 step.                                         (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_impl_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|]. split; [exact TR'|].
  split; assumption.
Qed.
End CANSEC1.
