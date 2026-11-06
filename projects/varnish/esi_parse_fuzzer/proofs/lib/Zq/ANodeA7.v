(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j ARtStmts AMTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma page_mask_id : forall x, 0 <= x < 2^62 -> x mod 4096 = 0 -> Z.land (x + 4095) 18446744073709547520 = x.
Proof.
  intros x Hx M. change 18446744073709547520 with (2^64 - 2^12).
  rewrite StrFun.land_align_down by lia. change (2^12) with 4096.
  replace ((x + 4095) mod 4096) with 4095; [lia|].
  rewrite <- Z.add_mod_idemp_l, M by lia. symmetry. apply Z.mod_small. lia.
Qed.

Definition mmapordie_entry : Z := 0x6c23c.
Definition mmap_ecall_pc : Z := 0x6a974.
Definition mmap_after_pc : Z := 0x6a978.
Definition mmapordie_resume : Z := 0x6c2c4.
Definition CF : Z := 0x1466e8.          (* [comment removed for export] *)
Definition PSC : Z := 0x144660.         (* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition mmapordie_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo size name : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> alloc_ceiling <= lo ->
    bv_unsigned sp <= 2^47 ->
    a0 = wz size -> a1 = wz name -> 1 <= size <= 2^44 -> size mod 4096 = 0 -> 1 <= name < 2^47 ->
    ro_cells rsegs m 0xa8b50 [C8 (wz PSC)] -> ro_cells rsegs m PSC [C8 (wz 4096)] ->
    ro_cells rsegs m 0xa8b60 [C8 (wz CF)] -> ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)] ->
    (forall (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) [CB 12 scr; C4 (wz 34); C8 s2; C8 s1; C8 s0; C8 ra] ->
        munch [(bv_unsigned sp - 320, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp + -48) ->
        Q (MSsvc (mkR (wz mmapordie_resume) (wz (bv_unsigned sp + -48)) gp tp t0' t1' t2' (wz name) (wz size)
                      (wz 0) (wz size) (wz 3) (wz 34) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz PSC) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz mmapordie_entry) fc None m (seg_rom rsegs)).

Theorem mmapordie_pre_ok : mmapordie_pre_stmt.
Proof.
  unfold mmapordie_pre_stmt. intros until Q.
  intros MI ST LOLE CEIL SPH A0 A1 SZ SZM NM GPS CPS GCF CDP K.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  change (CF + 260) with 1337324 in CDP.
  unfold mmapordie_entry, mmap_ecall_pc, mmapordie_resume, CF, PSC in *. subst a0 a1.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 48%nat ST.
  do 5 amz. (* [comment removed for export] *)
  do 5 amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  rewrite (page_mask_id size) by lia.
  amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 272%nat ST.
  do 8 amz. (* [comment removed for export] *)
  amz. amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. if_true. (* [comment removed for export] *)
  do 10 amz. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -48).
  do 7 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  step_ecall.
  eapply K; eassumption.
Qed.

(* [comment removed for export] *)
Definition mmapordie_post_stmt : Prop :=
  forall (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo res : Z) (scr : list byte)
         (s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp + -48) -> lo <= usp - 48 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    rw_cells rsegs m (usp + -48) [CB 12 scr; C4 (wz 34); C8 s2v; C8 s1v; C8 s0v; C8 ra0] -> bv_unsigned ra0 mod 2 = 0 ->
    ro_cells rsegs m 0xa8b60 [C8 (wz CF)] -> ro_cells rsegs m (CF + 144) [C8 (wz 0)] ->
    ((bv_unsigned a0 = 2^64 - 12 /\ res = 0) \/ (1 <= bv_unsigned a0 <= 2^64 - 4097 /\ res = bv_unsigned a0)) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(usp - 48, usp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz res) a1' a2' a3' a4' a5' a6' a7'
                   s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz mmapordie_resume) (wz (usp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz mmap_after_pc) fc None m (seg_rom rsegs)).

Theorem mmapordie_post_ok : mmapordie_post_stmt.
Proof.
  unfold mmapordie_post_stmt. intros until Q.
  intros MI ST LOLE CEIL SPH FR RA GCF CML RC K.
  pose proof alloc_ceiling_val as CV.
  change (CF + 144) with 1337208 in CML.
  unfold mmapordie_entry, mmap_after_pc, mmapordie_resume, CF, PSC in *.
  pose proof (munch_refl [(usp - 48, usp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range _ a0) as A0R.
  amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  destruct RC as [[A0V ->]|[A0V ->]].
  - (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. br_not_taken. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    rewrite A0V in FR. change (bv_swrap 32 (0 - (2 ^ 64 - 12))) with 12 in FR.
    amz. amz. (* [comment removed for export] *)
    rewrite A0V. change (Z.b2z (18446744073709547520 <? 2 ^ 64 - 12)) with 1.
    amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. if_false. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    do 7 amz. (* [comment removed for export] *)
    release_frame FR ST usp. apply evt_done. eapply K; eassumption.
  - (* [comment removed for export] *)
    amz. br_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? bv_unsigned a0)) with 0 by (symmetry; apply b2z_ltb_false; lia).
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. br_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? bv_unsigned a0)) with 0 by (symmetry; apply b2z_ltb_false; lia).
    amz. if_false. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. if_true. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    do 7 amz. (* [comment removed for export] *)
    release_frame FR ST usp. apply evt_done. rewrite <- (Z_to_bv_bv_unsigned a0). eapply K; eassumption.
Qed.

End CEIL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
