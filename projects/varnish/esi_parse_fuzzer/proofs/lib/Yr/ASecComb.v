(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
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
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition comb_entry : Z := 0x3b91c.
Definition comb_sec_ret : Z := 0x3b9c4.
Definition lma_entry : Z := 0x3bbf4.
Definition LMA : Z := 0xb1d98.
Definition LSTAT : Z := 0xb2008.

(* [comment removed for export] *)
Definition comb_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition comb_sec_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo C size : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz 0xb1d58 -> a1 = wz C -> a2 = wz size -> a3 = wz 8 -> kMaxSize < size < 2^48 ->
    (forall (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) (comb_frame s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp + -48) ->
        evt rsegs Q (MS (mkR (wz comb_sec_ret) (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz 8) s1
                            (wz LMA) (wz LSTAT) (wz size) (wz 8) (wz LMA) (wz 0x10000) a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz lma_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz comb_entry) fc None m (seg_rom rsegs)).

Theorem comb_sec_pre_ok : comb_sec_pre_stmt.
Proof.
  unfold comb_sec_pre_stmt. intros until Q.
  intros MI ST LOLE CEIL A0 A1 A2 A3 SZ K.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  unfold comb_entry, comb_sec_ret, lma_entry, LMA, LSTAT, comb_frame, kMaxSize in *. subst a0 a1 a2 a3.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 48%nat ST.
  do 7 amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  rewrite (b2z_ltb_false size 1) by lia. rewrite Z.add_0_r. rewrite (Z.mod_small size 18446744073709551616) by lia.
  rewrite (lxor_ones64 size) by lia.
  amz. br_taken. (* [comment removed for export] *)
  amz. amz. amz. br_taken. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. br_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  eapply K; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition comb_sec_post_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo : Z) (s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp + -48) -> lo <= usp - 48 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    rw_cells rsegs m (usp + -48) (comb_frame s4v s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v a0 a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 48, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo usp)
        (MS (mkR (wz comb_sec_ret) (wz (usp + -48)) gp tp t0 t1 t2 (wz 8) s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz comb_sec_ret) fc None m (seg_rom rsegs)).

Theorem comb_sec_post_ok : comb_sec_post_stmt.
Proof.
  unfold comb_sec_post_stmt. intros until ra0.
  intros MI ST LOLE CEIL USP FR RA.
  pose proof alloc_ceiling_val as CV. unfold comb_sec_ret, comb_frame in *.
  replace (usp - 48) with (usp + -48) by lia.
  pose proof (munch_refl [(usp + -48, usp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  amz. amz. amz. if_false. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  do 7 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  release_frame FR ST usp. finish.
  all: OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; eassumption.
Qed.

End CEIL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
