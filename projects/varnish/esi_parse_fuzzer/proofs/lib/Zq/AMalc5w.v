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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts AMTac.

Module AMalloc2.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts AMTac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition comb_hit_entry : Z := 0x3b7fc.
Definition comb_hit_stack : Z := 48.

(* [comment removed for export] *)
Definition comb_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C c cnt maxc sb : Z) (ks : list word) (kw : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 statv' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sb + c * 2^32 + 16 * bv_unsigned kw)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (C + 80 * c, C + 80 * c + 4); (C + 2576, C + 2584)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (C + 80 * c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv'].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo C c cnt maxc sb sz : Z) (ks : list word) (kw statv : word).
  Let E := C + 80 * c.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 48.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SZ : 1 <= sz <= 65536.
  Hypothesis SZ8 : sz mod 8 = 0.
  Hypothesis HC : c = size_class sz.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis SB : ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)].
  Hypothesis PC : rw_cells rsegs m E [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis CNT : 1 <= cnt <= 16.
  Hypothesis KW : nth_error ks (Z.to_nat (cnt - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis STA : rw_cells rsegs m (C + 2576) [C8 statv].
  Hypothesis CR : 4096 <= C /\ C + 3888 <= alloc_ceiling /\ C mod 16 = 0.   (* [comment removed for export] *)
  Hypothesis SBR : 0 <= sb /\ sb + 2^37 <= 2^47.

  #[using="CR STA KWR KW CNT LKS PC SB BLK HC SZ8 SZ SPA LO ST MI E statv Clg"] Lemma comb_alloc_hit :
    evt rsegs (comb_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C c cnt maxc sb ks kw lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1558) (Z_to_bv 64 C) (Z_to_bv 64 sz) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 comb_hit_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE. pose proof (size_class_range sz ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (class_size_range c CR1) as CSR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (C + 80 * c, C + 80 * c + 4); (C + 2576, C + 2584)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 48%nat ST. unfold comb_hit_entry.
    do 11 amz.
    (* [comment removed for export] *)
    rewrite b2z_ltb_false by lia. rewrite Z.add_0_r, Z.mod_small by lia. rewrite lxor_ones64 by lia. br_taken.
    do 3 amz. br_taken.
    amz. amz. br_not_taken. amz. br_not_taken. amz. amz.
    (* [comment removed for export] *)
    let K := fresh "K" in if_cases K; zify_cond K;
    [ (* [comment removed for export] *)
      eapply BLK; [lia| exact SZ8 |]; intros a2' a4' a5' a6' a7' t0' t1'; unfold classid_blk_exit; rewrite <- HC
    | (* [comment removed for export] *)
      do 3 amz; rewrite (Z.shiftr_div_pow2 (sz + 31) 5) by lia; change (2^5) with 32;
      rewrite <- (size_class_small sz) by lia; rewrite <- HC ].
    all: amz; br_not_taken; amz; amz; br_not_taken; amz; amz; amz.
    (* [comment removed for export] *)
    all: replace (Z_to_bv 64 (C + c * 80)) with (Z_to_bv 64 E) by (unfold E; f_equal; lia).
    all: amz; rewrite sx32_small by lia; amz; br_not_taken.
    all: do 7 amz.
    all: rewrite slli32_srli30 by lia; amz.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_read rsegs mm (E + 16) ks (cnt - 1) kw (wa (E + 16 + 4 * (cnt - 1))) (pc_chunks_u32arr mm E _ _ _ ks PC LKS) KW ltac:(lia) eq_refl) as HR end.
    all: amz; rewrite (zx32_word kw KWR); clear HR.
    all: amz; (* [comment removed for export] *) amz. (* [comment removed for export] *)
    all: do 6 amz; first [if_true | if_false].
    all: do 8 amz.
    all: replace (Z_to_bv 64 (bv_unsigned kw ≪ 4 + (c ≪ 32 + sb))) with (Z_to_bv 64 (sb + c * 2^32 + 16 * bv_unsigned kw))
      by (rewrite !Z.shiftl_mul_pow2 by lia; f_equal; lia).
    all: replace (cnt + -1) with (cnt - 1) in PC by lia.
    all: release_frame FR ST (bv_unsigned sp).
    all: finish. all: try exact STA; try exact PC; try exact MU.
  Qed.
End S.
End AMalloc2.


Module AMalloc1.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @NR; @SPR; @LO0; @SBR; @ABR; @K0; @H; @KL; @OL; @CV; @CE0; @NSB; @RSR; @ABQ; @NDE; @ER; @RGE; @K1; @NS; @K2; @RZR; @H0; @K3; @Kn; @ATHR; @CSR; @D0; @H1; @K4; @H2; @LKS; @CGE; @IDR; @SO; @H3; @K5; @Bthr; @DLEN; @RZ8; @Hd; @H4; @CNT; @SHB; @SOA; @E; @DD; @VAL; @VTH; @E2; @H5; @H6; @RZ0; @K7; @RLT; @RM8; @RZS; @ADN0; @ADF0; @Kd; @Hi])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma depot_findC_range : forall D h i r, depot_findC D h i = Some r -> i <= r < i + Z.of_nat (length D).
Proof.
  induction D as [|d D IH]; intros h i r H; cbn in H; [discriminate|].
  destruct (Z.eqb (depot_hashC d) h); [injection H as <-; cbn [length]; lia|].
  apply IH in H. cbn [length]. lia.
Qed.
Lemma depot_putC_id_range : forall D k, 1 <= snd (depot_putC D k) <= Z.of_nat (length D) + 1.
Proof.
  intros D k. unfold depot_putC. destruct (depot_findC D (depot_hashC k) 1) eqn:E; cbn [snd].
  - apply depot_findC_range in E. lia.
  - lia.
Qed.


(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

(* [comment removed for export] *)
Lemma rzlog_call : rzlog_stmt -> forall (l : Z),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
    0 <= l <= 7 -> a0 = Z_to_bv 64 (16 * 2 ^ l) -> bv_unsigned ra mod 2 = 0 ->
    evt rsegs (rzlog_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc l lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rzlog_entry) fc None m (seg_rom rsegs)).
Proof. intros H l; intros; eapply H; eauto. Qed.

(* [comment removed for export] *)
Definition depot_post_lit (dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : list (list Z)) (k : list Z) (n0 f0 lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
     ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (snd (depot_putC D k))) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
     /\ munch [(bv_unsigned sp - 512, bv_unsigned sp); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000)] m m'
     /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
     /\ dr AL_pboth rsegs (fst (depot_putC D k)) n0 f0 m'.
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma depot_call : forall dr, depot_put_stmt dr ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : list (list Z)) (k : list Z) (tr n0 f0 lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 512 -> alloc_ceiling <= lo ->
    a0 = Z_to_bv 64 tr -> a1 = Z_to_bv 64 (Z.of_nat (length k)) ->
    (1 <= length k <= 255)%nat -> Forall (fun w => 0 <= w < 2^64) k ->
    bytes_at rsegs m tr (u64s (map (Z_to_bv 64) k)) -> bv_unsigned sp <= tr ->
    tr + 8 * Z.of_nat (length k) <= 2^47 ->
    dr AL_pboth rsegs D n0 f0 m ->
    NoDup (map depot_hashC D) -> Z.of_nat (length D) + 1 < 65535 -> depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames ->
    aobj n0 kDepotNodesBlock -> n0 + kDepotNodesBlock <= alloc_ceiling -> aobj f0 kStackStoreBlockBytes -> f0 + kStackStoreBlockBytes <= alloc_ceiling ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (depot_post_lit dr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D k n0 f0 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x78cb8) fc None m (seg_rom rsegs)).
Proof. intros dr H. intros. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Definition poison_post_lin (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q8 dd value lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (q8 + 2147450880, q8 + 2147450880 + dd)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (q8 + 2147450880) (repeat (Z_to_bv 8 value) (Z.to_nat dd)).
Lemma poison_call : poison_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q8 dd addr size value lo : Z) (old : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = Z_to_bv 64 addr -> addr = 8 * q8 -> a1 = Z_to_bv 64 size -> size = 8 * dd -> a2 = Z_to_bv 64 value ->
    1 <= dd -> pz_in addr size -> addr + size <= 2^47 ->
    0 <= value < 256 -> (value = 0 -> dd < 2^45) ->
    poison_consts m ->
    rw_cells rsegs m (q8 + 2147450880) [CB (Z.to_nat dd) old] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (poison_post_lin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q8 dd value lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 poison_entry) fc None m (seg_rom rsegs)).
Proof.
  intros PS. intros until old. intros MI ST LOLE CEIL A0 Hq A1 Hd A2 DD HI HE VAL VTH PC SH RA.
  assert (E1 : sh addr = q8 + 2147450880) by (subst addr; rewrite sh_mul8; reflexivity).
  assert (E2 : size / 8 = dd) by (subst size; apply div8_mul8).
  eapply evt_mono.
  { eapply (PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m addr size value lo old);
      try eassumption; try lia.
    - subst addr. apply mod8_mul8.
    - subst size. apply mod8_mul8.
    - rewrite E1, E2. exact SH. }
  intros ms' PO. unfold poison_post in PO. unfold poison_post_lin. rewrite E1, E2 in PO. exact PO.
Qed.

End CEIL.

(* [comment removed for export] *)
Section S1a.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill : Z) (Q : machine_state -> Prop).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 128.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis SO : 0 < stkobj < 2^64.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis INI : ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x136e22 [C1 (Z_to_bv 8 0)].
  Hypothesis K : forall (r : Z) (m1 : word -> option byte) (junk0 : list byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s4' s8' : word),
      r = rz_log n -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
      rw_cells rsegs m1 (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra junk0) ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 canfill) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 r) s4' (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) s8' (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x371e8) fc None m1 (seg_rom rsegs)).

  #[using="K RSS INI SO NR LO ST MI lo Clg"] Lemma alloc_seg1a : evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1558) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 stkobj) (Z_to_bv 64 1) (Z_to_bv 64 canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3707c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 128%nat ST.
    run_to 0x370dc. amz. br_not_taken.
    run_to 0x37114.
    Ltac rzc := unfold rz_log; repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); try lia end.
    Ltac fin r := eapply (K r); [ rzc | eassumption | eassumption | eassumption | eassumption | eassumption ].
    (* [comment removed for export] *)
    amz. let K1 := fresh "K" in if_cases K1; zify_cond K1.
    2:{ amz. amz. fin 0. }
    amz. amz. let K2 := fresh "K" in if_cases K2; zify_cond K2.
    2:{ amz. amz. fin 1. }
    amz. amz. let K3 := fresh "K" in if_cases K3; zify_cond K3.
    2:{ amz. amz. fin 2. }
    amz. amz. amz. let K4 := fresh "K" in if_cases K4; zify_cond K4.
    2:{ amz. amz. fin 3. }
    amz. amz. amz. let K5 := fresh "K" in if_cases K5; zify_cond K5.
    2:{ amz. amz. fin 4. }
    amz. amz. amz. let K6 := fresh "K" in if_cases K6; zify_cond K6.
    2:{ amz. amz. fin 5. }
    amz. amz. amz. amz.
    destruct (Z.lt_ge_cases n 64513).
    - rewrite b2z_ltb_true by lia. change (Z.lxor 1 7) with 6. fin 6.
    - rewrite b2z_ltb_false by lia. change (Z.lxor 0 7) with 7. fin 7.
  Qed.
End S1a.

(* [comment removed for export] *)
Section S1b.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill : Z) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis RZm : ro_cells rsegs m 0xb2380 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis RZL : rzlog_stmt.
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 -> wmono rsegs m m1 ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37230) fc None m1 (seg_rom rsegs)).

  #[using="K RZL FR RZm NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 lo Clg"] Lemma alloc_seg1b : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 canfill) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) s8 (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x371e8) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_log_range n) as RZR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    do 6 amz.
    callz (rzlog_call RZL 0).
    all: sides.
    do 5 amz. callz (rzlog_call RZL 7). all: sides.
    Ltac fin := eapply K; eassumption.
    destruct (Z.eq_dec (rz_log n) 0) as [RZ0|RZ0].
    - (* [comment removed for export] *) rewrite RZ0 in *. amz. br_not_taken. amz. amz. br_not_taken. amz. amz. amz.
      let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn.
      + replace (Z.max n 8) with n in K by lia. fin.
      + amz. replace (Z.max n 8) with 8 in K by lia. fin.
    - amz. br_taken. amz. 
      let K7 := fresh "K7" in if_cases K7; zify_cond K7.
      + (* [comment removed for export] *) amz. amz. amz. let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn.
        * replace (Z.max n 8) with n in K by lia. fin.
        * amz. replace (Z.max n 8) with 8 in K by lia. fin.
      + (* [comment removed for export] *) amz. amz. amz. amz. replace (rz_log n) with 7 in K by lia.
        let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn.
        * amz. replace (Z.max n 8) with 8 in K by lia. fin.
        * amz. replace (Z.max n 8) with n in K by lia. fin.
  Qed.
End S1b.

(* [comment removed for export] *)
Section S1c.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj tsd ctx thr : Z) (Q : machine_state -> Prop).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis MUM : ro_cells rsegs m 0xb2378 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis GT : get_thread_stmt.
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 -> wmono rsegs m m1 ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1558) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37318) fc None m1 (seg_rom rsegs)).

  #[using="K GT TC MUM NR SPR LO ST MI thr ctx tsd lo Clg"] Lemma alloc_seg1c : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37230) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_log_range n) as RZR. pose proof (rz_log_small n ltac:(lia)) as RZS.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr & Bnds). pose proof Bnds as Bnds_; destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx). aobj_lin1 Bthr. aobj_lin1 Bctx. idtac.
    pose proof alloc_ceiling_val as CV.
    do 6 amz.
    replace (Z.land (Z.max n 8 + 7) 18446744073709551608) with (rounded_size n).
    2:{ rewrite land_m8 by lia. unfold rounded_size, round_up. replace (Z.max n 8 + 8 - 1) with (Z.max n 8 + 7) by lia.
        pose proof (Z.div_mod (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT. pose proof (rounded_size_mod8 n) as RM8.
    do 4 amz.
    replace (Z.land (rounded_size n) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
    br_not_taken. amz. amz. rewrite b2z_ltb_false by lia. amz. amz. rewrite sllw_rz.
    pose proof (rz_size_range n) as RSR.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : needed_size n <= 65536) by (apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia).
    amz. amz. amz. amz. rewrite NS. amz. rewrite b2z_ltb_true by lia.
    amz. change (Z.land 1 1) with 1. amz. amz. rewrite Z.land_0_l. amz. amz. rewrite Z.add_0_l.
    amz. br_not_taken. amz. br_not_taken. amz. amz. br_taken.
    (* [comment removed for export] *)
    amz. callz GT. all: sides.
    amz. amz. br_not_taken. amz. amz. amz. amz.
    eapply K; eassumption.
  Qed.
End S1c.

(* [comment removed for export] *)
Section S2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill ctx thr c cnt maxc sb AB : Z) (ks : list word) (b0w b1w : byte) (kw statv h2 w4 d8 trace sztag : word) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis SO : 0 < stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis SBc : ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)].
  Hypothesis PC : rw_cells rsegs m (thr + 208 + 80 * c) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis CNT : 1 <= cnt <= 16.
  Hypothesis KW : nth_error ks (Z.to_nat (cnt - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis STA : rw_cells rsegs m ((thr + 208) + 2576) [C8 statv].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABE : AB = sb + c * 2^32 + 16 * bv_unsigned kw.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis SEP_thr : thr + 4096 <= sb \/ sb + 2^37 <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= sb \/ sb + 2^37 <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis SOA : bv_unsigned sp <= stkobj.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 trace; C8 sztag].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); ((thr + 208 + 80 * c), (thr + 208 + 80 * c) + 4); ((thr + 208) + 2576, (thr + 208) + 2584); (AB + rz_size n + -16, (AB + rz_size n))] m m1 -> wmono rsegs m m1 ->
      rw_cells rsegs m1 (thr + 208 + 80 * c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)] ->
      rw_cells rsegs m1 ((thr + 208) + 2576) [C8 statv'] ->
      rw_cells rsegs m1 (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 trace sztag a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 0) (Z_to_bv 64 ((AB + rz_size n) + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37424) fc None m1 (seg_rom rsegs)).

  #[using="K TRC CTR CT8 TH0 HDR SOA SEP_tc SEP_ctx SEP_thr ABR ABA ABE SBR THRA THR STA KWR KW CNT LKS PC SBc BLK HC FR NR SPR SPA LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 sztag trace d8 w4 h2 statv kw b1w b0w ks AB sb maxc cnt c ctx canfill lo Clg"] Lemma alloc_seg2 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1558) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37318) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); ((thr + 208 + 80 * c), (thr + 208 + 80 * c) + 4); ((thr + 208) + 2576, (thr + 208) + 2584); (AB + rz_size n + -16, (AB + rz_size n))] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR. unfold kMaxSize in CSR. unfold kHighMemBeg in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    amz. callz (comb_alloc_hit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (thr + 208) c cnt maxc sb (needed_size n) ks kw statv).
    all: sides.
    rewrite <- ABE. amz. amz. br_not_taken. amz. amz.
    replace (Z.land (AB + rz_size n) 7) with 0.
    2:{ symmetry. apply land7_of_mod8; [lia|]. apply mod_add_lit; [lia| |].
        - apply (mod0_down AB 32 8); [exists 4; reflexivity| exact ABA].
        - apply (mod0_down (rz_size n) 16 8); [exists 2; reflexivity| apply rz_size_mod16]. }
    amz. amz. br_taken. amz. amz. br_not_taken.
    (* [comment removed for export] *)
    amz. amz. amz. amz.
    amz. replace (Z.shiftr n 32) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. replace (Z.shiftr n 48) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. sb_done. amz. amz. amz. if_false. amz. amz. amz. amz. amz. sb_done.
    (* [comment removed for export] *)
    amz. br_not_taken. amz. amz. amz. amz. amz. amz.
    eapply K; eassumption.
  Qed.
End S2.

(* [comment removed for export] *)
Section S3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr c sb AB q r8 d e n0 f0 : Z) (b0w : byte) (b1v : Z) (d8 : word)
            (D : list (list Z)) (k : list Z) (olds : list byte) (Q : machine_state -> Prop).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis SOA : bv_unsigned sp <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis PCo : poison_consts m.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  Hypothesis DR : dr AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0 : n0 + kDepotNodesBlock <= sb \/ sb + 2^37 <= n0.
  Hypothesis SEP_f0 : f0 + kStackStoreBlockBytes <= sb \/ sb + 2^37 <= f0.
  Hypothesis KL : (1 <= length k <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) k.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (Z_to_bv 64 (stkobj + 16)); C8 (Z_to_bv 64 (Z.of_nat (length k)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) k)).
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].
  Hypothesis SHA : ro_cells rsegs m (q + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)].
  Hypothesis SHU : u8arr rsegs m (q + r8 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis K : forall (m1 md : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      let id := snd (depot_putC D k) in
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + rz_size n + -8, AB + rz_size n); (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d)] m m1 ->
      wmono rsegs m m1 ->
      dr AL_pboth rsegs (fst (depot_putC D k)) n0 f0 md ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -8, AB + rz_size n);
             (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d)] md m1 -> wmono rsegs md m1 ->
      rw_cells rsegs m1 (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
      bytes_at rsegs m1 (q + r8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d)) ->
      wr_at rsegs m1 (q + r8 + kShadowOffset) d ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37534) fc None m1 (seg_rom rsegs)).

  #[using="K OL SHU SHA HDR TRB TRC KR KL SEP_f0 SEP_n0 DF0 DN0 DTOT DLEN DND DR DPS PS PCo RZ8 ABR ABQ SBR THR HC SOA ER NDE NR SPR LO ST MI dr olds D d8 b1v b0w f0 n0 e d r8 q sb c lo Clg"] Lemma alloc_seg3 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 (stkobj + 16)) (Z_to_bv 64 (Z.of_nat (length k))) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37424) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + rz_size n + -8, AB + rz_size n); (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR. unfold kMaxSize in CSR.
    pose proof PCo as PC'. destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps).
    clear PCo. kun.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV.
    pose proof (depot_putC_id_range D k) as IDR.
    pose proof (u8arr_bound rsegs m _ _ SHU) as SHB. rewrite OL, Z2Nat.id in SHB by lia.
    amz. callz (depot_call dr DPS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D k (stkobj + 16) n0 f0 lo). all: sides.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?md _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -8, AB + rz_size n);
             (q + r8 + 2147450880, q + r8 + 2147450880 + d)] md) as MU2;
      pose proof (wmono_refl rsegs md) as WM2 end.
    amz. amz. rewrite (Z.mod_small (snd (depot_putC D k)) 4294967296) by lia. amz. rewrite Z.lor_0_l. amz. amz. first [if_true | if_false].
    amz. amz. amz. amz. replace (Z.shiftr AB 3) with q by (rewrite ABQ, shiftr3_mul8; lia). amz.
    replace (2147450880 + q) with (q + 2147450880) by lia. amz. amz. if_true.
    amz. amz. amz.
    replace (Z.land n 281474976710648) with (8 * d) by (symmetry; rewrite NDE; apply land_mask48_m8; lia).
    amz. destruct (Z.eq_dec d 0) as [D0|D0].
    - (* [comment removed for export] *)
      if_cases Kd; zify_cond Kd; [clear Kd| exfalso; lia].
      eapply K; try eassumption.
      + rewrite D0. change (Z.to_nat 0) with 0%nat. cbn [repeat]. split; [lia| split; [cbn [length Z.of_nat]; lia| intros i Hi; cbn in Hi; lia]].
      + destruct SHU as [_ W]. rewrite OL, D0 in W. rewrite D0. exact W.
    - br_not_taken. amz. amz. amz. amz.
      pose proof (proj2 SHU) as WRS. rewrite OL, Z2Nat.id in WRS by lia.
      callz (poison_call PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + r8) d (AB + rz_size n) (8 * d) 0 lo olds). all: try sides.
      1:{ rewrite <- OL. apply rw_cells_of_u8arr. exact SHU. }
      eapply K; try eassumption.
  Qed.
End S3.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AMalloc1.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)
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
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

(* [comment removed for export] *)
Section S4.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr c sb AB q r8 d e : Z) (oldp : byte) (Q : machine_state -> Prop).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 < e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis CR1 : 1 <= c <= 30.
  Hypothesis FIT : needed_size n <= class_size c.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].  (* [comment removed for export] *)
  Hypothesis SHP : rw_cells rsegs m (q + r8 + d + kShadowOffset) [C1 oldp].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + 1)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 (AB + rz_size n + 8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x375c8) fc None m1 (seg_rom rsegs)).

  #[using="K SHP AF2 AF1 PCo RZ8 FIT CR1 ABR ABQ SBR THR ER NDE NR ST MI oldp e r8 q sb c lo Clg"] Lemma alloc_seg4_nz : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37534) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    pose proof (class_size_range c CR1) as CSR.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    clear PCo. kun. unfold kHighMemEnd in Chivars.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV.
    amz. br_not_taken. amz. amz. amz. amz. amz. change (Z.b2z (0 <? 1)) with 1.
    amz. amz. first [if_false|if_true]. amz. amz. amz. amz. amz. amz. amz. amz.
    amz. br_not_taken. amz. amz. amz. amz. amz. amz. amz. amz. br_taken.
    amz. amz. amz. amz. amz. amz. br_not_taken. amz. br_not_taken.
    amz. amz. amz. amz.
    replace (Z.shiftr (AB + rz_size n + 8 * d) 3) with (q + r8 + d).
    2:{ rewrite ABQ, RZ8. replace (8 * q + 8 * r8 + 8 * d) with (8 * (q + r8 + d)) by lia. rewrite shiftr3_mul8; lia. }
    amz. amz. amz. amz.
    replace (2147450880 + (q + r8 + d)) with (q + r8 + d + 2147450880) by lia.
    rewrite (land_land_ones7 n d e NDE) by lia.
    amz. sb_done.
    eapply K; eassumption.
  Qed.
End S4.

(* [comment removed for export] *)
Section S4z.
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (n d : Z) (Q : machine_state -> Prop).
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + 0.
  Hypothesis K : evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x375c8) fc None m (seg_rom rsegs)).
  #[using="K NDE NR"] Lemma alloc_seg4_z : evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37534) fc None m (seg_rom rsegs)).
  Proof. amz. br_taken. exact K. Qed.
End S4z.

(* [comment removed for export] *)
Section S5.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr c sb AB : Z) (v0 v1 v2 : word) (vs : list word) (uj : list byte) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis BLK2 : classid_blk2_stmt.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis SEP_thr : thr + 4096 <= sb \/ sb + 2^37 <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= sb \/ sb + 2^37 <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis TSDL : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].   (* [comment removed for export] *)
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].  (* [comment removed for export] *)
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STA2 : u64arr rsegs m (thr + 2912) vs.
  Hypothesis LVS : length vs = 32%nat.
  Hypothesis USR : rw_cells rsegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' vc' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8);
             (AB + rz_size n, AB + rz_size n + Z.min n 4096)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (thr + 2800) [C8 v0'; C8 v1'; C8 v2'] ->
      u64arr rsegs m1 (thr + 2912) (upd vs (Z.to_nat c) vc') ->
      rw_cells rsegs m1 (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) (fill_result canfill uj (Z.to_nat (Z.min n 4096)))] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3775c) fc None m1 (seg_rom rsegs)).

  (* [comment removed for export] *)
  #[using="K LVS SEP_tc SEP_ctx SEP_thr ABR SBR TC HC CF NR LO sb ctx tsd Clg"] Lemma alloc_seg5_tail : forall (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' : word) (m0 : word -> option byte),
      mem_inv rsegs m0 -> stk rsegs m0 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8);
             (AB + rz_size n, AB + rz_size n + Z.min n 4096)] m m0 ->
      wmono rsegs m m0 ->
      rw_cells rsegs m0 (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0) ->
      poison_consts m0 ->
      ro_cells rsegs m0 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)] -> ro_cells rsegs m0 0xb23e4 [C4 (Z_to_bv 64 4096)] ->
      ro_cells rsegs m0 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)] ->
      rw_cells rsegs m0 (thr + 2800) [C8 v0'; C8 v1'; C8 v2'] ->
      u64arr rsegs m0 (thr + 2912) vs ->
      rw_cells rsegs m0 (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 (thr + 2912)) (Z_to_bv 64 c) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3770c) fc None m0 (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. intros until m0. intros MI0 ST0 MU WM FR0 PC0 AF1' AF44' AF52' STS0 STA0 USR0.
    clear MI ST FR PCo AF1 AF44 AF52 STS STA2 USR.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR.
    (first [ dand13 PC0 as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC0 as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx. clear Cini Ckey Ctsd Cctx Cthr2. kun.
    unfold kMallocFillByte in *.
    assert (LO0 : 0 <= lo) by (destruct ST0 as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR0.
    pose proof (u64arr_bound rsegs m0 _ _ STA0) as STB. pose proof LVS as LVS'. rewrite LVS' in STB.
    amz. rewrite (Z.shiftl_mul_pow2 c 3) by lia. change (2^3) with 8. replace (c * 8) with (8 * c) by lia. amz.
    destruct (nth_error vs (Z.to_nat c)) as [vc|] eqn:VC. 2:{ exfalso. apply nth_error_None in VC. lia. }
    pose proof (u64arr_read rsegs m0 (thr + 2912) vs c vc (wa (thr + 2912 + 8 * c)) STA0 VC ltac:(lia) eq_refl) as HR.
    amz. amz.
    pose proof (u64arr_store_ok rsegs m0 (thr + 2912) vs c (wa (thr + 2912 + 8 * c)) STA0 ltac:(lia) eq_refl) as SOK.
    amz. pose proof (u64arr_write rsegs m0 (thr + 2912) vs c (Z_to_bv 64 (bv_unsigned vc + 1)) STA0 ltac:(lia)) as STA1. clear STA0 HR.
    store_done.
    (* [comment removed for export] *)
    amz. amz. destruct (Z.eq_dec canfill 0) as [CF0|CF1].
    - (* [comment removed for export] *)
      subst canfill. if_true. eapply K; eassumption.
    - if_cases Kf; zify_cond Kf; [exfalso; lia| clear Kf].
      amz. amz. amz. amz. if_false. amz.
      assert (FRK : fill_result canfill uj (Z.to_nat (Z.min n 4096)) = repeat (Z_to_bv 8 (190 mod 256)) (Z.to_nat (Z.min n 4096))).
      { unfold fill_result. replace (canfill =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      amz. let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn.
      + (* [comment removed for export] *) replace (Z.min n 4096) with n in * by lia.
        amz. amz. amz. amz. amz. amz.
        callz (memset_spec_z _ _ _ _ _ _ _ _ _ (AB + rz_size n) 190 n). all: sides.
        rewrite FRK in K. eapply K; eassumption.
      + replace (Z.min n 4096) with 4096 in * by lia.
        amz. amz. amz. amz. amz. amz. amz.
        callz (memset_spec_z _ _ _ _ _ _ _ _ _ (AB + rz_size n) 190 4096). all: sides.
        rewrite FRK in K. eapply K; eassumption.
  Qed.

  #[using="K USR LVS STA2 STS AF52 AF44 AF1 PCo TPL TSDL SEP_tc SEP_ctx SEP_thr ABR SBR BLK2 TSS TC HC FR CF NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 uj vs v2 v1 v0 sb c ctx tsd canfill lo Clg"] Lemma alloc_seg5 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x375c8) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8);
             (AB + rz_size n, AB + rz_size n + Z.min n 4096)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx. kun.
    unfold kMallocFillByte in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    pose proof (u64arr_bound rsegs m _ _ STA2) as STB. rewrite LVS in STB.
    amz. callz TSS. all: sides.
    unfold off_th_stats. amz. amz. amz. amz. amz. amz. amz. amz. amz. amz. amz. amz.
    amz. br_taken. amz. amz. amz.
    let Kc := fresh "Kc" in if_cases Kc; zify_cond Kc.
    - (* [comment removed for export] *)
      eapply BLK2; [lia| apply needed_size_mod8 |]. intros a2' a3' a4' a5' a6'. unfold classid_blk2_exit. rewrite <- HC.
      eapply alloc_seg5_tail; try eassumption;
      exact (conj Ccan (conj Cgotcf (conj Cthr (conj Cgotsh (conj Cshoff (conj Cgotmid (conj Cgotmide (conj Cgothi (conj Chivars (conj Cgotms (conj Creal (conj Cgotps Cps)))))))))))).
    - amz. amz. rewrite (Z.shiftr_div_pow2 (needed_size n + 31) 5) by lia. change (2^5) with 32.
      rewrite <- (size_class_small (needed_size n)) by lia. rewrite <- HC. amz.
      eapply alloc_seg5_tail; try eassumption;
      exact (conj Ccan (conj Cgotcf (conj Cthr (conj Cgotsh (conj Cshoff (conj Cgotmid (conj Cgotmide (conj Cgothi (conj Chivars (conj Cgotms (conj Creal (conj Cgotps Cps)))))))))))).
  Qed.
End S5.

(* [comment removed for export] *)
Section S6.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill thr c sb AB b1v id : Z) (b0w : byte) (j0 j1 : word) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis ABH : rz_size n <> 16 -> rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis K : forall (m1 : word -> option byte)
                        (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (AB + rz_size n + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
      (rz_size n <> 16 -> rw_cells rsegs m1 AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + rz_size n + -16))]) ->
      evt rsegs Q
        (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 (AB + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)).

  (* [comment removed for export] *)
  #[using="K ABR SBR THR HC NR SPR LO sb c Clg"] Lemma alloc_seg6_tail : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m0 : word -> option byte),
      mem_inv rsegs m0 -> stk rsegs m0 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] m m0 ->
      wmono rsegs m m0 ->
      rw_cells rsegs m0 (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0) ->
      ro_cells rsegs m0 0x146680 [C8 (Z_to_bv 64 0)] ->
      rw_cells rsegs m0 (AB + rz_size n + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
      (rz_size n <> 16 -> rw_cells rsegs m0 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (AB + rz_size n + -16))]) ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x377a4) fc None m0 (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. intros until m0. intros MI0 ST0 MU WM FR0 HK0 HDR0 ABH0.
    clear MI ST FR LS1 LS2 HK HDR ABH.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR. kun. unfold kAllocBegMagic, CHUNK_ALLOCATED in *.
    assert (LO0 : 0 <= lo) by (destruct ST0 as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR0.
    (* [comment removed for export] *)
    destruct (Z.eq_dec (rz_size n) 16) as [E16|N16];
      [clear ABH0 | pose proof (ABH0 N16) as ABH1; clear ABH0].
    all: amz; amz; amz.
    (* [comment removed for export] *)
    all: carve_frame 32%nat ST0.
    all: arun_to 0x66e7c; amz.
    all: release_frame FR ST0 (bv_unsigned sp + -128).
    (* [comment removed for export] *)
    all: arun_to 0x377ec; amz.
    all: release_frame FR0 ST0 (bv_unsigned sp).
    all: eapply K; try eassumption.
    - intros X. exfalso. exact (X E16).
    - intros _. exact ABH1.
  Qed.

  #[using="K ABH B1R HDR HK LS2 LS1 ABR SBR THR TPL HC FR NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 j1 j0 b0w id b1v sb c canfill lo Clg"] Lemma alloc_seg6 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3775c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR. kun. unfold kAllocBegMagic, CHUNK_ALLOCATED in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    pose proof (zr_word tp) as TPR; unfold inr64 in TPR.
    (* [comment removed for export] *)
    destruct (Z.eq_dec (rz_size n) 16) as [RZ16|RZ16];
      [clear ABH | pose proof (ABH RZ16) as ABH'; clear ABH; assert (RZ32 : 32 <= rz_size n) by (pose proof (rz_size_cases n); lia)].
    (* [comment removed for export] *)
    all: amz; amz; amz; amz; replace (16 + bv_unsigned tp) with (bv_unsigned tp + 16) by lia.
    all: amz; amz; amz; amz; amz; rewrite (unsigned_lit8 b1v B1R); amz; amz; amz; amz.
    all: amz; sb_done; amz; amz.
    all: amz.
    - (* [comment removed for export] *)
      if_cases Kq; zify_cond Kq; [clear Kq| exfalso; lia].
      eapply alloc_seg6_tail; try eassumption. intros X; exfalso; exact (X RZ16).
    - if_cases Kq; zify_cond Kq; [exfalso; lia| clear Kq].
      amz. amz. br_not_taken. amz. amz. amz. amz. amz.
      eapply alloc_seg6_tail; try eassumption. intros _. exact ABH'.
  Qed.
End S6.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
