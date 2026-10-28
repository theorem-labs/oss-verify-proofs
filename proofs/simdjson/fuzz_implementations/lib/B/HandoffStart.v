(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_auxv D_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import SrzEqv HandoffKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hk_fx : PropExec.FPState := PropExec.fx0.

Section Start.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (fs : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH fs E ch R FULL model.

Variables (RT : rt_sig) (OUT_rep : stdout_st -> mem -> Prop) (ERR_rep XENV LIB : mem -> Prop) (argvb : list (list byte)).

Variable (Σ : rts RT).
Hypothesis Hallow : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb (rt_allow RT Σ) p = true.
Hypothesis Hawf : A_wf (rt_allow RT Σ).
Hypothesis Hminv : MInv (rt_allow RT Σ) model.
Hypothesis Hartm : ARTM RT Σ model.

Hypothesis Hfd : a_fd ch = AP.FdStd.

#[local] Notation m := (mH FULL model (rt_allow RT Σ)).

Variables (usp ap : Z).
Hypothesis R1 : getr R (Z_to_bv 5 1) = Z_to_bv 64 MAIN_RA.
Hypothesis R2 : getr R (Z_to_bv 5 2) = Z_to_bv 64 usp.
Hypothesis R4 : getr R (Z_to_bv 5 4) = Z_to_bv 64 TP_A.
Hypothesis R10 : getr R (Z_to_bv 5 10) = Z_to_bv 64 (Z.of_nat (length argvb)).
Hypothesis R11 : getr R (Z_to_bv 5 11) = Z_to_bv 64 ap.

Hypothesis Hart : ART RT Σ m.
Hypothesis Hinv : mem_inv bsegs m.
Hypothesis Hclx : CLX OUT_rep ERR_rep XENV LIB stdout_init m.
Hypothesis Hargv : argv_rep argvb m ap.
Hypothesis Haux : el_auxvA usp m.
Hypothesis Hstk : stk bsegs m (rt_sp0 RT Σ - STACK_WIN) usp.
Hypothesis Hsig : sigma0_ok RT Σ usp.
Hypothesis Husp : usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp.

Theorem start_of_handoff : START RT OUT_rep ERR_rep XENV LIB argvb fs (canon_cfg bsegs R a_main FULL model).
Proof.
  unfold START.
  exists Σ, usp, ap,
    (getr R (Z_to_bv 5 3)), (getr R (Z_to_bv 5 5)), (getr R (Z_to_bv 5 6)), (getr R (Z_to_bv 5 7)), (getr R (Z_to_bv 5 8)),
    (getr R (Z_to_bv 5 9)), (getr R (Z_to_bv 5 12)), (getr R (Z_to_bv 5 13)), (getr R (Z_to_bv 5 14)), (getr R (Z_to_bv 5 15)),
    (getr R (Z_to_bv 5 16)), (getr R (Z_to_bv 5 17)), (getr R (Z_to_bv 5 18)), (getr R (Z_to_bv 5 19)), (getr R (Z_to_bv 5 20)),
    (getr R (Z_to_bv 5 21)), (getr R (Z_to_bv 5 22)), (getr R (Z_to_bv 5 23)), (getr R (Z_to_bv 5 24)), (getr R (Z_to_bv 5 25)),
    (getr R (Z_to_bv 5 26)), (getr R (Z_to_bv 5 27)), (getr R (Z_to_bv 5 28)), (getr R (Z_to_bv 5 29)), (getr R (Z_to_bv 5 30)),
    (getr R (Z_to_bv 5 31)), fp_regs, fp_csr, m.
  split; [vm_compute; reflexivity|].
  split; [|split; [exact Hart|split; [exact Hinv|split; [exact Hclx|split; [exact Hargv|split; [exact Haux|split; [exact Hstk|split; [exact Hsig|exact Husp]]]]]]]].
  unfold ASTA, AST. split; [|split; [|split]].
  -   unfold macct. split; [exact Hawf|]. split; [exact Hminv|].
    split; [exact (hk_halted bsegs A nx0 LIMIT SINV argH fs E ch R FULL model HC)|].
    split; [rewrite <- Hsegtop; exact (hk_ranges_from bsegs A nx0 LIMIT SINV argH fs E ch R FULL model HC)|].
    unfold SEGTOP_A. lia.
  -
    unfold canon_cfg, canon_regs, entry_st, restrict, mkst, MS, mH. cbn [cfg_ms cfg_model].
    rewrite R1, R2, R4, R10, R11. reflexivity.
  -   split; [exact Hartm|]. unfold PMfd. split.
    { pose proof (APS.co_fds _ _ _ _ _ _ _ _ _ _ _ _ HC) as F. rewrite Hfd in F. exact F. }
    exact (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
  -   intros a Ha Hna. cbn [cfg_ms cfg_model canon_cfg mkst ms_mem] in *.
    exact (hk_HZ bsegs A nx0 LIMIT SINV argH fs HULL_ok E ch R FULL model HC (rt_allow RT Σ) Hallow a Ha Hna).
Qed.

Theorem hole_of_start : forall T,
  (forall c, START RT OUT_rep ERR_rep XENV LIB argvb fs c -> realizes bsegs c T) ->
  srealizes bsegs (APS.cfg_of bsegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact start_of_handoff.
Qed.

End Start.
