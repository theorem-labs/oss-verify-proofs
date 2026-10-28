(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs I_iodefs X_xdefs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX D_auxv HandoffAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hs_fx : PropExec.FPState := PropExec.fx0.

Definition hs_start_ok (ch : acs) : bool :=
  (hs_regs_ok ch && hs_ro_ok bsegs ch && hs_stk_ok ch && hs_argv_ok ch && hs_clx_ok ch
   && match a_fd ch with FdStd => true | _ => false end
   && hs_auxv_ok ch)%bool.

Section Start.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.

Variables (RT : rt_sig) (LIB : mem -> Prop) (Σ : rts RT).
Hypothesis Hallow : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb (rt_allow RT Σ) p = true.
Hypothesis Hawf : A_wf (rt_allow RT Σ).
Hypothesis Hminv : MInv (rt_allow RT Σ) model.
Hypothesis Hartm : ARTM RT Σ model.
Hypothesis Hsp0 : rt_sp0 RT Σ = usp.
#[local] Notation m := (mH FULL model (rt_allow RT Σ)).
Hypothesis Hart : ART RT Σ m.
Hypothesis Hsig : sigma0_ok RT Σ (usp - USP_OFF).
Hypothesis HLIB : LIB m.

Lemma hsa_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. intros E1 a H. exact (argH0_high ph sp rdraw argv envp uid hw Hsp Hva E1 a H). Qed.

Lemma hsa_sp0 : bv_unsigned (vm_init_sp (m_vmmaps model)) = usp.
Proof.
  destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. rewrite I1.
  exact (SINV0_sp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E FULL (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)).
Qed.

Lemma hsa_argc : ev E V_ARGC = Z_to_bv 64 (Z.of_nat (length argv)).
Proof.
  destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [Hv _]. rewrite (Hv V_ARGC) by (unfold V_ARGC, NX0; lia).
  reflexivity.
Qed.

Theorem hs_start : START RT OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg bsegs R a_main FULL model).
Proof.
  unfold hs_start_ok in HT.
  apply andb_prop in HT as [HT Hauxt]. apply andb_prop in HT as [H6 Hfd]. apply andb_prop in H6 as [H5 Hclx]. apply andb_prop in H5 as [H4 Hargv].
  apply andb_prop in H4 as [H3 Hstk]. apply andb_prop in H3 as [Hregs Hro].
  assert (Hfd' : a_fd ch = FdStd) by (destruct (a_fd ch); try reflexivity; discriminate Hfd).
  destruct (hi_regs bsegs A nx0 LIMIT SINV argH fs E ch R FULL model HC Hregs) as (R1 & R4 & R10 & R11 & R2).
  pose proof (hi_usp bsegs A nx0 LIMIT SINV argH fs E ch R FULL model HC Hregs) as (U1 & U2 & U3 & U4 & U5).
  rewrite hsa_sp0 in R11, R2, U1, U2, U3, U4, U5. rewrite hsa_argc in R10.
  apply (start_of_handoff A nx0 LIMIT SINV argH fs HULL_ok Hsegtop E ch R FULL model HC RT OUT_repA ERR_repA XENVA LIB argv Σ
           Hallow Hawf Hminv Hartm Hfd' (usp - USP_OFF) (usp + 8) R1 R2 R4 R10 R11 Hart).
  - exact (hi_mem_inv bsegs A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok hsa_argH_high E ch R FULL model HC (rt_allow RT Σ) Hallow Hro).
  - exact (hi_clx A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok hsa_argH_high E ch R FULL model HC (rt_allow RT Σ) Hallow LIB HLIB Hclx).
  - exact (hi_argv A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok E ch R FULL model HC
             (rt_allow RT Σ) Hallow Hargv).
  - exact (hi_auxv A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok E ch R FULL model HC
             (rt_allow RT Σ) Hallow Hauxt (usp - USP_OFF) ltac:(unfold USP_OFF; lia)).
  - pose proof (hi_stk bsegs A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok E ch R FULL model HC (rt_allow RT Σ) Hallow Hstk) as S.
    rewrite hsa_sp0 in S. rewrite Hsp0. unfold STACK_WIN. exact S.
  - exact Hsig.
  - rewrite Hsp0. unfold STACK_WIN, USP_OFF in *. split; [exact U1|]. split; [lia|]. lia.
Qed.

Theorem hs_hole : forall T,
  (forall c, START RT OUT_repA ERR_repA XENVA LIB argv fs c -> realizes bsegs c T) ->
  srealizes bsegs (APS.cfg_of bsegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start.
Qed.

End Start.
