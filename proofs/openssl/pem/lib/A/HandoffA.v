(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs I_iodefs X_xdefs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Definition hs_start_ok (ch : acs) : bool :=
  (hs_regs_ok ch && hs_ro_ok asegs ch && hs_stk_ok ch && hs_argv_ok ch && hs_clx_ok ch
   && match a_fd ch with FdStd => true | _ => false end)%bool.

Section Start.
Context {XB : BlobEnv}.      (* [comment removed for export] *)
Variables (A : atable) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hseglo : img_lo A = SEGLO.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
(* [comment removed for export] *)
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH usp fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.

(* [comment removed for export] *)
Variables (RT : rt_sig) (LIB : mem -> Prop) (Σ : rts RT).
Variable CG : cgraph.          (* [comment removed for export] *)
Hypothesis Hallow : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb (rt_allow RT Σ) p = true.
Hypothesis Hawf : A_wf (rt_allow RT Σ).
Hypothesis Hminv : MInv (rt_allow RT Σ) model.
Hypothesis Hartm : ARTM RT Σ model.
Hypothesis Hsp0 : rt_sp0 RT Σ = usp.
#[local] Notation m := (mH FULL model (rt_allow RT Σ)).
Hypothesis Hart : ART RT Σ m.
Hypothesis Hsig : sigma0_ok RT CG Σ (usp - USP_OFF).
Hypothesis HLIB : LIB m.

Lemma hsa_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ usp <= bv_unsigned a.
Proof. intros E1 a H. exact (ha_argH_high ph sp rdraw argv envp uid hw Hsp Hva E1 a H). Qed.

(* [comment removed for export] *)
Lemma hsa_isp : sp_window_lo <= usp <= sp_window_hi.
Proof. destruct Hsp as (H1 & H2 & _). split; assumption. Qed.

(* [comment removed for export] *)
Lemma hsa_sp0 : bv_unsigned (vm_init_sp (m_vmmaps model)) = usp.
Proof. exact (proj1 (APS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.

Lemma hsa_argc : ev E V_ARGC = Z_to_bv 64 (Z.of_nat (length argv)).
Proof.
  destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [Hv _]. rewrite (Hv V_ARGC) by (unfold V_ARGC, NX0; lia).
  reflexivity.
Qed.

Theorem hs_start : START RT OUT_repA ERR_repA (XENVA false) LIB CG argv fs (canon_cfg asegs R a_main FULL model).
Proof.
  unfold hs_start_ok in HT.
  apply andb_prop in HT as [H6 Hfd]. apply andb_prop in H6 as [H5 Hclx]. apply andb_prop in H5 as [H4 Hargv].
  apply andb_prop in H4 as [H3 Hstk]. apply andb_prop in H3 as [Hregs Hro].
  assert (Hfd' : a_fd ch = FdStd) by (destruct (a_fd ch); try reflexivity; discriminate Hfd).
  destruct (hi_regs asegs A LIMIT SINV argH usp fs E ch R FULL model HC Hregs hsa_isp) as (R1 & R4 & R10 & R11 & R2).
  pose proof (hi_usp asegs A LIMIT SINV argH usp fs E ch R FULL model HC Hregs hsa_isp) as (U1 & U2 & U3 & U4 & U5).
  rewrite hsa_sp0 in R11, R2, U1, U2, U3, U4, U5. rewrite hsa_argc in R10.
  apply (start_of_handoff A LIMIT SINV argH usp fs HULL_ok Hsegtop Hseglo E ch R FULL model HC RT OUT_repA ERR_repA (XENVA false) LIB argv CG Σ
           Hallow Hawf Hminv Hartm Hfd' (usp - USP_OFF) (usp + 8) R1 R2 R4 R10 R11 Hart).
  - exact (hi_mem_inv asegs A LIMIT SINV argH usp fs SEGS_in_hull HULL_ok hsa_argH_high E ch R FULL model HC (rt_allow RT Σ) Hallow Hro).
  - exact (hi_clx A LIMIT SINV argH usp fs SEGS_in_hull HULL_ok hsa_argH_high E ch R FULL model HC (rt_allow RT Σ) Hallow Hsegtop Hseglo LIB HLIB Hclx).
  - exact (hi_argv A LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok E ch R FULL model HC
             (rt_allow RT Σ) Hallow Hargv).
  - pose proof (hi_stk asegs A LIMIT SINV argH usp fs SEGS_in_hull HULL_ok E ch R FULL model HC (rt_allow RT Σ) Hallow hsa_isp Hstk) as S.
    rewrite hsa_sp0 in S. rewrite Hsp0. unfold STACK_WIN. exact S.
  - exact Hsig.
  - rewrite Hsp0. unfold STACK_WIN, USP_OFF in *. split; [exact U1|]. split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Theorem hs_hole : forall T,
  (forall c, START RT OUT_repA ERR_repA (XENVA false) LIB CG argv fs c -> realizes asegs c T) ->
  srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start.
Qed.

End Start.
