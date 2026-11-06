(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanNodesArg CxPlan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3B CxfNodes CxfNodesArg CxfInst CxfCheck CxfExec CxfPlan CxfPlanC CxfRt CxfL1 CxfL2 CxfL3 CxfL4 CxfL6 CxfL7 CxfL9 CxfL11 CxfL12 CxfL15 CxfL16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFF.
Import AX2. Import APC. Import CAP.

Theorem check_l_eq : forall segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p,
  CXFL.check_f segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p
  = CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p.
Proof. intros. rewrite CXFL.L_CXFL_check_f. apply CXF.check_f_eq. Qed.

Lemma check_l_intro : forall segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p r,
  CXFL.check_f segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r ->
  CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r.
Proof. intros. rewrite <- check_l_eq. assumption. Qed.

Lemma check_l_hooks : forall segs IT A nx0 LIMIT XN XE XB HS XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p r,
  (forall id args c, XN' id args c = XN id args c) -> (forall id args c, XE' id args c = XE id args c) ->
  (forall id args c, XB' id args c = XB id args c) -> (forall h, HS' h = HS h) ->
  CXFL.check_f segs IT A nx0 LIMIT XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p = r ->
  CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r.
Proof.
  intros segs IT A nx0 LIMIT XN XE XB HS XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p r H1 H2 H3 H4 H.
  assert (E1 : XN' = XN) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H1).
  assert (E2 : XE' = XE) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H2).
  assert (E3 : XB' = XB) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H3).
  assert (E4 : HS' = HS) by (apply functional_extensionality; intros h; apply H4).
  subst XN' XE' XB' HS'. apply check_l_intro. exact H.
Qed.

(* [comment removed for export] *)
Definition node_munmap_pL (segs : list Segment) (cs : acs) : option acs := CXFNL.node_munmap_pF segs cs.
Lemma node_munmap_pL_eq : forall segs cs, node_munmap_pL segs cs = CAP.node_munmap_p segs cs.
Proof. intros. unfold node_munmap_pL. rewrite CXFNL.L_CXFNL_node_munmap_pF. apply CXFN.node_munmap_pF_eq. Qed.
Definition xe_L (segs : list Segment) (A : atable) (nx0 : nat) (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  CXFAL.xe_f segs A nx0 id args cs.
Lemma xe_L_eq : forall segs A nx0 id args cs, xe_L segs A nx0 id args cs = AN.xe segs A nx0 id args cs.
Proof. intros. unfold xe_L. rewrite CXFAL.L_CXFAL_xe_f. apply CXFA.xe_f_eq. Qed.

(* [comment removed for export] *)
Definition inst_list_L (ch : acs) (s : list (nat * expr)) : acs := CXFIL.inst_list_s ch s.
Lemma inst_list_L_eq : forall ch s, inst_list_L ch s = inst_list ch s.
Proof. intros. unfold inst_list_L. rewrite CXFIL.L_CXFIL_inst_list_s. apply CXFI.inst_list_s_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_x_c (segs : list Segment) (A : atable) (nx0 : nat) (c : CXFRT.rtc) (x : xnode) (args : list expr) (cs : acs) : option acs * CXFRT.rtc :=
  match x with
  | XIMemset => let bcc := CXFRTL.mkbc_c c (kn cs) in (APCL.summary_fill_b A nx0 (fst bcc) cs (x_imemset A) 256, snd bcc)
  | XMemset => let bcc := CXFRTL.mkbc_c c (kn cs) in (APCL.summary_fill_b A nx0 (fst bcc) cs (x_memset A) AX2L.two64, snd bcc)
  | XIMemcpy => let bcc := CXFRTL.mkbc_c c (kn cs) in (APCL.summary_copy_b segs A nx0 (fst bcc) cs (x_imemcpy A), snd bcc)
  | XMemcpy => let bcc := CXFRTL.mkbc_c c (kn cs) in (APCL.summary_copy_b segs A nx0 (fst bcc) cs (x_memcpy A), snd bcc)
  | XMemIsZero => let bcc := CXFRTL.mkbc_c c (kn cs) in (APCL.summary_miz_b A nx0 (fst bcc) cs, snd bcc)
  | _ => (CAPL.node_x segs A nx0 x args cs, c)
  end.
Lemma node_x_c_spec : forall segs A nx0 c, CXFRT.rtc_ok c -> forall x args cs,
  fst (node_x_c segs A nx0 c x args cs) = CAP.node_x segs A nx0 x args cs /\ CXFRT.rtc_ok (snd (node_x_c segs A nx0 c x args cs)).
Proof.
  intros segs A nx0 c Hc x args cs. rewrite <- CAPL.L_CAPL_node_x.
  destruct (CXFRT.mkbc_c_spec c (kn cs) Hc) as [E1 E2]. rewrite <- AX2BL.L_AX2BL_mkbc in E1. rewrite <- CXFRTL.L_CXFRTL_mkbc_c in E1, E2.
  destruct x; unfold node_x_c; cbv zeta; cbn [fst snd]; unfold CXFRTL.rtc, CXFRT.rtc in *.
  - rewrite E1. split; [|exact E2]. change (CAPL.node_x segs A nx0 XIMemset args cs) with (APCL.summary_fill A nx0 cs (x_imemset A) 256). apply APCL.summary_fill_b_ok.
  - rewrite E1. split; [|exact E2]. change (CAPL.node_x segs A nx0 XIMemcpy args cs) with (APCL.summary_copy segs A nx0 cs (x_imemcpy A)). apply APCL.summary_copy_b_ok.
  - rewrite E1. split; [|exact E2]. change (CAPL.node_x segs A nx0 XMemset args cs) with (APCL.summary_fill A nx0 cs (x_memset A) AX2L.two64). apply APCL.summary_fill_b_ok.
  - rewrite E1. split; [|exact E2]. change (CAPL.node_x segs A nx0 XMemcpy args cs) with (APCL.summary_copy segs A nx0 cs (x_memcpy A)). apply APCL.summary_copy_b_ok.
  - rewrite E1. split; [|exact E2]. change (CAPL.node_x segs A nx0 XMemIsZero args cs) with (APCL.summary_miz A nx0 cs). apply APCL.summary_miz_b_ok.
  - split; [reflexivity|exact Hc].
  - split; [reflexivity|exact Hc].
  - split; [reflexivity|exact Hc].
  - split; [reflexivity|exact Hc].
  - split; [reflexivity|exact Hc].
  - split; [reflexivity|exact Hc].
Qed.
Definition check_x (segs : list Segment) (IT : itab) (A : atable) (nx0 : nat) (LIMIT : Z)
  (XN : nat -> list expr -> acs -> option acs) (XE : nat -> list expr -> acs -> option (Z * list spiece * acs))
  (XB : nat -> list expr -> acs -> option (acs * acs)) (HS : nat -> option acs) (KC : nat) (FO SPIN GC : bool) (bfuel : nat)
  (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
  CXFPCL.check_c segs IT A nx0 LIMIT XN XE XB HS FO SPIN (CXFEL.RB_c segs IT GC KC bfuel) (node_x_c segs A nx0) CXFNL.node_respell_c (APCL.entails_x segs A nx0)
                 fuel lc None cs p.
Theorem check_x_eq : forall segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p,
  check_x segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p
  = CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p.
Proof.
  intros. unfold check_x. rewrite CXFPCL.L_CXFPCL_check_c.
  rewrite (CXFPC.check_c_eq segs IT A nx0 LIMIT XN XE XB HS FO SPIN (CXFEL.RB_c segs IT GC KC bfuel) (node_x_c segs A nx0) CXFNL.node_respell_c (APCL.entails_x segs A nx0)
             (CXFE.RB_f segs IT GC KC bfuel) (CAP.node_x segs A nx0) CXFN.node_respell_f).
  - apply CXFP.check_g_eq; intros; [apply CXFE.RB_f_eq | reflexivity | apply CXFN.node_respell_f_eq | rewrite APCL.L_APCL_entails_x; reflexivity].
  - intros c Hc cs0 r e. rewrite CXFNL.L_CXFNL_node_respell_c. apply CXFN.node_respell_c_eq. exact Hc.
  - intros c Hc gb st cs0. rewrite CXFEL.L_CXFEL_RB_c. apply CXFE.RB_c_spec. exact Hc.
  - intros c Hc x args cs0. apply node_x_c_spec. exact Hc.
  - exact I.
Qed.
Lemma check_x_intro : forall segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p r,
  check_x segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r ->
  CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r.
Proof. intros. rewrite <- check_x_eq. assumption. Qed.
Lemma check_x_hooks : forall segs IT A nx0 LIMIT XN XE XB HS XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p r,
  (forall id args c, XN' id args c = XN id args c) -> (forall id args c, XE' id args c = XE id args c) ->
  (forall id args c, XB' id args c = XB id args c) -> (forall h, HS' h = HS h) ->
  check_x segs IT A nx0 LIMIT XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p = r ->
  CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r.
Proof.
  intros segs IT A nx0 LIMIT XN XE XB HS XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p r H1 H2 H3 H4 H.
  assert (E1 : XN' = XN) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H1).
  assert (E2 : XE' = XE) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H2).
  assert (E3 : XB' = XB) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H3).
  assert (E4 : HS' = HS) by (apply functional_extensionality; intros h; apply H4).
  subst XN' XE' XB' HS'. apply check_x_intro. exact H.
Qed.

End CXFF.
