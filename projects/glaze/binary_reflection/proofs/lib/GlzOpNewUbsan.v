(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocUbsanIface OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.MuslCall OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.LibWritev OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocUbsanIface OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.   (* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation "'W8' v" := (word_to_le_bytes 8 v) (at level 10, v at level 9).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FENCE.
Context {fx : FPState}.


End FENCE.

Ltac kept_in := cbv [In]; tauto.
Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
Proof. intros v. apply length_N_to_le_bytes. Qed.



Section PIECES.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Definition nw_mem1 (M : word -> option byte) (sp ra s0 : word) : word -> option byte :=
  wbytes (wbytes M (Z_to_bv 64 (bv_unsigned sp - 8)) (W8 ra)) (Z_to_bv 64 (bv_unsigned sp - 16)) (W8 s0).

Lemma nw_mem1_out : forall M sp ra s0 (a : word),
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned a < bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a)%Z -> nw_mem1 M sp ra s0 a = M a.
Proof using.
  intros M sp ra s0 a Hsp Ha. pose proof (u64_range sp). unfold nw_mem1.
  rewrite !wbytes_outside; rewrite ?lenW8; u_norm; try lia; reflexivity.
Qed.

Lemma nw_mem1_grows : forall M sp ra s0, mem_grows M (nw_mem1 M sp ra s0).
Proof using.
  intros. unfold nw_mem1. eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
Qed.

Lemma nw_rd_ra : forall M sp ra s0, (16 <= bv_unsigned sp)%Z ->
  rdn USEGS (nw_mem1 M sp ra s0) (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = Some (W8 ra).
Proof using.
  intros. pose proof (u64_range sp). unfold nw_mem1.
  rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
  apply rdn_wbytes_hit8. u_norm. lia.
Qed.

Lemma nw_rd_s0 : forall M sp ra s0, (16 <= bv_unsigned sp)%Z ->
  rdn USEGS (nw_mem1 M sp ra s0) (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = Some (W8 s0).
Proof using.
  intros. pose proof (u64_range sp). unfold nw_mem1. apply rdn_wbytes_hit8. u_norm. lia.
Qed.

(* [comment removed for export] *)
Ltac okstk :=
  store_ok_peel;
  match goal with
  | Hs : store_ok _ ?M0 (Z_to_bv 64 (bv_unsigned ?sp0 - ?k)) ?N = true |- store_ok _ ?M0' _ ?n = true =>
      constr_eq M0 M0';
      eapply (store_ok_sub _ M0 (Z_to_bv 64 (bv_unsigned sp0 - k)) _ N n);
      [u_norm; cbn; lia | exact Hs | u_norm; lia | u_norm; cbn; lia]
  end.
(* [comment removed for export] *)
Ltac msd F D aa :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
      | gres; rwH; reflexivity
      | okstk ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac mld8 F D vv RD :=
  chain_step; [reflexivity
    | eapply step_ld with (v := vv);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          lazymatch type of RD with rdn _ _ ?c _ = _ =>
            replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
        exact RD
      | apply bytes_le_to_Z_8 ]
    | step_simpl]; vnorm.

(* [comment removed for export] *)
Lemma opnew_pro : forall regs M (sp ra a0 s0 : word),
  getr regs 2 = sp -> getr regs 1 = ra -> getr regs 10 = a0 -> getr regs 8 = s0 ->
  (bv_unsigned a0 <> 0)%Z -> (16 <= bv_unsigned sp)%Z ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true ->
  exists r1,
    msteps USEGS (mkst regs (0x749a4 : word) M rom) (mkst r1 (0x662d0 : word) (nw_mem1 M sp ra s0) rom)
    /\ getr r1 1 = (0x749c0 : word) /\ getr r1 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr r1 10 = a0 /\ getr r1 8 = a0
    /\ (forall x : Z, In x [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%Z -> getr r1 (Z_to_bv 5 x) = getr regs (Z_to_bv 5 x)).
Proof using.
  intros regs M sp ra a0 s0 H2 H1 H10 H8 Ha0 Hsp Hstk.
  pose proof (u64_range sp) as Hspr. pose proof (u64_range a0) as Ha0r.
  eexists. split.
  - stepiv F_74950 D_74950 (Z_to_bv 64 (bv_unsigned sp - 16))
      ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).      (* [comment removed for export] *)
    msd F_74954 D_74954 (Z_to_bv 64 (bv_unsigned sp - 8)).           (* [comment removed for export] *)
    msd F_74958 D_74958 (Z_to_bv 64 (bv_unsigned sp - 16)).          (* [comment removed for export] *)
    stepiv F_7495c D_7495c (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_sltiu; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z; destruct (Z.ltb_spec (bv_unsigned a0) 1); [lia|reflexivity]).
                                                                      (* [comment removed for export] *)
    stepiv F_74960 D_74960 a0
      ltac:(gres; rwH; apply v_add_0_r).                              (* [comment removed for export] *)
    stepn F_74964 D_74964.                                            (* [comment removed for export] *)
    stepn F_74968 D_74968.                                            (* [comment removed for export] *)
    rwH. unfold nw_mem1. pu_refl.
  - repeat split; gres; rwH; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma opnew_epi1 : forall r (M' : word -> option byte) (sp ra s0 p : word),
  getr r 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr r 10 = p -> (bv_unsigned p <> 0)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  rdn USEGS M' (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = Some (W8 ra) ->
  rdn USEGS M' (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = Some (W8 s0) ->
  ret_ok ra ->
  exists r2,
    msteps USEGS (mkst r (0x749c0 : word) M' rom) (mkst r2 ra M' rom)
    /\ getr r2 1 = ra /\ getr r2 2 = sp /\ getr r2 8 = s0 /\ getr r2 10 = p
    /\ (forall x : Z, In x [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%Z -> getr r2 (Z_to_bv 5 x) = getr r (Z_to_bv 5 x)).
Proof using.
  intros r M' sp ra s0 p H2 H10 Hp Hsp RDra RDs0 Hret.
  pose proof (u64_range sp) as Hspr. pose proof (u64_range p) as Hpr.
  eexists. split.
  - stepb_tk F_7496c D_7496c ltac:(rwH; apply c_eq_neq; unorm; cbn; lia).    (* [comment removed for export] *)
    mld8 F_74988 D_74988 ra RDra.                                       (* [comment removed for export] *)
    mld8 F_7498c D_7498c s0 RDs0.                                       (* [comment removed for export] *)
    stepiv F_74990 D_74990 sp
      ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                        (* [comment removed for export] *)
    stepret F_74994 D_74994 ra ltac:(reflexivity).
    pu_refl.
  - repeat split; gres; rwH; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma opdel_jj : forall regs M,
  msteps USEGS (mkst regs (0x5a5a4 : word) M rom) (mkst regs (0x66190 : word) M rom).
Proof using.
  intros. stepn F_5a544 D_5a544. stepn F_5a540 D_5a540. pu_refl.
Qed.
Lemma opdel_sized_j : forall regs M,
  msteps USEGS (mkst regs (0x5a5a0 : word) M rom) (mkst regs (0x66190 : word) M rom).
Proof using.
  intros. stepn F_5a540 D_5a540. pu_refl.
Qed.



End PIECES.

(* [comment removed for export] *)
Close Scope bv_scope.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KGEN.
Context {fx : FPState}.
Variable segs : list Segment.



(* [comment removed for export] *)
Lemma K_msteps : forall (K : config -> Prop) ms ms' model,
  kclosed segs K -> m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' -> K (mkCfg ms' model) -> K (mkCfg ms model).
Proof using.
  intros K ms ms' model HK Hh Hl Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hst Hms IH]; intros Hk; [exact Hk|].
  apply (HK _ unit tt (fun _ => mkCfg ms1 model)).
  - apply node_instr; assumption.
  - intros []. apply IH. exact Hk.
Qed.
End KGEN.

Lemma wbytes_changed_some : forall bs m (a x : word), wbytes m a bs x <> m x -> wbytes m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn [wbytes] in *; [congruence|].
  set (m' := fun y : word => if bv_eqb y a then Some b else m y) in *.
  destruct (decide (wbytes m' (a + 1) bs x = m' x)) as [E|NE].
  - rewrite E in *. unfold m' in *. destruct (bv_eqb x a); [discriminate | congruence].
  - exact (IH m' (a + 1)%bv x NE).
Qed.

Lemma changed_some_layer : forall (m X : word -> option byte) (a : word) bs (x : word),
  (X x <> m x -> X x <> None) -> wbytes X a bs x <> m x -> wbytes X a bs x <> None.
Proof.
  intros m X a bs x IH H. destruct (decide (wbytes X a bs x = X x)) as [E|NE].
  - rewrite E in *. exact (IH H).
  - exact (wbytes_changed_some bs X a x NE).
Qed.
Ltac changed_some := repeat apply changed_some_layer; congruence.

(* [comment removed for export] *)
Lemma zreg : forall z (H : BvWf 5 z), Z_to_bv 5 z = @BV 5 z H.
Proof. intros z H. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_wf_in_range. exact H. Qed.
(* [comment removed for export] *)
Ltac csrw CS k :=
  let E := fresh "E" in
  pose proof (CS k%Z ltac:(cbv; tauto)) as E; rewrite ?(zreg k I) in E; rewrite E; clear E.
Ltac csrwH CS k H :=
  let E := fresh "E" in
  pose proof (CS k%Z ltac:(cbv; tauto)) as E; rewrite ?(zreg k I) in E; rewrite E in H; clear E.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RETRY.
Context {fx : FPState} {RN : run_ceil}.
(* [comment removed for export] *)
Variable AINV : ainv_t.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis HMW : MALLOC_KATW AINV MSTK_M.

(* [comment removed for export] *)
Hypothesis AINV_stack : forall L B C M M' mdl,
  AINV L B C M mdl ->
  (forall a : word, M' a <> M a -> CEIL <= bv_unsigned a /\ M' a <> None) ->
  AINV L B C M' mdl.

(* [comment removed for export] *)
Lemma zbv_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof using. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.
Lemma store_ok1_ext : forall segs (M M' : word -> option byte) (a : word),
  M' a = M a -> store_ok segs M' a 1%nat = store_ok segs M a 1%nat.
Proof using. intros segs M M' a E. cbn [store_ok]. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (mdl0 : Model) (Lc : list (Z * Z)) (B C ret n sp0 : Z).
Hypothesis HA0 : AINV Lc B C M0 mdl0.
Hypothesis HPRE : malloc_pre (MSTK_M + 16) R0 M0 mdl0 B C ret n sp0.

Definition rom : word -> option byte := seg_rom RSEGS.
Definition spw : word := getr R0 2.
Definition sp1w : word := Z_to_bv 64 (sp0 - 16).
Definition nw : word := getr R0 10.
Definition retw : word := Z_to_bv 64 ret.

(* [comment removed for export] *)
Definition HMEM (M : word -> option byte) : Prop :=
  rdn RSEGS M (Z_to_bv 64 (sp0 - 8)) 8 = Some (W8 retw) /\
  rdn RSEGS M (Z_to_bv 64 (sp0 - 16)) 8 = Some (W8 (getr R0 8)) /\
  (forall a : word, M a <> M0 a -> mh_changed (MSTK_M + 16) Lc sp0 a) /\
  (forall a : word, sp0 - (MSTK_M + 16) <= bv_unsigned a < sp0 -> store_ok RSEGS M a 1%nat = true).
Definition HMDL (mdl : Model) : Prop :=
  m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\ m_fs mdl = m_fs mdl0 /\ m_fds mdl = m_fds mdl0.
Definition CSV : list Z := [3; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%Z.
Definition QQ : config -> Prop := malloc_ok AINV (MSTK_M + 16) R0 M0 mdl0 Lc B C ret n sp0.

(* [comment removed for export] *)
Lemma pre_facts :
  m_halted mdl0 = None /\ m_vm_lazy mdl0 = [] /\ m_vm_materialized mdl0 = [] /\
  getr R0 1 = retw /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
  bv_unsigned nw = n /\ 1 <= n <= MH_NMAX /\
  bv_unsigned spw = sp0 /\ sp0 mod 16 = 0 /\ CEIL + (MSTK_M + 16) <= sp0 /\
  getr R0 4 = Z_to_bv 64 TPV /\
  (forall a : word, sp0 - (MSTK_M + 16) <= bv_unsigned a < sp0 -> store_ok RSEGS M0 a 1%nat = true) /\
  B + (n + MBLK) <= MH_GBUDGET /\ C + 1 <= LMAX.
Proof using HPRE. exact HPRE. Qed.

Lemma sp0_rng : CEIL0 <= CEIL /\ CEIL + 1296 <= sp0 /\ sp0 < 2 ^ 64.
Proof using HPRE n ret C B mdl0 M0 R0.
  destruct pre_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Hsp & _ & Hc & _). ceil. unfold MSTK_M in Hc.
  pose proof (u64_range spw). lia.
Qed.
Lemma sp1w_u : bv_unsigned sp1w = sp0 - 16.
Proof using HPRE n ret C B mdl0 M0 R0 RN. unfold sp1w. pose proof sp0_rng. apply u_Z2bv; lia. Qed.

(* [comment removed for export] *)
Lemma hmem_pro : HMEM (nw_mem1 M0 spw retw (getr R0 8)).
Proof using HPRE n C B mdl0.
  destruct pre_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Hsp & _ & Hc & _ & Hstk & _). pose proof sp0_rng as SR.
  pose proof (u64_range spw) as Hspr.
  split; [|split; [|split]].
  - rewrite <- Hsp. apply nw_rd_ra. lia.
  - rewrite <- Hsp. apply nw_rd_s0. lia.
  - intros a Hne. right; left. unfold MSTK_M.
    destruct (Z_lt_ge_dec (bv_unsigned a) (sp0 - 16)) as [Hl|Hg]; [exfalso; apply Hne; apply nw_mem1_out; lia|].
    destruct (Z_lt_ge_dec (bv_unsigned a) sp0) as [Hl2|Hg2]; [lia | exfalso; apply Hne; apply nw_mem1_out; lia].
  - intros a Ha. eapply store_ok_mono; [apply nw_mem1_grows | apply Hstk; exact Ha].
Qed.

Lemma hmem_after_malloc : forall Mx M', HMEM Mx ->
  (forall a : word, M' a <> Mx a -> mh_changed MSTK_M Lc (sp0 - 16) a) ->
  (forall a : word, sp0 - 16 - MSTK_M <= bv_unsigned a < sp0 - 16 -> store_ok RSEGS M' a 1%nat = true) ->
  HMEM M'.
Proof using HPRE n C B mdl0.
  intros Mx M' (R8 & R16 & CH & ST) CH' ST'. pose proof sp0_rng as SR. ceil.
  assert (AG : forall x : word, sp0 - 16 <= bv_unsigned x -> M' x = Mx x).
  { intros x Hx. destruct (decide (M' x = Mx x)) as [E|NE]; [exact E|]. exfalso.
    pose proof (CH' x NE) as X. unfold mh_changed, MSTK_M, HEAPLO, CTX_END, CTX, A_ERRNO, TPV in X.
    destruct X as [(X1 & X2 & _)|[X|[X|X]]]; lia. }
  split; [|split; [|split]].
  - rewrite (rdn_ext RSEGS 8 M' Mx); [exact R8 | u_norm; lia | intros x Hx; apply AG; revert Hx; u_norm; lia].
  - rewrite (rdn_ext RSEGS 8 M' Mx); [exact R16 | u_norm; lia | intros x Hx; apply AG; revert Hx; u_norm; lia].
  - intros a Hne. destruct (decide (M' a = Mx a)) as [E|NE].
    + apply CH. rewrite <- E. exact Hne.
    + pose proof (CH' a NE) as X. unfold mh_changed, MSTK_M in *.
      destruct X as [X|[X|[X|X]]]; [left; exact X | right; left; lia | right; right; left; exact X | right; right; right; exact X].
  - intros a Ha. unfold MSTK_M in *.
    destruct (Z_lt_ge_dec (bv_unsigned a) (sp0 - 16)) as [Hl|Hg].
    + apply ST'. lia.
    + rewrite (store_ok1_ext RSEGS Mx M' a (AG a ltac:(lia))). apply ST. lia.
Qed.

Lemma ainv_pro : AINV Lc B C (nw_mem1 M0 spw retw (getr R0 8)) mdl0.
Proof using HPRE HA0 sp0 n AINV_stack RN.
  destruct pre_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Hsp & _). pose proof sp0_rng as SR. pose proof (u64_range spw).
  apply (AINV_stack Lc B C M0); [exact HA0|]. intros a Hne. split.
  - destruct (Z_lt_ge_dec (bv_unsigned a) (sp0 - 16)) as [H1|H1]; [exfalso; apply Hne; apply nw_mem1_out; lia|].
    destruct (Z_lt_ge_dec (bv_unsigned a) sp0) as [H2|H2]; [lia | exfalso; apply Hne; apply nw_mem1_out; lia].
  - revert Hne. unfold nw_mem1. changed_some.
Qed.

(* [comment removed for export] *)
Lemma call_K : forall (K : config -> Prop) rx Mx mdlx retk,
  kclosed RSEGS K -> AINV Lc B C Mx mdlx -> malloc_pre MSTK_M rx Mx mdlx B C retk n (sp0 - 16) ->
  (forall c3, malloc_ok AINV MSTK_M rx Mx mdlx Lc B C retk n (sp0 - 16) c3 -> K c3) ->
  K (mkCfg (mkst rx (0x662d0%bv : word) Mx rom) mdlx).
Proof using HMW.
  intros K rx Mx mdlx retk HK HA HP Hok.
  pose proof (katw_ok_only RSEGS _ _ _ (HMW rx Mx mdlx Lc B C retk n (sp0 - 16) HA HP)) as W.
  unfold malloc_cfg, A_MALLOC in W. rewrite (zbv_lit 0x662d0 (0x662d0%bv : word) eq_refl) in W.
  exact (W K HK Hok).
Qed.

(* [comment removed for export] *)
Lemma mpre_of : forall rx Mx mdlx retk,
  HMEM Mx -> HMDL mdlx ->
  getr rx 1 = Z_to_bv 64 retk -> 0 <= retk < 2 ^ 64 -> retk mod 2 = 0 ->
  getr rx 10 = nw -> getr rx 2 = sp1w -> getr rx 4 = Z_to_bv 64 0x8ab90 ->
  malloc_pre MSTK_M rx Mx mdlx B C retk n (sp0 - 16).
Proof using HPRE.
  intros rx Mx mdlx retk (_ & _ & _ & ST) (Hh & Hl & Hm & _ & _) H1 Hrk Hev H10 H2 H4.
  destruct pre_facts as (_ & _ & _ & _ & _ & _ & Hn & Hnr & Hsp & Hal & Hc & _ & _ & Hb & Hcn). pose proof sp0_rng as SR.
  unfold malloc_pre. rewrite H10, H2, sp1w_u.
  repeat match goal with |- _ /\ _ => split end; try assumption; try (unfold MSTK_M in *; lia).
  - rewrite <- Zminus_mod_idemp_l, Hal. reflexivity.
  - intros a Ha. apply ST. unfold MSTK_M in *. lia.
Qed.

(* [comment removed for export] *)
Definition CSR (r : bvmap 5 word) : Prop := forall x : Z, In x CSV -> getr r (Z_to_bv 5 x) = getr R0 (Z_to_bv 5 x).

(* [comment removed for export] *)
Ltac olit r := lazymatch r with @BV _ ?z _ => olit z | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac olits G := lazymatch G with False => idtac | (?a = ?b) \/ ?R => olit a; olit b; olits R | ?a = ?b => olit a; olit b end.
Ltac lit_in := first [ solve [ repeat first [ left; reflexivity | right ] ] | lazymatch goal with |- ?G => tryif olits G then fail else tauto end ].
Ltac in_cases Hx := cbv in Hx; repeat (destruct Hx as [<-|Hx]; [|]); [..| destruct Hx].

(* [comment removed for export] *)
Lemma exit_K : forall (K : config -> Prop) rx Mx mdlx c3,
  kclosed RSEGS K -> (forall d, QQ d -> K d) ->
  HMEM Mx -> HMDL mdlx -> CSR rx -> getr rx 2 = sp1w -> getr rx 4 = Z_to_bv 64 0x8ab90 ->
  malloc_ok AINV MSTK_M rx Mx mdlx Lc B C 0x749c0 n (sp0 - 16) c3 -> K c3.
Proof using HPRE.
  intros K rx Mx mdlx c3 HK HQK HMx (Hhx & Hlx & Hmx & Hfsx & Hfdx) CSx R2 R4
         (R' & M' & mdl' & p & -> & RK & H10 & Hal & Hblk & Hdisj & Hdef & CH' & ST' & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
  destruct pre_facts as (_ & _ & _ & _ & Hrr & Hre & _ & _ & Hsp & _ & _ & HT4 & _). pose proof sp0_rng as SR.
  pose proof (hmem_after_malloc Mx M' HMx CH' ST') as HM'. destruct HM' as (M8 & M16 & MCH & MST).
  assert (R'2 : getr R' 2 = Z_to_bv 64 (bv_unsigned spw - 16)) by (rewrite Hsp; csrw RK 2; exact R2).
  assert (Hp : bv_unsigned p <> 0) by (destruct Hblk as [B1 _]; unfold HEAPLO in B1; lia).
  assert (Hro : ret_ok retw) by (apply ret_ok_even; unfold retw; u_norm; exact Hre).
  rewrite <- Hsp in M8, M16.
  destruct (opnew_epi1 rom R' M' spw retw (getr R0 8) p R'2 H10 Hp ltac:(lia) M8 M16 Hro) as (r4 & S4 & H41 & H42 & H48 & H410 & CS4).
  rewrite (zbv_lit 0x749c0 (0x749c0%bv : word) eq_refl).
  apply (K_msteps RSEGS K _ _ mdl' HK Hh' Hl' S4). apply HQK.
  unfold QQ, malloc_ok. exists r4, M', mdl', p.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - reflexivity.
  - intros x Hx. in_cases Hx;
    first [ rewrite (zreg 2 I); exact H42
          | rewrite (zreg 8 I); exact H48
          | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
              rewrite (CS4 k ltac:(cbv; lit_in)), (RK k ltac:(cbv; lit_in)) end;
            first [ apply CSx; cbv; lit_in | rewrite (zreg 4 I), R4, HT4; reflexivity ] ].
  - rewrite Hfs'. exact Hfsx.
  - rewrite Hfd'. exact Hfdx.
Qed.

(* [comment removed for export] *)
Theorem opnew_retry : forall T,
  T [] ->
  (forall d, QQ d -> realizes RSEGS d T) ->
  realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x749a4) M0 rom) mdl0) T.
Proof using HPRE HA0 AINV_stack HMW.
  intros T HT HQ.
  destruct pre_facts as (Hh & Hl & Hm & Hra & Hrr & Hre & Hn & Hnr & Hsp & Hal & Hc & HT4 & Hstk & _). pose proof sp0_rng as SR.
  pose proof (u64_range spw) as Hspr.
  assert (ST16 : store_ok USEGS M0 (Z_to_bv 64 (bv_unsigned spw - 16)) 16 = true).
  { apply store_ok_of_all; [u_norm; lia|]. intros x Hx. revert Hx; u_norm; intros Hx.
    pose proof (Hstk x ltac:(unfold MSTK_M; lia)) as S. cbn [store_ok] in S. destruct (wview USEGS M0 x); [discriminate | discriminate S]. }
  destruct (opnew_pro rom R0 M0 spw retw nw (getr R0 8) eq_refl Hra eq_refl eq_refl ltac:(lia) ltac:(lia) ST16)
    as (r1 & S1 & H11 & H12 & H110 & H18 & CS1).
  rewrite (zbv_lit 0x749a4 (0x749a4%bv : word) eq_refl).
  apply (rz_msteps RSEGS _ _ mdl0 T Hh Hl S1).
  assert (HD0 : HMDL mdl0) by (split; [exact Hh | split; [exact Hl | split; [exact Hm | split; reflexivity]]]).
  assert (R12 : getr r1 2 = sp1w) by (rewrite H12, Hsp; reflexivity).
  assert (R14 : getr r1 4 = Z_to_bv 64 0x8ab90) by (csrw CS1 4; exact HT4).
  assert (CSR1 : CSR r1) by (intros x Hx; apply CS1; revert Hx; cbv; tauto).
  apply (call_K (fun c => realizes RSEGS c T) r1 (nw_mem1 M0 spw retw (getr R0 8)) mdl0 0x749c0).
  - apply (kclosed_realizes RSEGS).
  - apply ainv_pro.
  - apply mpre_of; [apply hmem_pro | exact HD0 | rewrite H11; symmetry; apply zbv_lit; reflexivity | lia | reflexivity | exact H110 | exact R12 | exact R14].
  - intros c3 Hok. exact (exit_K (fun c => realizes RSEGS c T) r1 (nw_mem1 M0 spw retw (getr R0 8)) mdl0 c3
                            (kclosed_realizes RSEGS T) HQ hmem_pro HD0 CSR1 R12 R14 Hok).
Qed.


End RETRY.
