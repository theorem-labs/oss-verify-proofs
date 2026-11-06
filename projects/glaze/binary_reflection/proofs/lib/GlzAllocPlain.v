(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GcFlush.F72_004.   (* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.LinuxProcessSem.Specs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzOpNewPlain.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.MuslCall OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.LibWritev OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0.
   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
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
  rdn PSEGS (nw_mem1 M sp ra s0) (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = Some (W8 ra).
Proof using.
  intros. pose proof (u64_range sp). unfold nw_mem1.
  rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
  apply rdn_wbytes_hit8. u_norm. lia.
Qed.

Lemma nw_rd_s0 : forall M sp ra s0, (16 <= bv_unsigned sp)%Z ->
  rdn PSEGS (nw_mem1 M sp ra s0) (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = Some (W8 s0).
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
  store_ok PSEGS M (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true ->
  exists r1,
    msteps PSEGS (mkst regs (0x70334 : word) M rom) (mkst r1 (0x61c60 : word) (nw_mem1 M sp ra s0) rom)
    /\ getr r1 1 = (0x70350 : word) /\ getr r1 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr r1 10 = a0 /\ getr r1 8 = a0
    /\ (forall x : Z, In x [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%Z -> getr r1 (Z_to_bv 5 x) = getr regs (Z_to_bv 5 x)).
Proof using.
  intros regs M sp ra a0 s0 H2 H1 H10 H8 Ha0 Hsp Hstk.
  pose proof (u64_range sp) as Hspr. pose proof (u64_range a0) as Ha0r.
  eexists. split.
  - stepiv F_702e0 D_702e0 (Z_to_bv 64 (bv_unsigned sp - 16))
      ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).      (* [comment removed for export] *)
    msd F_702e4 D_702e4 (Z_to_bv 64 (bv_unsigned sp - 8)).           (* [comment removed for export] *)
    msd F_702e8 D_702e8 (Z_to_bv 64 (bv_unsigned sp - 16)).          (* [comment removed for export] *)
    stepiv F_702ec D_702ec (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_sltiu; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z; destruct (Z.ltb_spec (bv_unsigned a0) 1); [lia|reflexivity]).
                                                                      (* [comment removed for export] *)
    stepiv F_702f0 D_702f0 a0
      ltac:(gres; rwH; apply v_add_0_r).                              (* [comment removed for export] *)
    stepn F_702f4 D_702f4.                                            (* [comment removed for export] *)
    stepn F_702f8 D_702f8.                                            (* [comment removed for export] *)
    rwH. unfold nw_mem1. pu_refl.
  - repeat split; gres; rwH; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma opnew_epi1 : forall r (M' : word -> option byte) (sp ra s0 p : word),
  getr r 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr r 10 = p -> (bv_unsigned p <> 0)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  rdn PSEGS M' (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = Some (W8 ra) ->
  rdn PSEGS M' (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = Some (W8 s0) ->
  ret_ok ra ->
  exists r2,
    msteps PSEGS (mkst r (0x70350 : word) M' rom) (mkst r2 ra M' rom)
    /\ getr r2 1 = ra /\ getr r2 2 = sp /\ getr r2 8 = s0 /\ getr r2 10 = p
    /\ (forall x : Z, In x [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%Z -> getr r2 (Z_to_bv 5 x) = getr r (Z_to_bv 5 x)).
Proof using.
  intros r M' sp ra s0 p H2 H10 Hp Hsp RDra RDs0 Hret.
  pose proof (u64_range sp) as Hspr. pose proof (u64_range p) as Hpr.
  eexists. split.
  - stepb_tk F_702fc D_702fc ltac:(rwH; apply c_eq_neq; unorm; cbn; lia).    (* [comment removed for export] *)
    mld8 F_70318 D_70318 ra RDra.                                       (* [comment removed for export] *)
    mld8 F_7031c D_7031c s0 RDs0.                                       (* [comment removed for export] *)
    stepiv F_70320 D_70320 sp
      ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                        (* [comment removed for export] *)
    stepret F_70324 D_70324 ra ltac:(reflexivity).
    pu_refl.
  - repeat split; gres; rwH; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma opdel_jj : forall regs M,
  msteps PSEGS (mkst regs (0x55f34 : word) M rom) (mkst regs (0x61b20 : word) M rom).
Proof using.
  intros. stepn F_55ed4 D_55ed4. stepn F_55ed0 D_55ed0. pu_refl.
Qed.
Lemma opdel_sized_j : forall regs M,
  msteps PSEGS (mkst regs (0x55f30 : word) M rom) (mkst regs (0x61b20 : word) M rom).
Proof using.
  intros. stepn F_55ed0 D_55ed0. pu_refl.
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
(* [comment removed for export] *)
Hypothesis HMW : MALLOC_KATW MSTK_M.

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
Proof using HPRE HA0 sp0 n AINV_stack.
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
  K (mkCfg (mkst rx (0x61c60%bv : word) Mx rom) mdlx).
Proof using HMW.
  intros K rx Mx mdlx retk HK HA HP Hok.
  pose proof (katw_ok_only RSEGS _ _ _ (HMW rx Mx mdlx Lc B C retk n (sp0 - 16) HA HP)) as W.
  unfold malloc_cfg, A_MALLOC in W. rewrite (zbv_lit 0x61c60 (0x61c60%bv : word) eq_refl) in W.
  exact (W K HK Hok).
Qed.

(* [comment removed for export] *)
Lemma mpre_of : forall rx Mx mdlx retk,
  HMEM Mx -> HMDL mdlx ->
  getr rx 1 = Z_to_bv 64 retk -> 0 <= retk < 2 ^ 64 -> retk mod 2 = 0 ->
  getr rx 10 = nw -> getr rx 2 = sp1w -> getr rx 4 = Z_to_bv 64 0x86520 ->
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
  HMEM Mx -> HMDL mdlx -> CSR rx -> getr rx 2 = sp1w -> getr rx 4 = Z_to_bv 64 0x86520 ->
  malloc_ok AINV MSTK_M rx Mx mdlx Lc B C 0x70350 n (sp0 - 16) c3 -> K c3.
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
  rewrite (zbv_lit 0x70350 (0x70350%bv : word) eq_refl).
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
  realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x70334) M0 rom) mdl0) T.
Proof using HPRE HA0 AINV_stack HMW.
  intros T HT HQ.
  destruct pre_facts as (Hh & Hl & Hm & Hra & Hrr & Hre & Hn & Hnr & Hsp & Hal & Hc & HT4 & Hstk & _). pose proof sp0_rng as SR.
  pose proof (u64_range spw) as Hspr.
  assert (ST16 : store_ok PSEGS M0 (Z_to_bv 64 (bv_unsigned spw - 16)) 16 = true).
  { apply store_ok_of_all; [u_norm; lia|]. intros x Hx. revert Hx; u_norm; intros Hx.
    pose proof (Hstk x ltac:(unfold MSTK_M; lia)) as S. cbn [store_ok] in S. destruct (wview PSEGS M0 x); [discriminate | discriminate S]. }
  destruct (opnew_pro rom R0 M0 spw retw nw (getr R0 8) eq_refl Hra eq_refl eq_refl ltac:(lia) ltac:(lia) ST16)
    as (r1 & S1 & H11 & H12 & H110 & H18 & CS1).
  rewrite (zbv_lit 0x70334 (0x70334%bv : word) eq_refl).
  apply (rz_msteps RSEGS _ _ mdl0 T Hh Hl S1).
  assert (HD0 : HMDL mdl0) by (split; [exact Hh | split; [exact Hl | split; [exact Hm | split; reflexivity]]]).
  assert (R12 : getr r1 2 = sp1w) by (rewrite H12, Hsp; reflexivity).
  assert (R14 : getr r1 4 = Z_to_bv 64 0x86520) by (csrw CS1 4; exact HT4).
  assert (CSR1 : CSR r1) by (intros x Hx; apply CS1; revert Hx; cbv; tauto).
  apply (call_K (fun c => realizes RSEGS c T) r1 (nw_mem1 M0 spw retw (getr R0 8)) mdl0 0x70350).
  - apply (kclosed_realizes RSEGS).
  - apply ainv_pro.
  - apply mpre_of; [apply hmem_pro | exact HD0 | rewrite H11; symmetry; apply zbv_lit; reflexivity | lia | reflexivity | exact H110 | exact R12 | exact R14].
  - intros c3 Hok. exact (exit_K (fun c => realizes RSEGS c T) r1 (nw_mem1 M0 spw retw (getr R0 8)) mdl0 c3
                            (kclosed_realizes RSEGS T) HQ hmem_pro HD0 CSR1 R12 R14 Hok).
Qed.


End RETRY.
End GlzOpNewPlain.
Require OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizePlain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzStrResizePlain2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizePlain.MuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizePlain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac u_norm ::= pu_u_norm.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation PSEGS := Plain.M.loaded_segments.
#[local] Notation W8 v := (word_to_le_bytes 8 v).
Ltac kept_in := cbv [callee_kept app_saved In]; first [ kin | kin_nt ].   (* [comment removed for export] *)

Section UNIFORM.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem resize_short_any : forall regs M (obj sp ret w0 cw : word) (s n : Z),
  rdn PSEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 256 = 2 * s)%Z ->
  (0 <= s <= 22)%Z -> (0 <= n <= 22)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj)%Z ->
  store_ok PSEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true ->
  store_ok PSEGS M obj 24 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = cw ->
  exists r' M',
    msteps PSEGS (mkst regs (0x57b68 : word) M rom) (mkst r' ret M' rom)
    /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x)
    /\ (forall a : word, M' a <> M a ->
          (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 \/ bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp)%Z)
    /\ mem_grows M M'
    /\ rdn PSEGS M' obj 1 = Some [Z_to_bv 8 (2 * n)]
    /\ M' (Z_to_bv 64 (bv_unsigned obj + 1 + n)) = Some (Z_to_bv 8 0).
Proof using.
  intros regs M obj sp ret w0 cw s n RD8 Hw0 Hs Hn Hobj Hsp Hapart STF STO Hret H1 H2 H10 H11 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range sp) as Hspr.
  assert (STb : forall z m, (0 <= z <= 23)%Z -> (z + Z.of_nat m <= 24)%Z -> store_ok PSEGS M (Z_to_bv 64 (bv_unsigned obj + z)) m = true).
  { intros z m Hz Hm. eapply (store_ok_sub PSEGS M obj _ 24); [cbn; lia | exact STO | u_norm; lia | u_norm; cbn; lia]. }
  assert (ST0 : store_ok PSEGS M obj 1 = true).
  { rewrite <- (Z_to_bv_bv_unsigned 64 obj). rewrite <- (Z.add_0_r (bv_unsigned obj)). apply STb; cbn; lia. }
  destruct (Z.le_gt_cases n s) as [Hle|Hgt].
  - (* [comment removed for export] *)
    assert (ST1 : store_ok PSEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true).
    { replace (bv_unsigned obj + 1 + n)%Z with (bv_unsigned obj + (1 + n))%Z by lia. apply STb; cbn; lia. }
    destruct (resize_short_le rom regs M obj ret w0 s n RD8 Hw0 ltac:(lia) ltac:(lia) Hobj ST0 ST1 Hret H1 H10 H11) as (r' & RUN & K).
    exists r', (wbytes (wbytes M obj [Z_to_bv 8 (2 * n)]) (Z_to_bv 64 (bv_unsigned obj + 1 + n)) [Z_to_bv 8 0]).
    split; [exact RUN|]. split; [rewrite (K 10) by kept_in; exact H10|]. split; [intros x Hx; apply K; kin_from Hx|].
    split; [|split; [|split]].
    + intros a Ha. left.
      assert (OUT : (bv_unsigned a < bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned a)%Z -> False).
      { intros O1. apply Ha. rewrite !wbytes_outside by (cbn; unfold in_rng; u_norm; lia). reflexivity. }
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj)) as [L|L]; [exfalso; apply OUT; lia|].
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 24)) as [U|U]; [lia | exfalso; apply OUT; lia].
    + eapply mem_grows_trans; apply wbytes_grows.
    + rewrite rdn_wbytes_out by (cbn; u_norm; lia). apply (rdn_wbytes_hit PSEGS [Z_to_bv 8 (2 * n)]). cbn. lia.
    + apply (wbytes_fill_at1 _ _ _). 
  - (* [comment removed for export] *)
    assert (ST1 : store_ok PSEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true).
    { replace (bv_unsigned obj + 1 + n)%Z with (bv_unsigned obj + (1 + n))%Z by lia. apply STb; cbn; lia. }
    assert (STM : store_ok PSEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + s)) (Z.to_nat (n - s)) = true).
    { replace (bv_unsigned obj + 1 + s)%Z with (bv_unsigned obj + (1 + s))%Z by lia. apply STb; lia. }
    destruct (resize_short_fill rom regs M obj sp ret w0 cw s n RD8 Hw0 ltac:(lia) ltac:(lia) Hobj Hsp Hapart STF ST0
                STM ST1 Hret H1 H2 H10 H11 H12) as (r' & RUN & A0 & K).
    exists r', (rs_short_fill_mem M sp regs obj cw s n).
    split; [exact RUN|]. split; [exact A0|]. split; [exact K|].
    unfold rs_short_fill_mem. split; [|split; [|split]].
    + intros a Ha.
      assert (OUT : (bv_unsigned a < bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned a)%Z ->
                    (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z -> False).
      { intros O1 O2. apply Ha. rewrite !wbytes_outside by (rewrite ?repeat_length; cbn; unfold in_rng; u_norm; lia).
        apply app_mem1_out; [exact Hsp | exact O2]. }
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj)) as [L|L];
        [| destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 24)) as [U|U]; [left; lia|]];
        right;
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp - 80)) as [L2|L2]; [exfalso; apply OUT; lia|]);
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp)) as [U2|U2]; [lia | exfalso; apply OUT; lia]).
    + eapply mem_grows_trans; [apply app_mem1_grows|]. eapply mem_grows_trans; [apply wbytes_grows|].
      eapply mem_grows_trans; apply wbytes_grows.
    + rewrite rdn_wbytes_out by (cbn; u_norm; lia). apply (rdn_wbytes_hit PSEGS [Z_to_bv 8 (2 * n)]). cbn. lia.
    + apply (wbytes_fill_at1 _ _ _).
Qed.

(* [comment removed for export] *)
Theorem resize_long_inplace_any : forall regs M (obj sp ret d w0 cw : word) (cap s n : Z),
  rdn PSEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 = cap + 2)%Z -> ((cap + 1) mod 2 = 0)%Z ->
  rdn PSEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
  rdn PSEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
  (0 <= s <= cap)%Z -> (0 <= n <= cap)%Z -> (cap < 2 ^ 62)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (bv_unsigned d + cap + 1 <= 2 ^ 64)%Z -> (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj)%Z ->
  (bv_unsigned d + cap + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned d)%Z ->
  (bv_unsigned d + cap + 1 <= bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned d)%Z ->
  store_ok PSEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true ->
  store_ok PSEGS M obj 24 = true ->
  store_ok PSEGS M d (Z.to_nat (cap + 1)) = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = cw ->
  exists r' M',
    msteps PSEGS (mkst regs (0x57b68 : word) M rom) (mkst r' ret M' rom)
    /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x)
    /\ (forall a : word, M' a <> M a ->
          (bv_unsigned obj + 8 <= bv_unsigned a < bv_unsigned obj + 16
           \/ bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1
           \/ bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp)%Z)
    /\ mem_grows M M'
    /\ rdn PSEGS M' obj 8 = Some (W8 w0)
    /\ rdn PSEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n))
    /\ rdn PSEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d)
    /\ M' (Z_to_bv 64 (bv_unsigned d + n)) = Some (Z_to_bv 8 0).
Proof using.
  intros regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd Hs Hn Hcap62 Hobj Hd Hsp Hapart Hdfr Hdobj STF STO STD
         Hret H1 H2 H10 H11 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range sp) as Hspr. pose proof (u64_range d) as Hdr.
  assert (Odd : (bv_unsigned w0 mod 2 = 1)%Z).
  { rewrite Hw0. replace (cap + 2)%Z with (cap + 1 + 1)%Z by lia. rewrite Z.add_mod, Hcap by lia. reflexivity. }
  assert (ST8 : store_ok PSEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true).
  { eapply (store_ok_sub PSEGS M obj _ 24); [cbn; lia | exact STO | u_norm; lia | u_norm; cbn; lia]. }
  assert (STDb : forall z m, (0 <= z <= cap)%Z -> (z + Z.of_nat m <= cap + 1)%Z -> store_ok PSEGS M (Z_to_bv 64 (bv_unsigned d + z)) m = true).
  { intros z m Hz Hm. eapply (store_ok_sub PSEGS M d _ (Z.to_nat (cap + 1))); [lia | exact STD | u_norm; lia | u_norm; lia]. }
  assert (ST1 : store_ok PSEGS M (Z_to_bv 64 (bv_unsigned d + n)) 1 = true) by (apply STDb; cbn; lia).
  destruct (Z.le_gt_cases n s) as [Hle|Hgt].
  - (* [comment removed for export] *)
    destruct (resize_long_le rom regs M obj ret w0 d s n RD8 Odd RDs RDd ltac:(lia) ltac:(lia) Hobj ltac:(lia) ST8 ST1 Hret H1 H10 H11)
      as (r' & RUN & K).
    exists r', (wbytes (wbytes M (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 n))) (Z_to_bv 64 (bv_unsigned d + n)) [Z_to_bv 8 0]).
    split; [exact RUN|]. split; [rewrite (K 10) by kept_in; exact H10|]. split; [intros x Hx; apply K; kin_from Hx|].
    split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha.
      assert (OUT : (bv_unsigned a < bv_unsigned obj + 8 \/ bv_unsigned obj + 16 <= bv_unsigned a)%Z ->
                    bv_unsigned a <> (bv_unsigned d + n)%Z -> False).
      { intros O1 O2. apply Ha. rewrite !wbytes_outside by (rewrite ?lenW8; cbn; unfold in_rng; u_norm; lia). reflexivity. }
      destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned d + n)) as [E|NE]; [right; left; lia|].
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 8)) as [L|L]; [exfalso; apply OUT; lia|].
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 16)) as [U|U]; [left; lia | exfalso; apply OUT; lia].
    + eapply mem_grows_trans; apply wbytes_grows.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). exact RD8.
    + rewrite rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). apply rdn_wbytes_hit8. u_norm. lia.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). exact RDd.
    + apply (wbytes_fill_at1 _ _ _).
  - (* [comment removed for export] *)
    assert (STM : store_ok PSEGS M (Z_to_bv 64 (bv_unsigned d + s)) (Z.to_nat (n - s)) = true) by (apply STDb; lia).
    destruct (resize_long_fill rom regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd ltac:(lia) ltac:(lia) Hcap62 Hobj Hd Hsp
                Hapart Hdfr Hdobj STF ST8 STM ST1 Hret H1 H2 H10 H11 H12) as (r' & RUN & A0 & K).
    exists r', (rs_long_fill_mem M sp regs obj d cw s n).
    split; [exact RUN|]. split; [exact A0|]. split; [exact K|].
    unfold rs_long_fill_mem.
    assert (AOUT : forall a : word, (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z ->
                   app_mem1 M sp regs a = M a) by (intros a Ha; apply app_mem1_out; [exact Hsp | exact Ha]).
    split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha.
      assert (OUT : (bv_unsigned a < bv_unsigned obj + 8 \/ bv_unsigned obj + 16 <= bv_unsigned a)%Z ->
                    (bv_unsigned a < bv_unsigned d \/ bv_unsigned d + cap + 1 <= bv_unsigned a)%Z ->
                    (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z -> False).
      { intros O1 O2 O3. apply Ha. rewrite !wbytes_outside by (rewrite ?lenW8, ?repeat_length; cbn; unfold in_rng; u_norm; lia).
        apply AOUT. exact O3. }
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned d)) as [L1|L1];
        [| destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned d + cap + 1)) as [U1|U1]; [right; left; lia|]];
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 8)) as [L|L];
          [| destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 16)) as [U|U]; [left; lia|]]);
        right; right;
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp - 80)) as [L2|L2]; [exfalso; apply OUT; lia|]);
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp)) as [U2|U2]; [lia | exfalso; apply OUT; lia]).
    + eapply mem_grows_trans; [apply app_mem1_grows|]. eapply mem_grows_trans; [apply wbytes_grows|].
      eapply mem_grows_trans; apply wbytes_grows.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8, ?repeat_length; cbn; u_norm; lia).
      rewrite <- RD8. apply rdn_ext; [cbn; lia|]. intros x Hx. apply AOUT. cbn in Hx. lia.
    + rewrite rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). apply rdn_wbytes_hit8. u_norm. lia.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8, ?repeat_length; cbn; u_norm; lia).
      rewrite <- RDd. apply rdn_ext; [cbn; u_norm; lia|]. intros x Hx. apply AOUT. revert Hx. u_norm. cbn. intros Hx. lia.
    + apply (wbytes_fill_at1 _ _ _).
Qed.

End UNIFORM.
End GlzStrResizePlain2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesResize OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowPlain2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowPlain3 OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzStrSpecsPlain.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrameStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesResize GlzStrResizePlain2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowPlain2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowPlain3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Plain.
Context {RC : run_ceil}.
(* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable RZ : GPS.rz_t.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GPLAIN <= lo /\ hi <= g_img_hi GPLAIN /\ (forall plo phi, In (plo, phi) (g_priv GPLAIN) -> hi <= plo \/ phi <= lo).
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HIDc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0c + bcap <= GBUDGET.
Hypothesis ccap_ok : C0c + ccap <= GCOUNT.
#[local] Notation AINVc := (AINV_f SWIN GPLAIN AINVH PERMc SPTOPc HIDc M0c B0c C0c).

(* [comment removed for export] *)
Definition RSTK : Z := MSTK_MALLOC + 16.
Hypothesis OPN : GlzSpecsStr.GlzContracts.opnew_mspecR PSEGS AINVH fx_ok RZ GPLAIN RSTK GBUDGET GCOUNT 0x70334.
Hypothesis DEL : GlzSpecsStr.GlzContracts.free_mspecR PSEGS AINVH fx_ok RZ GPLAIN MSTK_MALLOC 0x55f34.

(* [comment removed for export] *)
Lemma priv_img : forall z, in_wins (g_priv GPLAIN) z -> g_img_lo GPLAIN <= z < g_img_hi GPLAIN.
Proof. intros z (lo & hi & Hin & Hz). destruct (GPLAIN_priv lo hi Hin) as [H1 H2]. cbn [g_img_lo g_ro_hi g_img_hi GPLAIN] in *. lia. Qed.
Lemma priv_below : forall z, in_wins (g_priv GPLAIN) z -> z < CEIL_run.
Proof. intros z Hz. pose proof (priv_img z Hz). pose proof plain_G_img_ceil. lia. Qed.
Lemma img_ok : 0 <= g_img_lo GPLAIN <= g_img_hi GPLAIN /\ g_img_hi GPLAIN <= CEIL_run.
Proof. pose proof plain_G_img_ceil. cbn [g_img_lo g_img_hi GPLAIN] in *. lia. Qed.

Lemma AINVH_app : forall Lc B C M M' mdl,
  AINVH Lc B C M mdl ->
  (forall a : word, M' a <> M a -> (in_blocks Lc (bv_unsigned a) \/ CEIL_run <= bv_unsigned a) /\ M' a <> None) ->
  AINVH Lc B C M' mdl.
Proof.
  intros Lc B C M M' mdl HA Hch. eapply AINVH_frame; [exact HA|]. intros a Ha. destruct (Hch a Ha) as [[X|X] D]; (split; [|exact D]); [left; exact X | right; left; exact X].
Qed.

Lemma opdel_at : GlzSpecsStr.GlzContracts.free_mspecR PSEGS AINVH fx_ok RZ GPLAIN RSTK 0x55f34.
Proof.
  unfold RSTK. apply (free_mspecR_mono PSEGS AINVH fx_ok RZ GPLAIN priv_below MSTK_MALLOC); [unfold MSTK_MALLOC; lia|]. exact DEL.
Qed.
Lemma RSTK_ok : 0 <= RSTK /\ RSTK + 80 <= MSTK.
Proof. unfold RSTK, MSTK_MALLOC, MSTK. lia. Qed.

(* [comment removed for export] *)
Lemma entry_lit : Z_to_bv 64 0x57b68 = (0x57b68%bv : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma plain_keepS : resize_keepS_spec PSEGS 0x57b68.
Proof.
  intros fx regs M obj sp ret w0 cw s n RD8 Hw0 Hs Hn Hobj Hsp Hapart STF STO Hret H1 H2 H10 H11 H12.
  unfold mkstF. rewrite entry_lit.
  exact (@resize_short_any fx (seg_rom PSEGS) regs M obj sp ret w0 cw s n RD8 Hw0 Hs Hn Hobj Hsp Hapart STF STO Hret H1 H2 H10 H11 H12).
Qed.
Lemma plain_keepL : resize_keepL_spec PSEGS 0x57b68.
Proof.
  intros fx regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd Hs Hn Hcap62 Hobj Hd Hsp Hapart Hdfr Hdobj STF STO STD Hret H1 H2 H10 H11 H12.
  unfold mkstF. rewrite entry_lit.
  exact (@resize_long_inplace_any fx (seg_rom PSEGS) regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd Hs Hn Hcap62 Hobj Hd Hsp Hapart Hdfr Hdobj
           STF STO STD Hret H1 H2 H10 H11 H12).
Qed.

(* [comment removed for export] *)
Lemma plain_growL_mspec : resize_growL_mspec PSEGS AINVH fx_ok RZ GPLAIN RSTK GBUDGET GCOUNT 0x57b68.
Proof.
  exact (resize_grow_long AINVH fx_ok GPLAIN RZ RZ_msteps AINVH_app priv_img img_ok RSTK GBUDGET GCOUNT (proj1 RSTK_ok) OPN opdel_at).
Qed.
Lemma plain_growS_mspec : resize_growS_mspec PSEGS AINVH fx_ok RZ GPLAIN RSTK GBUDGET GCOUNT 0x57b68.
Proof.
  exact (resize_grow_short AINVH fx_ok GPLAIN RZ RZ_msteps AINVH_app priv_img img_ok RSTK GBUDGET GCOUNT (proj1 RSTK_ok) OPN).
Qed.

(* [comment removed for export] *)
Theorem plain_resize_specs : resize_specs PSEGS SWIN PERMc SPTOPc AINVc fx_ok RZ GPLAIN bcap ccap 0x57b68.
Proof.
  constructor.
  - exact plain_keepS.
  - exact plain_keepL.
  - eapply (growS_nspec_of_mspec PSEGS SWIN GPLAIN fx_ok RZ AINVH);
      first [exact AINVH_zone | exact AINVH_disj | exact AINVH_mono | exact AINVH_frame | exact plain_G_ro_img | exact plain_G_img_ceil | exact GPLAIN_priv | exact SWIN_img
            | exact plain_SEGS_out | exact B0c_nonneg | exact C0c_nonneg | exact RSTK_ok | exact bcap_ok | exact ccap_ok | exact plain_growS_mspec].
  - eapply (growL_nspec_of_mspec PSEGS SWIN GPLAIN fx_ok RZ AINVH);
      first [exact AINVH_zone | exact AINVH_disj | exact AINVH_mono | exact AINVH_frame | exact plain_G_ro_img | exact plain_G_img_ceil | exact GPLAIN_priv | exact SWIN_img
            | exact plain_SEGS_out | exact B0c_nonneg | exact C0c_nonneg | exact RSTK_ok | exact bcap_ok | exact ccap_ok | exact plain_growL_mspec].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

Theorem plain_OBL_str_resize2 : OBL_str_resize2 PSEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc fx_ok UINV RZ GPLAIN bcap ccap.
Proof.
  unfold OBL_str_resize2.
  apply (node_str_resize2_sound PSEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINVc
           (AINV_f_frame SWIN GPLAIN AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil PERMc SPTOPc HIDc M0c B0c C0c)
           (AINV_f_mono SWIN GPLAIN AINVH AINVH_mono PERMc SPTOPc HIDc M0c B0c C0c)
           fx_ok UINV UINV_agree RZ RZ_msteps GPLAIN bcap ccap plain_SEGS_out plain_G_ro_img plain_G_img_ceil plain_G_img_hull plain_segs_wr_ok).
  exact plain_resize_specs.
Qed.

End Plain.
End GlzStrSpecsPlain.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 GlzOpNewPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon GlzStrSpecsPlain.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require MhFree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac lia ::= Zify.zify; xlia zchecker.

Section OpNew.
Context {RC : run_ceil}.
(* [comment removed for export] *)
Hypothesis HMW : forall fx : FPState, @MALLOC_KATW fx RC MSTK_M.
(* [comment removed for export] *)
Lemma AINV_stack : forall L B C (M M' : word -> option byte) mdl,
  AINV L B C M mdl -> (forall a : word, M' a <> M a -> GlzConst.RunCeil.CEIL <= bv_unsigned a /\ M' a <> None) -> AINV L B C M' mdl.
Proof.
  intros L B C M M' mdl HA H. apply (AINV_frame [] L B C M M' mdl); [intros lo hi a [] | exact HA |].
  intros a Hne. destruct (H a Hne) as [X D]. split; [right; left; exact X | exact D].
Qed.

Lemma same_csr : GlzSpecsStr.GlzContracts.callee_saved_regs = MhSpec3.callee_saved_regs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem plain_opnew_mspecR : forall bc cc,
  bc <= GBUDGET -> cc <= GCOUNT ->
  opnew_mspecR PSEGS AINV fx_ok (realizes PSEGS) GPLAIN (MSTK_MALLOC + 16) bc cc 0x70334.
Proof.
  intros bc cc Hbc Hcc.
  unfold opnew_mspecR. intros fx R M mdl Lc B C ret n sp T PRE HT HK.
  destruct PRE as (Hh & Hl & Hm & HFX & HA & Hra & Hret & Hev & Hn & Hnr & Hsp & Hal & Hceil & Htp & Hstk & HB & HC).
  assert (HPRE : malloc_pre (MSTK_M + 16) R M mdl B C ret n sp).
  { unfold malloc_pre. unfold MSTK_M. unfold MSTK_MALLOC in Hceil, Hstk.
    unfold NMAX in Hnr. unfold MH_NMAX. unfold mcost, GlzIface.MBLK, GBUDGET in HB, Hbc. unfold MH_GBUDGET, MhDefs.MBLK.
    unfold MCNT, GCOUNT, GlzIface.LMAX in HC, Hcc. unfold MhDefs.LMAX.
    cbn [g_tp GPLAIN] in Htp. unfold TPV.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
  unfold mkstF.
  apply (opnew_retry (HMW fx) AINV_stack R M mdl Lc B C ret n sp HA HPRE T HT).
  intros d Hok.
  destruct Hok as (R' & M' & mdl' & p & -> & RK & H10 & Hp16 & Hblk & Hdisj & Hdef & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
  apply (HK fx R' M' mdl' p).
  unfold alloc_post_ok.
  repeat match goal with |- _ /\ _ => split end; try assumption;
  lazymatch goal with
  | |- forall r, In r _ -> _ => rewrite same_csr; exact RK
  | |- GlzSpecsStr.GlzContracts.blk_ok _ _ _ =>
      unfold GlzSpecsStr.GlzContracts.blk_ok; cbn [g_img_lo g_img_hi GPLAIN]; unfold PTRLO; unfold MhAInv.blk_ok, HEAPLO in Hblk; lia
  | |- forall a : word, M' a <> M a -> _ =>
      intros a Ha; pose proof (CH a Ha) as X; unfold mh_changed in X; unfold alloc_changed;
      cbn [g_img_lo g_img_hi g_priv GPLAIN]; unfold MSTK_M in X; unfold MSTK_MALLOC;
      unfold MhAInv.in_blocks in X; unfold GPS.in_blocks, GPS.in_wins;
      unfold CTX_END, CTX, A_ERRNO, TPV in X;
      destruct X as [(X1 & X2 & X3)|[X|[X|X]]];
      [ left; split; [lia | split; [lia | exact X3]]
      | right; left; lia
      | right; right; exists 0xa6820, 0xa6bd0; split; [cbv; tauto | lia]
      | right; right; exists 0x8647c, 0xa6564; split; [cbv; tauto | lia] ]
  | |- forall a : word, _ -> RiscvSemantics.store_ok _ _ _ _ = true =>
      intros a Ha; apply ST; unfold MSTK_M; unfold MSTK_MALLOC in Ha; lia
  | |- AINV _ _ _ _ _ => unfold mcost, GlzIface.MBLK, MCNT; unfold MhDefs.MBLK in HA'; exact HA'
  | |- _ => idtac
  end.
Qed.
End OpNew.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Free.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_kc : forall T, kclosed PSEGS (fun c => RZ c T).
(* [comment removed for export] *)
Let HF : forall fx : FPState, @FREE_KAT fx RC MSTK_M := fun fx => @MhFree3.free_kat3 fx RC.

Lemma same_csr' : GlzSpecsStr.GlzContracts.callee_saved_regs = MhSpec3.callee_saved_regs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_mspecR_via : forall e : Z,
  (forall (fx : FPState) R M, msteps PSEGS (@mkst fx R (Z_to_bv 64 e) M (seg_rom PSEGS)) (@mkst fx R (Z_to_bv 64 0x61b20) M (seg_rom PSEGS))) ->
  free_mspecR PSEGS AINV fx_ok RZ GPLAIN MSTK_MALLOC e.
Proof.
  intros e STEPS. unfold free_mspecR.
  intros fx R M mdl Lc Lc' B C B' C' ret sp p T Hh Hl Hm HFX HA Hra Hret Hev H10 Hcase Hsp Hal Hceil Htp Hstk HK.
  unfold mkstF. apply (K_msteps PSEGS (fun c => RZ c T) _ _ mdl (RZ_kc T) Hh Hl (STEPS fx R M)).
  assert (HPRE : free_pre MSTK_M R M mdl Lc Lc' B C B' C' ret sp p).
  { unfold free_pre. unfold MSTK_M. unfold MSTK_MALLOC in Hceil, Hstk. unfold mcost, GlzIface.MBLK, MCNT in Hcase. unfold MhDefs.MBLK.
    cbn [g_tp GPLAIN] in Htp. unfold TPV.
    repeat match goal with |- _ /\ _ => split end; try assumption; lia. }
  pose proof (HF fx R M mdl Lc Lc' B C B' C' ret sp p HA HPRE) as KAT.
  unfold free_cfg, A_FREE in KAT. apply (KAT (fun c => RZ c T) (RZ_kc T)).
  intros c' (R' & M' & mdl' & -> & RK & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
  apply (HK fx R' M' mdl' HFX).
  - rewrite same_csr'. exact RK.
  - intros a Ha. pose proof (CH a Ha) as X. unfold mh_changed in X. unfold alloc_changed.
    cbn [g_img_lo g_img_hi g_priv GPLAIN]. unfold MSTK_M in X. unfold MSTK_MALLOC.
    unfold MhAInv.in_blocks in X. unfold GPS.in_blocks, GPS.in_wins.
    unfold CTX_END, CTX, A_ERRNO, TPV in X.
    destruct X as [(X1 & X2 & X3)|[X|[X|X]]];
      [ left; split; [lia | split; [lia | exact X3]]
      | right; left; lia
      | right; right; exists 0xa6820, 0xa6bd0; split; [cbv; tauto | lia]
      | right; right; exists 0x8647c, 0xa6564; split; [cbv; tauto | lia] ].
  - intros a Ha. apply ST. unfold MSTK_M. unfold MSTK_MALLOC in Ha. lia.
  - exact HA'.
  - exact Hh'. - exact Hl'. - exact Hm'. - exact Hfs'. - exact Hfd'.
Qed.

Theorem plain_free_mspecR : free_mspecR PSEGS AINV fx_ok RZ GPLAIN MSTK_MALLOC 0x61b20.
Proof. apply free_mspecR_via. intros fx R M. apply mst_refl. Qed.

Lemma zbv_w : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.

Theorem plain_opdel_mspecR : free_mspecR PSEGS AINV fx_ok RZ GPLAIN MSTK_MALLOC 0x55f34.
Proof.
  apply free_mspecR_via. intros fx R M.
  rewrite (zbv_w 0x55f34 (0x55f34%bv : word) eq_refl), (zbv_w 0x61b20 (0x61b20%bv : word) eq_refl). apply opdel_jj.
Qed.
Theorem plain_opdel_sized_mspecR : free_mspecR PSEGS AINV fx_ok RZ GPLAIN MSTK_MALLOC 0x55f30.
Proof.
  apply free_mspecR_via. intros fx R M.
  rewrite (zbv_w 0x55f30 (0x55f30%bv : word) eq_refl), (zbv_w 0x61b20 (0x61b20%bv : word) eq_refl). apply opdel_sized_j.
Qed.
End Free.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GC.
Context {RC : run_ceil}.
Hypothesis HMW : forall fx : FPState, @MALLOC_KATW fx RC MSTK_M.
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : swin_ok SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GPLAIN <= lo /\ hi <= g_img_hi GPLAIN /\ (forall plo phi, In (plo, phi) (g_priv GPLAIN) -> hi <= plo \/ phi <= lo).
#[local] Notation RZ := (realizes PSEGS).

(* [comment removed for export] *)
Lemma RZ_step_rr : GPS.RZ_STEP PSEGS RZ.
Proof. intros ms model ms' T. apply rz_step. Qed.
Lemma RZ_msteps_rr : GPS.RZ_MSTEPS PSEGS RZ.
Proof. intros ms ms' model T. apply rz_msteps. Qed.
Lemma RZ_exit_rr : GPS.RZ_EXIT PSEGS RZ.
Proof. intros ms model x8. apply rz_exit. Qed.
Lemma RZ_conseq_rr : GPS.RZ_CONSEQ RZ.
Proof. intros c T T'. apply rz_conseq. Qed.
Lemma rr_kc : forall T, kclosed PSEGS (fun c => realizes PSEGS c T).
Proof. exact (kclosed_realizes PSEGS). Qed.

(* [comment removed for export] *)
Lemma P_frame : forall L B C M M' mdl,
  AINV L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINV L B C M' mdl.
Proof. intros L B C M M' mdl HA H. exact (AINV_frame SWIN L B C M M' mdl SWIN_ok HA H). Qed.
Lemma P_zone : forall L B C M mdl b m, AINV L B C M mdl -> In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GPLAIN b m.
Proof.
  intros L B C M mdl b m HA Hin. destruct (AINV_zone L B C M mdl b m HA Hin) as (Z1 & Z2 & Z3).
  unfold GlzSpecsStr.GlzContracts.blk_ok. cbn [g_img_lo g_img_hi GPLAIN]. unfold HEAPLO in Z1. unfold PTRLO. lia.
Qed.
Lemma P_disj : forall L B C M mdl L1 L2 b m b' m',
  AINV L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof. exact AINV_disj. Qed.
Lemma P_mono : forall L B C B' C' M mdl, AINV L B C M mdl -> B <= B' -> C <= C' -> AINV L B' C' M mdl.
Proof. exact AINV_mono. Qed.

Lemma MM_ok : 0 <= MSTK_MALLOC <= GlzIface.MSTK. Proof. unfold MSTK_MALLOC, GlzIface.MSTK. lia. Qed.   (* [comment removed for export] *)
Lemma RSTK16_ok : 0 <= MSTK_MALLOC + 16 <= GlzIface.MSTK. Proof. unfold MSTK_MALLOC, GlzIface.MSTK. lia. Qed.

(* [comment removed for export] *)
Theorem GC_ALL : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  itab_sound PSEGS IT ->
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f SWIN GPLAIN AINV PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Proof.
  intros IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV IT_ok HB0 HC0 HBc HCc HUa.
  pose proof (AINV_f_frame SWIN GPLAIN AINV P_frame P_zone P_disj plain_G_ro_img plain_G_img_ceil PERMf TOPf HID M0 B0 C0) as AFR.
  pose proof (fun entry FS => free_nspec_of_mspec PSEGS SWIN GPLAIN fx_ok RZ AINV P_mono P_zone plain_G_ro_img plain_G_img_ceil GPLAIN_priv SWIN_img plain_SEGS_out
                                PERMf TOPf HID M0 B0 C0 HB0 HC0 MSTK_MALLOC MM_ok entry FS) as FNS.
  pose proof (opnew_nspec_of_mspec PSEGS SWIN GPLAIN fx_ok RZ AINV P_zone P_disj plain_G_ro_img plain_G_img_ceil GPLAIN_priv SWIN_img plain_SEGS_out
                PERMf TOPf HID M0 B0 C0 (MSTK_MALLOC + 16) RSTK16_ok bc cc HBc HCc 0x70334
                (plain_opnew_mspecR HMW GBUDGET GCOUNT ltac:(lia) ltac:(lia))) as ONS.
  constructor.
  - exact (node_imgload_sound PSEGS IT IT_ok NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_step_rr GPLAIN plain_rom_ok ltac:(cbn; lia)).
  - apply (node_opnew_sound PSEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GPLAIN bc cc); [cbn; lia | cbn; lia | exact ONS].
  - apply (node_free_sound PSEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GPLAIN); exact (FNS 0x61b20 (plain_free_mspecR RZ rr_kc)).
  - exact (node_blkfact_sound PSEGS NXF PERMf TOPf FS0 FDS0 _ fx_ok UINV RZ GPLAIN plain_G_img_hull ltac:(cbn; lia)
             (AINV_f_zone SWIN GPLAIN AINV P_zone PERMf TOPf HID M0 B0 C0)
             (AINV_f_disj SWIN GPLAIN AINV P_disj PERMf TOPf HID M0 B0 C0)
             (AINV_f_perm_apart SWIN GPLAIN AINV P_zone P_disj plain_G_ro_img SWIN_img PERMf TOPf HID M0 B0 C0)
             (AINV_f_top SWIN GPLAIN AINV PERMf TOPf HID M0 B0 C0)).
  - apply (node_opdel_sound PSEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GPLAIN). exact (FNS 0x55f34 (plain_opdel_mspecR RZ rr_kc)).
  - apply (node_opdel_sized_sound PSEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GPLAIN). exact (FNS 0x55f30 (plain_opdel_sized_mspecR RZ rr_kc)).
  - exact (plain_OBL_memcpy APLAIN NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GPLAIN eq_refl).
  - exact (plain_OBL_memset APLAIN NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GPLAIN eq_refl).
  - exact (plain_OBL_memmove APLAIN NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GPLAIN eq_refl plain_in_hull plain_hull_ok).
  - exact (plain_OBL_strlen NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GPLAIN eq_refl (conj eq_refl eq_refl) eq_refl).
Qed.

(* [comment removed for export] *)
Theorem OBL2_ALL : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f SWIN GPLAIN AINV PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Proof.
  intros NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  exact (plain_OBL_str_resize2 SWIN RZ RZ_msteps_rr AINV P_frame P_mono P_zone P_disj SWIN_img PERMf TOPf HID M0 B0 C0 HB0 HC0 bc cc HBc HCc
           (plain_opnew_mspecR HMW GBUDGET GCOUNT (Z.le_refl _) (Z.le_refl _)) (plain_opdel_mspecR RZ rr_kc) NXF FS0 FDS0 UINV HUa).
Qed.
End GC.
