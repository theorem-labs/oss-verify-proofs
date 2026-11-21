(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from DrvS0Dir.v's modules RefStrnlen (unchanged, so that this file need not Require DrvS0Dir) and DrvNodes2Sound, over BudgetWit.Rzb's ShapeRelB.shape_rel, BudgetWit.StdioB and BudgetWit.NodesB; the read node adds the no-allocation-call check (system call 63). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel reader from cs_ok's co_rdr; RomBase.sys_rob at the read node). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefStrnlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section SNL.
  Variable mem : word -> option byte.
  Variables s sp : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.
  Hypothesis HsK : (0 < bv_unsigned s + K)%Z.
  Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true.
  Hypothesis Hspr : (0x13060 <= bv_unsigned sp - 32)%Z.
  Hypothesis Hdisj : (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32
                      \/ bv_unsigned sp <= bv_unsigned s)%Z.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation W8 v := (word_to_le_bytes 8 v).

  (* [comment removed for export] *)
  Definition mem1 (ra s0 s1 : word) : word -> option byte :=
    wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
           (Z_to_bv 64 (usp - 24)) (W8 s1).

  Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof using. intros v. apply length_N_to_le_bytes. Qed.

  Lemma mem1_out : forall ra s0 s1 (a : word),
    (bv_unsigned a < usp - 24 \/ usp <= bv_unsigned a)%Z -> mem1 ra s0 s1 a = mem a.
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1 a Ha. pose proof (u64_range sp). unfold mem1.
    rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma HOK1 : forall ra s0 s1, mchrH (mem1 ra s0 s1) s buf K n.
  Proof using Hdisj Hspr HsK HOK.
    intros ra s0 s1. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. split; try assumption.
    - rewrite <- Hbuf. apply rdn_ext; [lia|]. intros x Hx. apply mem1_out. lia.
    - intros i Hi. rewrite mem1_out; [apply Hro; exact Hi | u_norm; lia].
  Qed.

  Lemma frame1 : forall ra s0 s1, frame_mod mem (mem1 ra s0 s1) [(Z_to_bv 64 (usp - 32), 32%Z)].
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1. pose proof (u64_range sp). split.
    - intros a [Ha _]. unfold in_rng in Ha. revert Ha. u_norm. intros Ha. apply mem1_out. lia.
    - unfold mem1. eapply mem_grows_trans; [| apply wbytes_grows].
      eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_ra : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 ra).
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s0 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s0).
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s1 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s1).
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1. apply rdn_wbytes_hit8. u_norm. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac okstk :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
      [u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].

  Ltac kept_cs := cbv [callee_saved In]; tauto.

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

  Lemma strnlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x6f380 : word) mem rom)
                   (mkst regs' ret (mem1 ret (getr regs 8) (getr regs 9)) rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 K.
  Proof using Hdisj Hspr Hstk HsK HOK buf.
    intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
    pose proof (KL _ _ _ _ _ HOK) as HKL.
    destruct HOK as [Hbuf Hwin Hnw HK0 _ _ HKn Hn64 Hro].
    set (s0 := getr regs 8). set (s1 := getr regs 9).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x6eb44 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 1 = (0x6f3a4 : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
                       /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = s
                       /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 n
                       /\ (forall x : reg, In x callee_saved -> x <> 1 -> x <> 2 -> x <> 8 -> x <> 9 -> getr r x = getr regs x))).
    { eexists. split.
      - stepiv F_6f32c D_6f32c (Z_to_bv 64 (usp - 32))
          ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
        msd F_6f330 D_6f330 (Z_to_bv 64 (usp - 8)).                 (* [comment removed for export] *)
        msd F_6f334 D_6f334 (Z_to_bv 64 (usp - 16)).                (* [comment removed for export] *)
        msd F_6f338 D_6f338 (Z_to_bv 64 (usp - 24)).                (* [comment removed for export] *)
        stepn F_6f33c D_6f33c.                                       (* [comment removed for export] *)
        stepn F_6f340 D_6f340.                                       (* [comment removed for export] *)
        stepn F_6f344 D_6f344.                                       (* [comment removed for export] *)
        stepn F_6f348 D_6f348.                                       (* [comment removed for export] *)
        stepn F_6f34c D_6f34c.                                       (* [comment removed for export] *)
        rwH. fold s0 s1. unfold mem1. pu_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; try bveq.
        intros x Hx N1 N2 N8 N9. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [first [ exfalso; match goal with N : ?a <> ?a |- _ => apply N; reflexivity end
                 | gres; reflexivity ] |]).
        destruct Hx. }
    cbv beta. intros r1 (R1 & R2 & R8 & R9 & R10 & R11 & R12 & RK).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x6f3a4 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 10 = Z_to_bv 64 (bv_unsigned s + K) /\ keeps_cs r1 r)).
    { destruct (ref_memchr0 (mem1 ret s0 s1) s buf K n rom r1 (0x6f3a4 : word) (HOK1 ret s0 s1)
                  ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r & RUN & KC & A10).
      exists r. split; [exact RUN | split; [exact A10 | exact KC]]. }
    cbv beta. intros r2 (A10 & KC).
    assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (KC 2) by kept_cs; exact R2).
    assert (S9 : getr r2 9 = s) by (rewrite (KC 9) by kept_cs; exact R9).
    (* [comment removed for export] *)
    eexists. split.
    - stepb_ft F_6f350 D_6f350 ltac:(rwH; apply c_eq_neq; unorm; lia).  (* [comment removed for export] *)
      stepiv F_6f354 D_6f354 (Z_to_bv 64 K)
        ltac:(gres; rwH; unfold v_sub; unorm; f_equal; lia).          (* [comment removed for export] *)
      stepn F_6f358 D_6f358.                                         (* [comment removed for export] *)
      mld8 F_6f35c D_6f35c ret (rd_ra ret s0 s1).                    (* [comment removed for export] *)
      mld8 F_6f360 D_6f360 s0 (rd_s0 ret s0 s1).                     (* [comment removed for export] *)
      mld8 F_6f364 D_6f364 s1 (rd_s1 ret s0 s1).                     (* [comment removed for export] *)
      stepiv F_6f368 D_6f368 sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                     (* [comment removed for export] *)
      stepret F_6f36c D_6f36c ret ltac:(reflexivity).
      pu_refl.
    - split.
      + intros x Hx. pose proof Hx as Hx'. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ gres; subst s0 s1; first [ symmetry; assumption | reflexivity
                  | rewrite (KC _ Hx'); apply (RK _ Hx'); intros E; discriminate E ] |]).
        destruct Hx.
      + gres. reflexivity.
  Qed.
End SNL.

Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x13060 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x6f380 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof using.
  intros mem s sp buf K n rom regs ret HOK HsK Hstk Hspr Hdisj Hret H1 H2 H10 H11.
  destruct (strnlen_run mem s sp buf K n rom HOK HsK Hstk Hspr Hdisj regs ret Hret H1 H2 H10 H11)
    as (r & RUN & KC & A10).
  exists r, (mem1 mem sp ret (getr regs 8) (getr regs 9)).
  split; [exact RUN | split; [exact KC | split; [exact A10 | apply frame1; exact Hspr]]].
Qed.
End FPGen1.
End RefStrnlen.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup.
Require Stdlib.NArith.NArith LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.WritevB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.NodesB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DrvNodes2SoundB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesBlob OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.RefStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStdioDefs.RefExitBase OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefStdioWriteB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefExitB OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes2 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemchr RefStrnlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.RzbAlg OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.ShapeRelB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.WritevB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefStdioWriteB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefExitB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.NodesB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS (only parsing).

(* [comment removed for export] *)
Lemma file_syms_sound : forall E M k f fd buf bsz wb wp,
  know_ok RSEGS E M k -> DN2.file_syms RSEGS k f = Some (fd, buf, bsz, wb, wp) -> 0 <= f -> f + 232 <= 2 ^ 64 ->
  sw_file M f (uE E wb) (uE E wp) fd (edenot E buf) (edenot E bsz) /\ 0 <= fd < two64.
Proof.
  intros E M k f fd buf bsz wb wp HK H Hf0 Hf8. unfold DN2.file_syms in H.
  destruct (kreadZ RSEGS k (ELit 0) (f + 120) 4) as [x1|] eqn:H1; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 88)) as [x2|] eqn:H2; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 96)) as [x3|] eqn:H3; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 56)) as [x4|] eqn:H4; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 40)) as [x5|] eqn:H5; [|discriminate].
  injection H as <- <- <- <- <-.
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H1 ltac:(lia) ltac:(lia) ltac:(lia)) as [R1 B1].
  pose proof (kread8e_lit0_sound E M k _ _ HK H2 ltac:(lia) ltac:(lia)) as R2.
  pose proof (kread8e_lit0_sound E M k _ _ HK H3 ltac:(lia) ltac:(lia)) as R3.
  pose proof (kread8e_lit0_sound E M k _ _ HK H4 ltac:(lia) ltac:(lia)) as R4.
  pose proof (kread8e_lit0_sound E M k _ _ HK H5 ltac:(lia) ltac:(lia)) as R5.
  split; [| lia]. constructor; unfold uE; rewrite ?Z_to_bv_bv_unsigned; assumption.
Qed.

(* [comment removed for export] *)
Lemma know_after_sw2 : forall E M M' k spb spk (su f : Z) (buf bsz : expr),
  know_ok RSEGS E M k ->
  bv_unsigned (edenot E spb) + spk = su -> 112 <= su -> 0 <= f -> f + 232 <= 2 ^ 64 ->
  sw_post M su f (edenot E buf) (edenot E bsz) M' ->
  know_ok RSEGS E M'
    ([KWord (SA (ELit 0) (f + 32)) 8 (eadd buf bsz); KWord (SA (ELit 0) (f + 40)) 8 buf; KWord (SA (ELit 0) (f + 56)) 8 buf]
     ++ kn_havoc (kn_havoc k spb (spk - DN.FR_SW) (ELit DN.FR_SW)) (ELit 0) (f + 32) (ELit 32)).
Proof.
  intros E M M' k spb spk su f buf bsz HK Hsu Hsu112 Hf0 Hf8 [AG GR WE WP WB].
  apply Forall_app. split.
  - repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok]; (split; [lia|]); (split; [unfold flat; rewrite estart_lit0; lia|]);
      rewrite GCL.adenot_SA, estart_lit0.
    + rewrite WE. do 2 f_equal. unfold eadd. rewrite mkAlu_denot. reflexivity.
    + exact WP.
    + exact WB.
  - set (M1 := fun x : word => if (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool then M x else M' x).
    apply (know_ok_havoc RSEGS E M1 M').
    + apply (know_ok_havoc RSEGS E M M1); [exact HK| |].
      * intros x Hx. rewrite estart_SA in Hx. unfold elenZ, DN.FR_SW in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia.
        unfold M1. destruct (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool eqn:Hc; [reflexivity|].
        apply Bool.andb_false_iff in Hc. apply AG; [lia| |]; destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc| apply Z.ltb_ge in Hc|apply Z.leb_gt in Hc| apply Z.ltb_ge in Hc]; lia.
      * intros x Hmx HM1. unfold M1 in HM1.
        destruct ((f + 32 <=? bv_unsigned x) && (bv_unsigned x <? f + 64))%bool; [exact (Hmx HM1) | exact (GR x Hmx HM1)].
    + intros x Hx. rewrite estart_lit0 in Hx. unfold elenZ in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia.
      unfold M1. destruct (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool eqn:Hc; [|reflexivity].
      apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
    + intros x HM1 Hm'. unfold M1 in HM1.
      destruct ((f + 32 <=? bv_unsigned x) && (bv_unsigned x <? f + 64))%bool; [exact (GR x HM1 Hm') | exact (HM1 Hm')].
Qed.

Section Sound.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable NZB : list nat.
Hypothesis UINV_nz : forall E j, UINV E -> In j NZB -> ~ In (Z_to_bv 8 0) (eb E j).
Hypothesis SR_det : forall c T T', sr_rel RSEGS SR c T -> realizes RSEGS c T' -> t_eq T T'.
Hypothesis SWINc : forall a, (DN.FILE1 <= a < DN.FILE1 + 232 \/ DN.FILE2 <= a < DN.FILE2 + 232) -> in_wins SWIN a.
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation cs_ok := (GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation cfg := (cfgF RSEGS).

Theorem node_stdio_write2_sound : forall cs fd ps cs' E fx R M model T,
  cs_ok E cs fx R M model -> DN2.node_stdio_write2 RSEGS nx0 cs = Some (fd, ps, cs') -> T [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Proof.
  intros cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN2.node_stdio_write2 in Hn.
  destruct (Z.eqb (pc cs) DN.P_STDIO_WRITE) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 10) as [f|] eqn:R10; [|discriminate].
  destruct (ret_lit cs) as [ret|] eqn:Rret; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN2.file_syms RSEGS (kn cs) f) as [[[[[fdv buf] bsz] wb] wp]|] eqn:Hfl; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hfd; [|discriminate] end. cbn [negb] in Hn.
  destruct (split_lit wb) as [wbb wbk] eqn:Hsqw.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsqs.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  cbv zeta in Hn.
  destruct (GNB.kgather RSEGS (kn cs) wb wp) as [pend|] eqn:Hpend; [|discriminate].
  destruct (GNB.kgather RSEGS (kn cs) (reg cs 11) (eadd (reg cs 11) (reg cs 12))) as [ext|] eqn:Hext; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg3; [|discriminate] end. cbn [negb] in Hn.
  match type of Hn with context [after_call ?a ?b ?c ?d ?e] => destruct (after_call a b c d e) as [cs1|] eqn:Hac; [|discriminate] end.
  injection Hn as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hg1 as [Hg1 Hlen]. apply andb_prop in Hg1 as [Hg1 Hfresh]. apply andb_prop in Hg1 as [Hg1 Hssp].
  apply andb_prop in Hg1 as [Hg1 Hfr]. apply andb_prop in Hg1 as [Hf12 Hspok]. apply Nat.eqb_eq in Hlen.
  apply andb_prop in Hg3 as [Hg3 Hdisj]. apply andb_prop in Hg3 as [Hg3 Hbflat]. apply andb_prop in Hg3 as [Hg3 Hwdisj].
  apply andb_prop in Hg3 as [Hg3 Hwflat]. apply andb_prop in Hg3 as [Hg3 Ltot]. apply andb_prop in Hg3 as [Lwp Lsl].
  assert (Hfdv : (fdv = 1 \/ fdv = 2) /\ (f = DN.FILE1 \/ f = DN.FILE2)).
  { apply orb_prop in Hfd as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_eq in H2; subst; tauto. }
  destruct Hfdv as [Hfdv Hf]. clear Hfd Hf12.
  assert (Hfb : 0x75000 <= f /\ f + 232 <= 0xa6790) by (unfold DN.FILE1, DN.FILE2 in Hf; lia).
  (* [comment removed for export] *)
  pose proof (co_know HC) as HK.
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 f HC ltac:(lia) R10) as [G10 _].
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)) as G11.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 12 HC ltac:(lia)) as G12.
  change (Z.of_nat 10) with 10 in G10. change (Z.of_nat 11) with 11 in G11. change (Z.of_nat 12) with 12 in G12.
  destruct (GCL.ret_lit_sound E cs R ret (co_regs HC) Rret) as (G1 & Hretok & Hretr & _).
  destruct (sp_ok_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN.FR_SW HC Hspok ltac:(unfold DN.FR_SW; lia)) as (Hsp & Hst & G2 & Hsu).
  specialize (Hsu spb spk Hsq).
  set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (file_syms_sound E M (kn cs) f fdv buf bsz wb wp HK Hfl ltac:(lia) ltac:(lia)) as [SWF Bfd].
  destruct (ssp_ok_sound E M (kn cs) HK Hssp) as [can Hcan].
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lwp) as Bwp. rewrite !GNB.xt_den1 in Bwp.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lsl) as Bsl. rewrite GNB.xt_den1, GNB.xt_den2 in Bsl.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Ltot) as Btot. rewrite GNB.xt_den1, GNB.xt_den2 in Btot.
  change (uE E (ELit 0)) with 0 in Bwp, Bsl.
  destruct (bflat_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) HK Hbflat) as (Fs0 & Fsl & Fs64).
  pose proof (u_of_split E (reg cs 11) sb sk Hsqs ltac:(lia)) as Us. rewrite estart_SA in Us.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) spb (spk - DN.FR_SW) (ELit DN.FR_SW) HK Hdisj) as DISJ.
  rewrite !estart_SA in DISJ. unfold elenZ, DN.FR_SW in DISJ. cbn [edenot] in DISJ. rewrite u64_lit in DISJ by lia.
  destruct (bflat_x_sound RSEGS E M (kn cs) wbb wbk (esub wp wb) HK Hwflat) as (Fw0 & Fwl & Fw64).
  pose proof (u_of_split E wb wbb wbk Hsqw ltac:(lia)) as Uwb. rewrite estart_SA in Uwb.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) wbb wbk (esub wp wb) spb (spk - DN.FR_SW) (ELit DN.FR_SW) HK Hwdisj) as WDISJ.
  rewrite !estart_SA in WDISJ. unfold elenZ, DN.FR_SW in WDISJ. cbn [edenot] in WDISJ. rewrite u64_lit in WDISJ by lia.
  (* [comment removed for export] *)
  destruct (GNB.kgather_sound RSEGS E M (kn cs) wb wp pend HK Hpend) as (Kp1 & Kp2 & Kp3 & _).
  destruct (GNB.kgather_sound RSEGS E M (kn cs) (reg cs 11) (eadd (reg cs 11) (reg cs 12)) ext HK Hext) as (Ke1 & Ke2 & Ke3 & _).
  set (pbs := flat_map (piece_den E) pend) in *. set (extra := flat_map (piece_den E) ext) in *.
  pose proof (u64_range (edenot E (reg cs 11))) as U11. pose proof (u64_range (edenot E (reg cs 12))) as U12.
  pose proof (u64_range (edenot E wp)) as Uwp. pose proof (u64_range (edenot E wb)) as Uwb'.
  assert (Ule : uE E (eadd (reg cs 11) (reg cs 12)) = uE E (reg cs 11) + uE E (reg cs 12)).
  { unfold eadd, uE in *. rewrite mkAlu_denot. rewrite u_add64. apply Z.mod_small. unfold DN.SPHI in Bsl. lia. }
  rewrite Ule in Ke1.
  assert (Usub : uE E (esub wp wb) = uE E wp - uE E wb).
  { unfold esub, uE in *. rewrite mkAlu_denot. rewrite u_sub64. apply Z.mod_small. lia. }
  unfold uE in Usub. rewrite Usub in Fwl, WDISJ.
  (* [comment removed for export] *)
  assert (HW : Wp E fdv (pend ++ ext) = map (WriteEv (Z_to_bv 64 fdv)) (pbs ++ extra)).
  { unfold Wp. f_equal. rewrite flat_map_app. reflexivity. }
  rewrite HW. unfold cfgF, mkstF. rewrite Hpc.
  replace (Z_to_bv 64 DN.P_STDIO_WRITE) with (0x649a0%bv : word) by (apply bv_eq; reflexivity).
  unfold uE in *.
  apply (ref_stdio_write_R (fx:=fx) SR R M model su f (bv_unsigned (edenot E wb)) (bv_unsigned (edenot E wp)) fdv (edenot E (reg cs 11)) (edenot E (reg cs 12))
           (edenot E buf) (edenot E bsz) can (Z_to_bv 64 ret) pbs extra T).
  all: try assumption.
  all: try (subst su; rewrite Z_to_bv_bv_unsigned; reflexivity).
  all: try (rewrite (co_fds HC); destruct Hfdv as [-> | ->]; [exact FDS1 | exact FDS2]).
  all: try exact (co_rdr HC).
  all: try exact (co_halt HC). all: try exact (co_lazy HC).
  all: try (rewrite Z_to_bv_bv_unsigned; exact Kp3).
  all: try (unfold DN.SPLO, DN.SPHI, DN.FR_SW in *; lia).
  - (* [comment removed for export] *)
    intros regs' mem' Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    unfold after_call in Hac.
    match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hcc; [|discriminate] end.
    apply andb_prop in Hcc as [Hcc Hrvv]. apply andb_prop in Hcc as [_ Hkv]. injection Hac as Ecs1.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := GCL.ext_call E (nxt cs) regs').
    pose proof (GCL.ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
    specialize (Hk E' fx regs' mem' model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
    rewrite <- Ecs1 in Hk. unfold cfgF, mkstF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
    pose proof (GPS.cs_ok_agree RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
    assert (KEPT : GCL.kept_ok R regs').
    { apply kept_ok_intro. intros r Hr. cbn [In] in Hr.
      repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] end; [| | | | | | | | | | | | | | | destruct Hr]; try assumption.
      rewrite Q2. subst su. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC1 | | reflexivity | | exact (co_fx HC) |].
    + cbn [mk_ss s_regs]. apply (GCL.regs_after_call E _ R regs' (nxt cs) (Some (reg cs 12)) (co_regs HC) Fsr KEPT).
      split; [exact Hrvv | replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact Q10].
    + cbn [mk_ss s_know]. eapply know_ok_agree'; [exact Hag | exact Hkv |].
      apply (know_after_sw2 E M mem' (kn cs) spb spk su f buf bsz HK); try assumption; try lia.
      unfold DN.SPLO, DN.FR_SW in Hsp. lia.
    + intros a Ha. cbn [a_vis]. rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
      destruct POST as [AG GR _ _ _]. pose proof (u64_range a) as Hau.
      split.
      2:{ intros Hn0. apply Ha. rewrite Hn0. destruct (M a) eqn:Hma; [|reflexivity]. exfalso. exact (GR a ltac:(congruence) Hn0). }
      destruct (Z_lt_le_dec (bv_unsigned a) (su - 112)) as [Hlow|Hhigh]; [|destruct (Z_lt_le_dec (bv_unsigned a) su) as [Hin|Habove]].
      * (* [comment removed for export] *) right. right. right. apply SWINc.
        assert (~ (~ f + 32 <= bv_unsigned a < f + 48 /\ ~ f + 56 <= bv_unsigned a < f + 64)) as Hx by (intros [X1 X2]; apply Ha; apply AG; lia).
        unfold DN.FILE1, DN.FILE2 in *. lia.
      * (* [comment removed for export] *) right. right. left. rewrite <- (co_top HC).
        unfold DN.frame_ok in Hfr. rewrite Hsq in Hfr.
        assert (Hrng : estart E (SA spb (spk - DN.FR_SW)) <= bv_unsigned a < estart E (SA spb (spk - DN.FR_SW)) + elenZ E (ELit DN.FR_SW)).
        { rewrite estart_SA. unfold elenZ, DN.FR_SW in *. cbn [edenot]. rewrite u64_lit by lia. lia. }
        exact (proj1 (GPS.in_floor_sound RSEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - DN.FR_SW) (ELit DN.FR_SW) a (co_know HC) Hfr (co_floor HC) Hrng)).
      * exfalso. unfold DN.SPLO, DN.FR_SW, DN.FILE1, DN.FILE2 in *. apply Ha. apply AG; lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_cons_inv : forall M (a : word) n b bs, rdn RSEGS M a (S n) = Some (b :: bs) ->
  GxSymExec3Sound.AX2S.rd1 RSEGS M a = Some b /\ rdn RSEGS M (a + 1)%bv n = Some bs.
Proof.
  intros M a n b bs H. cbn [rdn] in H. unfold GxSymExec3Sound.AX2S.rd1.
  destruct (match M a with Some b0 => Some b0 | None => seg_rom RSEGS a end) as [b0|]; [|discriminate].
  destruct (rdn RSEGS M (a + 1)%bv n) as [r|]; [|discriminate]. injection H as <- <-. split; reflexivity.
Qed.
Lemma rdn_nth1 : forall n M (a : word) bs i, rdn RSEGS M a n = Some bs -> (i < n)%nat ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) 1%nat = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  induction n as [|n IH]; intros M a bs i H Hi Hnw; [lia|].
  destruct bs as [|b bs']; [pose proof (rdn_length _ _ _ _ _ H) as L; cbn in L; lia|].
  destruct (rdn_cons_inv M a n b bs' H) as [H1 H2].
  destruct i as [|i].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. unfold GxSymExec3Sound.AX2S.rd1 in H1. rewrite H1. reflexivity.
  - cbn [nth]. pose proof (u64_range a) as Ha.
    assert (U1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S i)) with (bv_unsigned (a + 1)%bv + Z.of_nat i) by lia.
    apply (IH M (a + 1)%bv bs' i H2 ltac:(lia)). lia.
Qed.

Theorem node_strnlen_sound :
  GPS.node1_stmtN RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ GPS.always (DN2.node_strnlen nx0 NZB).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk. unfold DN2.node_strnlen in Hn.
  destruct (Z.eqb (pc cs) DN2.P_STRNLEN) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 11) as [n|] eqn:R11; [|discriminate].
  destruct (ret_lit cs) as [ret|] eqn:Rret; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate] end. cbn [negb] in Hn.
  destruct (split_lit (reg cs 10)) as [sb sk] eqn:Hsqs.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  destruct (find _ (kn cs)) as [K|] eqn:HF; [|discriminate].
  destruct K as [| | ba L jb| | | | | | |]; try discriminate.
  cbv zeta in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg2; [|discriminate] end. cbn [negb] in Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hg1 as [Hg1 Hn64]. apply andb_prop in Hg1 as [Hg1 Hn0]. apply andb_prop in Hg1 as [Hg1 Hro].
  apply andb_prop in Hg1 as [Hg1 Hlen]. apply andb_prop in Hg1 as [Hg1 Hfresh]. apply andb_prop in Hg1 as [Hspok Hfr].
  apply Nat.eqb_eq in Hlen. apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn64.
  apply andb_prop in Hg2 as [Hg2 Ls1]. apply andb_prop in Hg2 as [Hg2 Lhi]. apply andb_prop in Hg2 as [Hg2 Hdisj].
  apply andb_prop in Hg2 as [Hg2 Hbflat]. apply andb_prop in Hg2 as [Hg2 HLn]. apply andb_prop in Hg2 as [Hnul Hunk].
  (* [comment removed for export] *)
  apply find_some in HF as [HinB HB]. destruct ba as [bb bo]. apply andb_prop in HB as [HB Hj]. apply andb_prop in HB as [Hbb Hbo].
  apply expr_eqb_eq in Hbb. apply Z.eqb_eq in Hbo. subst bb bo. apply existsb_exists in Hj as (j0 & Hj0 & Hjj). apply Nat.eqb_eq in Hjj. subst j0.
  pose proof (co_know HC) as HK.
  pose proof (proj1 (Forall_forall _ _) HK _ HinB) as KB. cbn [kentry_ok] in KB. destruct KB as (FB & LEN & BY). unfold flat in FB. rewrite !estart_SA in FB, BY.
  (* [comment removed for export] *)
  apply existsb_exists in Hnul as (K' & HK' & HKK). apply kentry_eqb_eq in HKK. subst K'.
  pose proof (proj1 (Forall_forall _ _) HK _ HK') as KW. cbn [kentry_ok] in KW. destruct KW as (_ & FW & RW).
  (* [comment removed for export] *)
  apply existsb_exists in Hunk as (K' & HKu & HKU). destruct K' as [| | | | | | | | |[ub uo] um]; try discriminate.
  apply andb_prop in HKU as [HKU Lum]. apply andb_prop in HKU as [Hub Huo]. apply expr_eqb_eq in Hub. apply Z.eqb_eq in Huo. subst ub uo.
  pose proof (proj1 (Forall_forall _ _) HK _ HKu) as KU. cbn [kentry_ok] in KU. destruct KU as [FU DU]. unfold flat in FU. rewrite !estart_SA in FU, DU.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lum) as Bum. rewrite !GNB.xt_den1 in Bum.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lhi) as Bhi. rewrite GNB.xt_den1, GNB.xt_den2 in Bhi. change (uE E (ELit 0)) with 0 in Bhi.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Ls1) as Bs1. rewrite !GNB.xt_den1 in Bs1. change (uE E (ELit 1)) with 1 in Bs1.
  destruct (xhi (kn cs) L) as [lh|] eqn:Hlh; [|discriminate]. apply Z.leb_le in HLn.
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ HK Hlh) as Blh.
  (* [comment removed for export] *)
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 n HC ltac:(lia) R11) as [G11 _].
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 HC ltac:(lia)) as G10.
  change (Z.of_nat 11) with 11 in G11. change (Z.of_nat 10) with 10 in G10.
  destruct (GCL.ret_lit_sound E cs R ret (co_regs HC) Rret) as (G1 & Hretok & Hretr & _).
  destruct (sp_ok_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN2.FR_SNL HC Hspok ltac:(unfold DN2.FR_SNL; lia)) as (Hsp & Hst & G2 & Hsu).
  specialize (Hsu spb spk Hsq).
  set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (bflat_x_sound RSEGS E M (kn cs) sb sk (eadd L (ELit 8)) HK Hbflat) as (Fs0 & Fsl & Fs64).
  pose proof (u_of_split E (reg cs 10) sb sk Hsqs ltac:(lia)) as Us. rewrite estart_SA in Us.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) sb sk (eadd L (ELit 8)) spb (spk - DN2.FR_SNL) (ELit DN2.FR_SNL) HK Hdisj) as DISJ.
  rewrite !estart_SA in DISJ. unfold elenZ, DN2.FR_SNL in DISJ. cbn [edenot] in DISJ. rewrite u64_lit in DISJ by lia.
  assert (UL8 : uE E (eadd L (ELit 8)) = uE E L + 8).
  { unfold eadd, uE in *. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u64_lit by lia. apply Z.mod_small.
    pose proof (u64_range (edenot E L)). unfold DN.SPHI in Bhi. lia. }
  unfold uE in UL8. rewrite UL8 in Fsl, DISJ. unfold uE in *.
  set (sz := bv_unsigned (edenot E sb) + sk) in *. set (Lz := bv_unsigned (edenot E L)) in *.
  unfold elenZ in *.
  (* [comment removed for export] *)
  destruct (rdn_defined RSEGS M (Z.to_nat (Lz + 8)) (edenot E (reg cs 10))) as (buf & Hbuf & Lbuf).
  { rewrite Us. pose proof (u64_range (edenot E L)). lia. }
  { intros j Hj. unfold GxSymExec3Sound.AX2S.rd1. rewrite Us.
    pose proof (DU (Z.of_nat j) ltac:(pose proof (u64_range (edenot E L)); lia)) as D. destruct (M (Z_to_bv 64 (sz + Z.of_nat j))); [discriminate | exfalso; apply D; reflexivity]. }
  assert (MCH : mchrH M (edenot E (reg cs 10)) buf Lz n).
  { constructor.
    - rewrite Lbuf. exact Hbuf.
    - rewrite Lbuf, Us. pose proof (u64_range (edenot E L)). rewrite Z2Nat.id by lia.
      pose proof (Z.mul_div_le (sz + Lz) 8 ltac:(lia)). lia.
    - rewrite Lbuf, Us. pose proof (u64_range (edenot E L)). rewrite Z2Nat.id by lia. unfold DN.SPHI in Bhi. lia.
    - pose proof (u64_range (edenot E L)). lia.
    - (* [comment removed for export] *)
      pose proof (u64_range (edenot E L)) as UL.
      pose proof (rdn_nth1 (Z.to_nat (Lz + 8)) M (edenot E (reg cs 10)) buf (Z.to_nat Lz) Hbuf ltac:(lia) ltac:(rewrite Us; lia)) as X.
      rewrite Us, Z2Nat.id in X by lia.
      rewrite (adenot_flatZ' E) in RW || idtac.
      assert (AW : adenot E (SA (eadd (reg cs 10) L) 0) = Z_to_bv 64 (sz + Lz)).
      { apply bv_eq. rewrite (flat_u E _ _ FW), estart_SA, u64_lit by lia. unfold eadd. rewrite mkAlu_denot, u_add64. fold Lz. rewrite Us.
        rewrite Z.mod_small by lia. lia. }
      rewrite AW in RW. rewrite RW in X. injection X as X. rewrite <- X. reflexivity.
    - (* [comment removed for export] *)
      intros j Hj. pose proof (u64_range (edenot E L)) as UL.
      pose proof (rdn_nth1 (Z.to_nat (Lz + 8)) M (edenot E (reg cs 10)) buf j Hbuf ltac:(lia) ltac:(rewrite Us; lia)) as X.
      rewrite Us in X. pose proof (BY (Z.of_nat j) ltac:(lia)) as Y. rewrite Nat2Z.id in Y. replace (sz + 0 + Z.of_nat j) with (sz + Z.of_nat j) in Y by lia.
      cbn [rdn] in X. rewrite Y in X. injection X as X. rewrite <- X.
      intros Z0. apply (UINV_nz E jb (co_uinv HC) Hj0).
      assert (EQ : nth j (eb E jb) (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite <- EQ. apply nth_In. lia.
    - lia.
    - exact Hn64.
    - intros i Hi. exact (kimg_covers_sound E M (kn cs) 0x13040 32 HK Hro i Hi). }
  (* [comment removed for export] *)
  assert (E1 : Z_to_bv 5 1 = (1%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E2 : Z_to_bv 5 2 = (2%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 10 = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 11 = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  pose proof G1 as G1'. rewrite E1 in G1'. pose proof G10 as G10'. rewrite E10 in G10'. pose proof G11 as G11'. rewrite E11 in G11'.
  destruct (ref_strnlen (fx:=fx) M (edenot E (reg cs 10)) (getr R (Z_to_bv 5 2)) buf Lz n (seg_rom RSEGS) R (Z_to_bv 64 ret) MCH
              ltac:(lia) ltac:(exact Hst) ltac:(unfold DN.SPLO, DN2.FR_SNL in Hsp; lia) ltac:(rewrite Lbuf, Us, Z2Nat.id by lia; unfold DN2.FR_SNL in *; lia)
              Hretok G1' ltac:(rewrite E2; reflexivity) G10' G11')
    as (regs' & mem' & RUN & KC & A10 & FM).
  unfold cfgF, mkstF. rewrite Hpc. replace (Z_to_bv 64 DN2.P_STRNLEN) with (0x6f380%bv : word) by (apply bv_eq; reflexivity).
  eapply (sr_msteps RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | exact RUN |].
  (* [comment removed for export] *)
  unfold after_call in Hn.
  match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hcc; [|discriminate] end.
  apply andb_prop in Hcc as [Hcc Hrvv]. apply andb_prop in Hcc as [_ Hkv]. injection Hn as Ecs1.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := GCL.ext_call E (nxt cs) regs').
  pose proof (GCL.ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  specialize (Hk E' fx regs' mem' model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  rewrite <- Ecs1 in Hk. unfold cfgF, mkstF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
  pose proof (GPS.cs_ok_agree RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
  pose proof (GNL.keeps_cs_kept_ok R regs' KC) as KEPT.
  destruct FM as [AGR GRW]. subst su.
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC1 | | reflexivity | | exact (co_fx HC) |].
  + cbn [mk_ss s_regs]. apply (GCL.regs_after_call E _ R regs' (nxt cs) (Some L) (co_regs HC) Fsr KEPT).
    split; [exact Hrvv | rewrite E10, A10; unfold Lz; rewrite Z_to_bv_bv_unsigned; reflexivity].
  + cbn [mk_ss s_know]. eapply know_ok_agree'; [exact Hag | exact Hkv |].
    apply (know_ok_havoc RSEGS E M mem'); [exact HK | | exact GRW].
    intros x Hx. apply AGR. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u64_lit by (unfold DN.SPLO, DN.SPHI, DN2.FR_SNL in Hsp; lia).
    rewrite estart_SA in Hx. unfold elenZ, DN2.FR_SNL in Hx |- *. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia. lia.
  + intros a Ha. cbn [a_vis]. rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    pose proof (u64_range a) as Hau.
    split.
    2:{ intros Hn0'. apply Ha. rewrite Hn0'. destruct (M a) eqn:Hma; [|reflexivity]. exfalso. exact (GRW a ltac:(congruence) Hn0'). }
    set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
    assert (Hin : su - 32 <= bv_unsigned a < su).
    { destruct (Z_lt_le_dec (bv_unsigned a) (su - 32)) as [Hlow|Hhigh]; [|destruct (Z_lt_le_dec (bv_unsigned a) su) as [Hi'|Habove]; [lia|]];
        exfalso; apply Ha; apply AGR; cbn [outside]; (split; [|exact I]); unfold in_rng; rewrite u64_lit by (unfold DN.SPLO, DN.SPHI, DN2.FR_SNL in Hsp; lia); lia. }
    right. right. left. rewrite <- (co_top HC).
    unfold DN.frame_ok in Hfr. rewrite Hsq in Hfr.
    assert (Hrng : estart E (SA spb (spk - DN2.FR_SNL)) <= bv_unsigned a < estart E (SA spb (spk - DN2.FR_SNL)) + elenZ E (ELit DN2.FR_SNL)).
    { rewrite estart_SA. unfold elenZ, DN2.FR_SNL in *. cbn [edenot]. rewrite u64_lit by lia. lia. }
    exact (proj1 (GPS.in_floor_sound RSEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - DN2.FR_SNL) (ELit DN2.FR_SNL) a (co_know HC) Hfr (co_floor HC) Hrng)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma read_dir_node : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 63 ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some State.FdDir -> fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  node_ok RSEGS (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret EISDIR))) model).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hfd Hfd32 Haok.
  apply (node_ret_only RSEGS ms model x8 (errno_ret EISDIR) _ [] Hh Hsvc);
    [| exact Hh | exact Hlazy | exact (RomBase.sys_rob_memfree RSEGS ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_63))].
  intros eff. rewrite (check_syscall_63 RSEGS ms x8 eff model Hno). unfold check_read. rewrite Hfd32, Hfd, Haok. reflexivity.
Qed.

Variable DIRD : bool.
Hypothesis FDS3d : DIRD = true -> fd_lookup FDS0 (Z_to_bv 64 3) = Some State.FdDir.

Theorem node_read_dir_sound : DIRD = true ->
  GPS.node1_stmtN RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ GPS.always (DN2.node_read_dir RSEGS).
Proof.
  intros HD cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DN2.node_read_dir in Hn.
  destruct (reg_lit cs 11) as [b|] eqn:R11; [|discriminate].
  destruct (reg_lit cs 12) as [c|] eqn:R12; [|discriminate].
  match type of Hn with (if ?x then _ else _) = _ => destruct x eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hbc]. apply andb_prop in Hc as [Hc Hc0]. apply andb_prop in Hc as [Hc Hb0]. apply andb_prop in Hc as [Hsys H10].
  apply Z.leb_le in Hbc. apply Z.leb_le in Hc0. apply Z.leb_le in Hb0.
  unfold DN.at_sys in Hsys. apply andb_prop in Hsys as [Hec H17].
  unfold DN.reg_is in H17, H10.
  destruct (reg_lit cs 17) as [a7|] eqn:R17; [|discriminate]. apply Z.eqb_eq in H17. subst a7.
  destruct (reg_lit cs 10) as [fd|] eqn:R10; [|discriminate]. apply Z.eqb_eq in H10. subst fd.
  destruct (GPS.is_ecall_at_sound RSEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 17 63 HC ltac:(lia) R17) as [G17 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 3 HC ltac:(lia) R10) as [G10 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 b HC ltac:(lia) R11) as [G11 U11].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 12 c HC ltac:(lia) R12) as [G12 U12].
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  (* [comment removed for export] *)
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17)).
  (* [comment removed for export] *)
  eapply (sr_silent1 RSEGS SR).
  { eapply (read_dir_node _ model (getr R 17)); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | | | |].
    - rewrite G17. apply u64_lit. lia.
    - rewrite ms_gpr_epend0, G10, (co_fds HC). exact (FDS3d HD).
    - rewrite ms_gpr_epend0, G10. vm_compute. reflexivity.
    - rewrite ms_gpr_epend1, ms_gpr_epend2, G11, G12. unfold access_okb, TASK_SIZE.
      rewrite !u64_lit by (unfold two64 in *; lia). apply andb_true_intro. split; apply Z.leb_le; lia. }
  { (* the no-allocation-call check: system call 63, read *)
    apply (grant_ok_sysno _ model (getr R 17) 63); [reflexivity | rewrite G17; apply u64_lit; lia | reflexivity]. }
  (* [comment removed for export] *)
  rewrite adv_set_epend. rewrite v_addi_pc4 by (unfold two64 in *; lia).
  specialize (Hk E fx (regupd R 10 (errno_ret EISDIR)) M model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
  rewrite set_pc_set_reg_eq in Hk. unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc.
  apply Hk; [|reflexivity].
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV);
    [exact HC | | reflexivity | exact (co_know HC) | exact (co_fx HC) | intros a Ha; exfalso; exact (Ha eq_refl)].
  cbn [mk_ss s_regs].
  apply (regs_ok_set_n E (s_regs (a_ss cs)) R 10 (ELit (two64 - 21)) (errno_ret EISDIR) (co_regs HC) ltac:(lia)).
  cbn [edenot]. apply bv_eq. reflexivity.
Qed.

Theorem XEe_sound : GPS.emit_stmt RSEGS nx0 (DN2.XEe RSEGS nx0) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof.
  intros id args cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN2.XEe in Hn.
  do 66 (destruct id as [|id]; [exact (XEd_sound SR nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree SR_det SWINc FDS1 FDS2 _ args cs fd ps cs' E fx R M model T HC Hn HT Hk)|]).
  destruct id as [|id]; [exact (node_stdio_write2_sound cs fd ps cs' E fx R M model T HC Hn HT Hk)|].
  exact (XEd_sound SR nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree SR_det SWINc FDS1 FDS2 _ args cs fd ps cs' E fx R M model T HC Hn HT Hk).
Qed.
End Sound.
End DrvNodes2SoundB.
