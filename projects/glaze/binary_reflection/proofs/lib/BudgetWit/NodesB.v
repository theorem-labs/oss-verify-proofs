(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from DrvNodesSound.v's section Sound, over BudgetWit.Rzb's ShapeRelB.shape_rel and BudgetWit.StdioB; the ioctl node adds the no-allocation-call check (system call 29). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel reader, cs_ok's co_rdr, carried through the node lemmas). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import Ioctl.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.WritevB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStdioDefs. Import OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.RefStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStdioDefs.RefExitBase OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefStdioWriteB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefExitB OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation RSEGS := PSEGS (only parsing).
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.RzbAlg OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.ShapeRelB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.WritevB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefStdioWriteB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefExitB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

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
Hypothesis SR_det : forall c T T', sr_rel RSEGS SR c T -> realizes RSEGS c T' -> t_eq T T'.
(* [comment removed for export] *)
Hypothesis SWINc : forall a, (DN.FILE1 <= a < DN.FILE1 + 232 \/ DN.FILE2 <= a < DN.FILE2 + 232) -> in_wins SWIN a.
(* [comment removed for export] *)
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Lemma FDS12 : forall fd, fd = 1 \/ fd = 2 -> exists ch, fd_lookup FDS0 (Z_to_bv 64 fd) = Some (FdChannel ch).
Proof using FDS2 FDS1. intros fd [-> | ->]; eexists; eassumption. Qed.

#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation cs_ok := (GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation cfg := (cfgF RSEGS).

(* [comment removed for export] *)
Theorem node_ioctl_sound :
  GPS.node1_stmtN RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ GPS.always (DN.node_ioctl RSEGS).
Proof using FDS2 FDS1 AINV_frame SWIN.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DN.node_ioctl in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc H11]. apply andb_prop in Hc as [Hsys H10].
  unfold DN.at_sys in Hsys. apply andb_prop in Hsys as [Hec H17].
  unfold DN.reg_is in H17, H10, H11.
  destruct (reg_lit cs 17) as [a7|] eqn:R17; [|discriminate]. apply Z.eqb_eq in H17. subst a7.
  destruct (reg_lit cs 11) as [rq|] eqn:R11; [|discriminate]. apply Z.eqb_eq in H11. subst rq.
  destruct (reg_lit cs 10) as [fd|] eqn:R10; [|discriminate].
  assert (Hfd12 : fd = 1 \/ fd = 2).
  { apply orb_prop in H10 as [H|H]; apply Z.eqb_eq in H; lia. }
  destruct (GPS.is_ecall_at_sound RSEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 17 29 HC ltac:(lia) R17) as [G17 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 fd HC ltac:(lia) R10) as [G10 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 0x5413 HC ltac:(lia) R11) as [G11 _].
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11.
  (* [comment removed for export] *)
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17)).
  (* [comment removed for export] *)
  destruct (FDS12 fd Hfd12) as [ch He].
  eapply (sr_silent1 RSEGS SR).
  { eapply (ioctl_tty_node _ model (getr R 17) fd ch); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | | | lia | |].
    - rewrite G17. apply u64_lit. lia.
    - rewrite ms_gpr_epend0. exact G10.
    - rewrite (co_fds HC). exact He.
    - rewrite ms_gpr_epend1, G11. vm_compute. reflexivity. }
  { (* the no-allocation-call check: system call 29, ioctl *)
    apply (grant_ok_sysno _ model (getr R 17) 29); [reflexivity | rewrite G17; apply u64_lit; lia | reflexivity]. }
  (* [comment removed for export] *)
  rewrite adv_set_epend. rewrite v_addi_pc4 by (unfold two64 in *; lia).
  specialize (Hk E fx (regupd R 10 (errno_ret ENOTTY)) M model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
  rewrite set_pc_set_reg_eq in Hk. unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc.
  apply Hk; [|reflexivity].
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV);
    [exact HC | | reflexivity | exact (co_know HC) | exact (co_fx HC) | intros a Ha; exfalso; exact (Ha eq_refl)].
  cbn [mk_ss s_regs].
  apply (regs_ok_set_n E (s_regs (a_ss cs)) R 10 (ELit (two64 - 25)) (errno_ret ENOTTY) (co_regs HC) ltac:(lia)).
  cbn [edenot]. apply bv_eq. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fetch_exit_ecall : fetch_word RSEGS (Z_to_bv 64 DN.P_EXIT_ECALL) = Some (Z_to_bv 32 0x73).
Proof using. vm_compute. reflexivity. Qed.

Lemma wtlb1_0 : word_to_le_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof using. reflexivity. Qed.

(* [comment removed for export] *)
Lemma set_pc_set_reg2_eq : forall cs n1 e1 n2 e2 p,
  set_pc (set_reg (set_reg cs n1 e1) n2 e2) p = with_ss cs (mk_ss p (sr_upd (sr_upd (s_regs (a_ss cs)) n1 e1) n2 e2) (kn cs) (nxt cs)).
Proof using. reflexivity. Qed.

Lemma exit_succ_ok : forall E cs fx R M model,
  cs_ok E cs fx R M model -> length (s_regs (a_ss cs)) = 32%nat ->
  cs_ok E (DN.exit_succ cs) fx (regupd (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) (Z_to_bv 5 17) (Z_to_bv 64 94)) M model.
Proof using AINV_frame SWIN.
  intros E cs fx R M model HC Hlen. unfold DN.exit_succ. rewrite set_pc_set_reg2_eq.
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV);
    [exact HC | | reflexivity | exact (co_know HC) | exact (co_fx HC) | intros a Ha; exfalso; exact (Ha eq_refl)].
  cbn [mk_ss s_regs].
  apply (regs_ok_set_n E (sr_upd (s_regs (a_ss cs)) 10 (reg cs 8)) (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) 17 (ELit 94) (Z_to_bv 64 94)); [| lia | reflexivity].
  apply (regs_ok_set_n E (s_regs (a_ss cs)) R 10 (reg cs 8) (getr R (Z_to_bv 5 8)) (co_regs HC) ltac:(lia)).
  symmetry. exact (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 8 HC ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma stdout_pending_sound : forall E M k zs,
  know_ok RSEGS E M k -> DN.stdout_pending RSEGS k = Some zs ->
  Forall (fun z => 0 <= z < 256) zs /\
  ( (zs = [] /\ exists wp1 rp1, file_clean M 0x75858 wp1 rp1)
    \/ (exists wb wp bufp bufsz rp1 can, stdout_pending M wb wp bufp bufsz rp1 can (map (Z_to_bv 8) zs)) ).
Proof using.
  intros E M k zs HK H. unfold DN.stdout_pending in H.
  destruct (DN.kimg_covers k DN.FILE1 232) eqn:Himg.
  { injection H as <-. split; [constructor|]. left. split; [reflexivity|].
    pose proof (kimg_covers_sound E M k DN.FILE1 232 HK Himg) as PR. unfold DN.FILE1 in PR.
    exists (Z_to_bv 64 0), (Z_to_bv 64 0). unfold file_clean.
    repeat split; (eapply (rdn_pristine M 0x75858 (0x75858 + 232)); [exact PR | lia | cbn; lia | lia | lia | ]);
      [exact img_stdout_lock | exact img_stdout_wpos | exact img_stdout_wbase | exact img_stdout_rpos | exact img_stdout_rend]. }
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 140) 4) as [lock|] eqn:Hlock; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 72) 8) as [wr|] eqn:Hwr; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 120) 4) as [fd|] eqn:Hfd; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 88) 8) as [buf|] eqn:Hbuf; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 96) 8) as [bsz|] eqn:Hbsz; [|discriminate].
  match type of H with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in H.
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 56) 8) as [wb|] eqn:Hwb; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 40) 8) as [wp|] eqn:Hwp; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 8) 8) as [rp|] eqn:Hrp; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 16) 8) as [re|] eqn:Hre; [|discriminate].
  match type of H with (if negb ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end. cbn [negb] in H.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  rename X into Ebsz. rename X0 into Ebuf. rename X1 into Efd. rename X2 into Ewr.
  apply Z.eqb_eq in Hc. apply Z.eqb_eq in Ewr. apply Z.eqb_eq in Efd. apply Z.eqb_eq in Ebuf. apply Z.eqb_eq in Ebsz. subst lock wr fd buf bsz.
  repeat match type of Hc2 with (_ && _)%bool = true => apply andb_prop in Hc2 as [Hc2 ?X] end.
  rename X into Wmax. rename X0 into W3. rename X1 into W2. rename X2 into W1.
  apply Z.eqb_eq in Hc2. apply Z.leb_le in W1. apply Z.leb_le in W2. apply Z.leb_le in W3. apply Z.leb_le in Wmax. subst re.
  unfold DN.FILE1, DN.SBUF, DN.SBUF_SZ, DN.P_STDIO_WRITE, DN.RW_MAX in *.
  pose proof (fun a w z H Hw Ha Ha8 => proj1 (kreadZ_lit0_sound E M k a w z HK H Hw Ha Ha8)) as RD.
  specialize (RD _ _ _ Hlock ltac:(lia) ltac:(lia) ltac:(lia)) as Rlock.
  specialize (RD _ _ _ Hwr ltac:(lia) ltac:(lia) ltac:(lia)) as Rwr.
  specialize (RD _ _ _ Hfd ltac:(lia) ltac:(lia) ltac:(lia)) as Rfd.
  specialize (RD _ _ _ Hbuf ltac:(lia) ltac:(lia) ltac:(lia)) as Rbuf.
  specialize (RD _ _ _ Hbsz ltac:(lia) ltac:(lia) ltac:(lia)) as Rbsz.
  specialize (RD _ _ _ Hwb ltac:(lia) ltac:(lia) ltac:(lia)) as Rwb.
  specialize (RD _ _ _ Hwp ltac:(lia) ltac:(lia) ltac:(lia)) as Rwp.
  specialize (RD _ _ _ Hrp ltac:(lia) ltac:(lia) ltac:(lia)) as Rrp.
  specialize (RD _ _ _ Hre ltac:(lia) ltac:(lia) ltac:(lia)) as Rre.
  destruct (Z.eqb wb wp) eqn:Hwbwp.
  - (* [comment removed for export] *)
    injection H as <-. apply Z.eqb_eq in Hwbwp. subst wp. split; [constructor|]. left. split; [reflexivity|].
    exists (Z_to_bv 64 wb), (Z_to_bv 64 rp). unfold file_clean. repeat split; assumption.
  - destruct (DN.ssp_ok RSEGS k) eqn:Hssp; [|discriminate].
    apply Z.eqb_neq in Hwbwp.
    destruct (kbytes_lit0_sound E M k _ wb zs HK H ltac:(lia) ltac:(lia)) as (Rzs & Lzs & Fzs).
    destruct (ssp_ok_sound E M k HK Hssp) as [can Hcan].
    split; [exact Fzs|]. right.
    exists wb, wp, (Z_to_bv 64 0xa6bf8), (Z_to_bv 64 1024), (Z_to_bv 64 rp), can.
    constructor; try assumption.
    + lia.
    + rewrite length_map. lia.
    + rewrite length_map. unfold rw_bytes_max. lia.
    + rewrite length_map, Lzs. replace (Z.to_nat (wp - wb)) with (length zs) in Rzs by lia. rewrite <- Lzs. 
      rewrite Lzs. rewrite <- Lzs at 1. exact Rzs.
Qed.

Theorem node_exit_sound : forall cs fd ps cs' E fx R M model T,
  cs_ok E cs fx R M model -> DN.node_exit RSEGS cs = Some (fd, ps, cs') -> T [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Proof using FDS1 SR_det AINV_frame SWIN.
  intros cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN.node_exit in Hn.
  destruct (Z.eqb (pc cs) DN.P_EXIT) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 8) as [code|] eqn:R8; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:R4; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 40)) as [w2|] eqn:Hw2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 56)) as [b2|] eqn:Hb2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 8)) as [r2|] eqn:Hr2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 16)) as [e2|] eqn:He2; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN.stdout_pending RSEGS (kn cs)) as [zs|] eqn:Hpend; [|discriminate].
  injection Hn as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hcells]. apply andb_prop in Hc as [Htp Hspok].
  apply Z.eqb_eq in Htp. subst tp. apply Nat.eqb_eq in Hlen.
  apply andb_prop in Hc2 as [E1 E2]. apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. subst b2 e2.
  (* [comment removed for export] *)
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 8 code HC ltac:(lia) R8) as [G8 Hcode].
  change (Z.of_nat 8) with 8 in G8.
  destruct (sp_ok_up_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN.FR_EXIT DN.UP_EXIT HC Hspok ltac:(unfold DN.FR_EXIT; lia) ltac:(unfold DN.UP_EXIT; lia)) as (Hsplo & Hsphi & Hst & _).
  (* [comment removed for export] *)
  pose proof (cells_ok_sound E M (kn cs) DN.exit_cells (co_know HC) Hcells) as CE. unfold DN.exit_cells, DN.FILE1, DN.FILE2 in CE.
  repeat match type of CE with Forall _ (_ :: _) => apply Forall_cons_iff in CE as [?X CE] end. clear CE.
  repeat match goal with X : (1 <= ?w <= 8)%nat -> 0 <= ?a -> ?a + _ <= 2 ^ 64 -> _ |- _ => specialize (X ltac:((first [ (clear SWINc; lia) | lia ])) ltac:((first [ (clear SWINc; lia) | lia ])) ltac:((first [ (clear SWINc; lia) | lia ]))) end.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) Hw2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Rw2.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) Hb2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Rb2.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) Hr2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Rr2.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) He2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Re2.
  destruct (stdout_pending_sound E M (kn cs) zs (co_know HC) Hpend) as [Fzs PEND].
  (* [comment removed for export] *)
  set (spn := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  pose proof (u64_range (getr R (Z_to_bv 5 2))) as Hspu.
  set (spe := Z_to_bv 64 (spn + 16)).
  assert (Hspe : bv_unsigned spe = spn + 16) by (subst spe; unfold DN.SPHI, DN.UP_EXIT in Hsphi; rewrite u64_lit by lia; reflexivity).
  (* [comment removed for export] *)
  assert (EC : exit_common R M spe (Z_to_bv 64 code) (edenot E w2) (edenot E r2)).
  { unfold DN.SPLO, DN.SPHI, DN.FR_EXIT, DN.UP_EXIT, DN.FILE2 in *.
    constructor.   (* [comment removed for export] *)
    - rewrite Hspe. replace (spn + 16 - 16) with spn by lia. subst spn. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact G8.
    - rewrite Hspe. lia.
    - rewrite Hspe. lia.
    - rewrite Hspe. replace (spn + 16 - 144) with (spn - 128) by lia. exact Hst.
    - unfold stdio_globals; repeat split; try assumption;
        (match goal with X : rdn _ _ (Z_to_bv 64 0xa67b3) 1%nat = _ |- _ => rewrite X end; rewrite wtlb1_0; reflexivity).
    - unfold file_clean; repeat split; assumption. }
  assert (PRE : exit_pre R M model (Z_to_bv 64 code) (map (Z_to_bv 8) zs)).
  { exists spe, (edenot E w2), (edenot E r2).
    split; [exact EC|]. split; [exact (co_halt HC)|]. split; [exact (co_lazy HC)|].
    destruct PEND as [[-> CL] | PD]; [left; split; [reflexivity | exact CL] | right].
    destruct PD as (wb & wp & bufp & bufsz & rp1 & can & PD). exists wb, wp, bufp, bufsz, rp1, can.
    split; [exact PD | split; [rewrite (co_fds HC); exact FDS1 | exact (co_rdr HC)]]. }
  (* [comment removed for export] *)
  set (R' := regupd (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) (Z_to_bv 5 17) (Z_to_bv 64 94)).
  assert (G17 : getr R' (Z_to_bv 5 17) = Z_to_bv 64 94) by (unfold R'; apply getr_same; intro; discriminate).
  assert (G10' : getr R' (Z_to_bv 5 10) = Z_to_bv 64 code).
  { unfold R'. transitivity (getr (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) (Z_to_bv 5 10)).
    - unfold getr. rewrite regupd_other by (intro; discriminate). reflexivity.
    - rewrite getr_same by (intro; discriminate). exact G8. }
  pose proof (Hk E fx R' M model (conj (env_agree_refl _ _) (env_agree_refl _ _)) (exit_succ_ok E cs fx R M model HC Hlen) eq_refl) as HKT.
  unfold cfgF in HKT. cbn [pc DN.exit_succ set_pc set_reg with_ss a_ss mk_ss s_pc] in HKT.
  pose proof (LibWritevF.rz_exit_at (fx:=fx) RSEGS R' (Z_to_bv 64 DN.P_EXIT_ECALL) M (seg_rom RSEGS) model (Z_to_bv 32 0x73) (Z_to_bv 64 code)
                fetch_exit_ecall eq_refl (co_halt HC) (co_lazy HC) (or_introl G17) G10') as RX.
  unfold mkstF in HKT. pose proof (SR_det _ _ _ HKT RX) as TEQ.
  (* [comment removed for export] *)
  unfold cfgF, mkstF. rewrite Hpc.
  eapply (sr_conseq RSEGS SR); [apply (sr_of_realizes RSEGS SR); apply (ref_exit_Z (fx:=fx) R M model (Z_to_bv 64 code) (map (Z_to_bv 8) zs) PRE)|].
  assert (HW : Spec4.W 1 (map (Z_to_bv 8) zs) = Wp E 1 match zs with [] => [] | _ :: _ => [SPLit zs] end).
  { unfold Spec4.W, Wp. destruct zs; [reflexivity|]. cbn [flat_map piece_den]. rewrite app_nil_r. reflexivity. }
  rewrite HW. apply Spec4.AgentLib.t_emit_congr. apply t_eq_sym. exact TEQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_nth_seq : forall {A} (l : list A) (d : A), map (fun j => nth j l d) (seq 0 (length l)) = l.
Proof using.
  intros A l d. induction l as [|x l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. exact IH.
Qed.

(* [comment removed for export] *)
Lemma file_lits_sound : forall E M k f fd buf bsz wb wp,
  know_ok RSEGS E M k -> DN.file_lits RSEGS k f = Some (fd, buf, bsz, wb, wp) -> 0 <= f -> f + 232 <= 2 ^ 64 ->
  sw_file M f wb wp fd (Z_to_bv 64 buf) (Z_to_bv 64 bsz) /\ 0 <= fd < two64 /\ 0 <= wb < two64 /\ 0 <= wp < two64 /\ 0 <= buf < two64 /\ 0 <= bsz < two64.
Proof using.
  intros E M k f fd buf bsz wb wp HK H Hf0 Hf8. unfold DN.file_lits in H.
  destruct (kreadZ RSEGS k (ELit 0) (f + 120) 4) as [x1|] eqn:H1; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 88) 8) as [x2|] eqn:H2; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 96) 8) as [x3|] eqn:H3; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 56) 8) as [x4|] eqn:H4; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 40) 8) as [x5|] eqn:H5; [|discriminate].
  injection H as <- <- <- <- <-.
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H1 ltac:(lia) ltac:(lia) ltac:(lia)) as [R1 B1].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H2 ltac:(lia) ltac:(lia) ltac:(lia)) as [R2 B2].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H3 ltac:(lia) ltac:(lia) ltac:(lia)) as [R3 B3].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H4 ltac:(lia) ltac:(lia) ltac:(lia)) as [R4 B4].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H5 ltac:(lia) ltac:(lia) ltac:(lia)) as [R5 B5].
  split; [constructor; assumption | repeat split; lia].
Qed.

(* [comment removed for export] *)
Lemma range_pieces_sound : forall E M k (se le : expr) sb sk ext,
  know_ok RSEGS E M k -> DN.range_pieces RSEGS k se le = Some ext -> split_lit se = (sb, sk) ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + bv_unsigned (edenot E le) <= 2 ^ 64 -> estart E (SA sb sk) < 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 (estart E (SA sb sk))) (length (flat_map (piece_den E) ext)) = Some (flat_map (piece_den E) ext)
  /\ Z.of_nat (length (flat_map (piece_den E) ext)) = bv_unsigned (edenot E le).
Proof using.
  intros E M k se le sb sk ext HK H Hsq Hlo Hhi H64. unfold DN.range_pieces in H. rewrite Hsq in H.
  destruct (lit_of le) as [m|] eqn:Hm.
  - destruct le as [z| | | | | | |]; try discriminate. cbn [lit_of] in Hm. injection Hm as <-.
    assert (Hul : bv_unsigned (edenot E (ELit z)) = z mod two64).
    { cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. }
    pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as Hzr.
    destruct (z mod two64) as [|pm|nm] eqn:Hz.
    + injection H as <-. cbn [flat_map length Z.of_nat]. split; [reflexivity | lia].
    + destruct (Z.ltb 4096 (Z.pos pm)); [discriminate|].
      destruct (DN.kbytes RSEGS (Z.to_nat (Z.pos pm)) k sb sk) as [bs|] eqn:Hb; [|discriminate]. injection H as <-.
      unfold DN.kbytes in Hb.
      destruct (GCL.kread_bytes_sound RSEGS E M k _ sb sk bs HK Hb Hlo ltac:(lia)) as (R & L & _).
      cbn [flat_map piece_den]. rewrite app_nil_r, length_map, L. split; [exact R | lia].
    + lia.
  - destruct (List.find _ k) as [K|] eqn:HF; [|discriminate].
    apply find_some in HF as [HinK HK2].
    destruct K as [| |[kb ko] kl j| | | | | | |]; try discriminate. injection H as <-.
    apply andb_prop in HK2 as [HK2 El]. apply andb_prop in HK2 as [Eb Eo].
    apply expr_eqb_eq in Eb. apply Z.eqb_eq in Eo. apply expr_eqb_eq in El. subst kb ko kl.
    pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KO. cbn [kentry_ok] in KO. destruct KO as (Hfl & Hlen & Hby).
    cbn [flat_map piece_den]. rewrite app_nil_r. unfold elenZ in Hlen, Hby. split; [|lia].
    rewrite <- (map_nth_seq (eb E j) (Z_to_bv 8 0)) at 2. apply GCL.rdn_of_nth.
    + rewrite u64_lit by lia. lia.
    + intros i Hi. rewrite u64_lit by lia. apply GCL.rdn1_overlay. rewrite <- (Nat2Z.id i) at 2. apply Hby. lia.
Qed.

(* [comment removed for export] *)
Lemma know_after_sw : forall E M M' k spb spk (su f buf bsz : Z),
  know_ok RSEGS E M k ->
  bv_unsigned (edenot E spb) + spk = su -> 112 <= su -> 0 <= f -> f + 232 <= 2 ^ 64 -> 0 <= buf < two64 -> 0 <= bsz < two64 ->
  sw_post M su f (Z_to_bv 64 buf) (Z_to_bv 64 bsz) M' ->
  know_ok RSEGS E M'
    ([KWord (SA (ELit 0) (f + 32)) 8 (ELit (buf + bsz)); KWord (SA (ELit 0) (f + 40)) 8 (ELit buf); KWord (SA (ELit 0) (f + 56)) 8 (ELit buf)]
     ++ kn_havoc (kn_havoc k spb (spk - DN.FR_SW) (ELit DN.FR_SW)) (ELit 0) (f + 32) (ELit 32)).
Proof using.
  intros E M M' k spb spk su f buf bsz HK Hsu Hsu112 Hf0 Hf8 Hbuf Hbsz [AG GR WE WP WB].
  apply Forall_app. split.
  - repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok]; (split; [lia|]); (split; [unfold flat; rewrite estart_lit0; lia|]);
      rewrite GCL.adenot_SA, estart_lit0; cbn [edenot].
    + rewrite WE. do 2 f_equal. apply bv_eq. rewrite (bv_add_unsigned (Z_to_bv 64 buf)). rewrite !Z_to_bv_unsigned.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). unfold two64 in *.
      rewrite (Z.mod_small buf), (Z.mod_small bsz) by lia. reflexivity.
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

(* [comment removed for export] *)
Ltac in_list_solve := cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma kept_ok_intro : forall R R' : bvmap 5 word,
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
  GCL.kept_ok R R'.
Proof using.
  intros R R' H r Hr0 Hncs. pose proof (ridx_range r) as Hr.
  assert (Hz : ridx r <> 0%nat).
  { intros Hz. apply Hr0. rewrite (GCL.reg_of_ridx r _ eq_refl), Hz. apply bv_eq. reflexivity. }
  apply H. rewrite (GCL.reg_of_ridx r (ridx r) eq_refl). unfold caller_saved in Hncs.
  destruct (ridx r) as [|n]; [lia|].
  do 31 (destruct n as [|n]; [first [in_list_solve; fail | exfalso; apply Hncs; cbn [In]; (first [ (clear SWINc; lia) | lia ]) | idtac] |]); [..|(first [ (clear SWINc; lia) | lia ])];
    first [in_list_solve | exfalso; apply Hncs; cbn [In]; lia].
Qed.

Theorem node_stdio_write_sound : forall cs fd ps cs' E fx R M model T,
  cs_ok E cs fx R M model -> DN.node_stdio_write RSEGS nx0 cs = Some (fd, ps, cs') -> T [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Proof using FDS2 FDS1 SWINc UINV_agree AINV_frame SWIN.
  intros cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN.node_stdio_write in Hn.
  destruct (Z.eqb (pc cs) DN.P_STDIO_WRITE) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 10) as [f|] eqn:R10; [|discriminate].
  destruct (ret_lit cs) as [ret|] eqn:Rret; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN.file_lits RSEGS (kn cs) f) as [[[[[fdv buf] bsz] wb] wp]|] eqn:Hfl; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg2; [|discriminate] end. cbn [negb] in Hn.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsqs.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  cbv zeta in Hn.
  destruct (xhi (kn cs) (reg cs 12)) as [lh|] eqn:Hlh; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [sh|] eqn:Hsh; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg3; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN.kbytes RSEGS (Z.to_nat (wp - wb)) (kn cs) (ELit 0) wb) as [pend|] eqn:Hpend; [|discriminate].
  destruct (DN.range_pieces RSEGS (kn cs) (reg cs 11) (reg cs 12)) as [ext|] eqn:Hext; [|discriminate].
  match type of Hn with context [after_call ?a ?b ?c ?d ?e] => destruct (after_call a b c d e) as [cs1|] eqn:Hac; [|discriminate] end.
  injection Hn as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hg1 as [Hg1 Hlen]. apply andb_prop in Hg1 as [Hg1 Hfresh]. apply andb_prop in Hg1 as [Hg1 Hssp].
  apply andb_prop in Hg1 as [Hg1 Hfr]. apply andb_prop in Hg1 as [Hf12 Hspok]. apply Nat.eqb_eq in Hlen.
  apply andb_prop in Hg2 as [Hg2 Wbsz0]. apply andb_prop in Hg2 as [Hg2 Wbufhi]. apply andb_prop in Hg2 as [Hg2 Wbuflo].
  apply andb_prop in Hg2 as [Hg2 Wrng]. apply andb_prop in Hg2 as [Hg2 Wlen]. apply andb_prop in Hg2 as [Hfd Wle].
  apply Z.leb_le in Wbsz0. apply Z.leb_le in Wbufhi. apply Z.leb_le in Wbuflo. apply Z.leb_le in Wlen. apply Z.leb_le in Wle.
  apply andb_prop in Hg3 as [Hg3 Hsd]. apply andb_prop in Hg3 as [Hlok Hs47]. apply andb_prop in Hsd as [Hbflat Hdisj].
  apply Z.leb_le in Hlok. apply Z.leb_le in Hs47.
  assert (Hfdv : (fdv = 1 \/ fdv = 2) /\ (f = DN.FILE1 \/ f = DN.FILE2)).
  { apply orb_prop in Hfd as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_eq in H2; subst; tauto. }
  destruct Hfdv as [Hfdv Hf].
  assert (Hfb : 0x75000 <= f /\ f + 232 <= 0xa6790) by (unfold DN.FILE1, DN.FILE2 in Hf; lia).
  assert (Hwr : (wb = 0 /\ wp = 0) \/ (0x75000 <= wb /\ wp <= 0xa7000)).
  { apply orb_prop in Wrng as [H|H]; apply andb_prop in H as [H1 H2]; [apply Z.eqb_eq in H1; apply Z.eqb_eq in H2 | apply Z.leb_le in H1; apply Z.leb_le in H2]; lia. }
  clear Hfd Wrng.
  (* [comment removed for export] *)
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 f HC ltac:(lia) R10) as [G10 _].
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)) as G11.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 12 HC ltac:(lia)) as G12.
  change (Z.of_nat 10) with 10 in G10. change (Z.of_nat 11) with 11 in G11. change (Z.of_nat 12) with 12 in G12.
  destruct (GCL.ret_lit_sound E cs R ret (co_regs HC) Rret) as (G1 & Hretok & Hretr & _).
  destruct (sp_ok_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN.FR_SW HC Hspok ltac:(unfold DN.FR_SW; lia)) as (Hsp & Hst & G2 & Hsu).
  specialize (Hsu spb spk Hsq).
  set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (file_lits_sound E M (kn cs) f fdv buf bsz wb wp (co_know HC) Hfl ltac:(lia) ltac:(lia)) as (SWF & Bfd & Bwb & Bwp & Bbuf & Bbsz).
  destruct (ssp_ok_sound E M (kn cs) (co_know HC) Hssp) as [can Hcan].
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ (co_know HC) Hlh) as Blh.
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ (co_know HC) Hsh) as Bsh.
  destruct (bflat_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) (co_know HC) Hbflat) as (Fs0 & Fsl & Fs64).
  pose proof (u_of_split E (reg cs 11) sb sk Hsqs ltac:(lia)) as Us.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) spb (spk - DN.FR_SW) (ELit DN.FR_SW) (co_know HC) Hdisj) as DISJ.
  rewrite !estart_SA in DISJ. unfold elenZ, DN.FR_SW in DISJ. cbn [edenot] in DISJ. rewrite u64_lit in DISJ by lia. rewrite estart_SA in Us.
  destruct (kbytes_lit0_sound E M (kn cs) _ wb pend (co_know HC) Hpend ltac:((first [ (clear DISJ Hf Hfdv SWINc; lia) | lia ])) ltac:(unfold two64 in *; (first [ (clear DISJ Hf Hfdv SWINc; lia) | lia ]))) as (Rpend & Lpend & Fpend).
  destruct (range_pieces_sound E M (kn cs) (reg cs 11) (reg cs 12) sb sk ext (co_know HC) Hext Hsqs Fs0 Fsl Fs64) as [Rext Lext].
  set (extra := flat_map (piece_den E) ext) in *.
  (* [comment removed for export] *)
  assert (HW : Wp E fdv ((match pend with [] => [] | _ :: _ => [SPLit pend] end) ++ ext) = map (WriteEv (Z_to_bv 64 fdv)) (map (Z_to_bv 8) pend ++ extra)).
  { unfold Wp. f_equal. rewrite flat_map_app. fold extra. destruct pend; [reflexivity|]. cbn [flat_map piece_den]. rewrite app_nil_r. reflexivity. }
  rewrite HW. unfold cfgF, mkstF. rewrite Hpc.
  replace (Z_to_bv 64 DN.P_STDIO_WRITE) with (0x649a0%bv : word) by (apply bv_eq; reflexivity).
  apply (ref_stdio_write_R (fx:=fx) SR R M model su f wb wp fdv (edenot E (reg cs 11)) (edenot E (reg cs 12))
           (Z_to_bv 64 buf) (Z_to_bv 64 bsz) can (Z_to_bv 64 ret) (map (Z_to_bv 8) pend) extra T).
  all: try assumption.
  - subst su. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - unfold DN.SPLO, DN.FR_SW in Hsp. lia.
  - unfold DN.SPHI in Hsp. lia.
  - lia.
  - lia.
  - lia.
  - rewrite (co_fds HC). destruct Hfdv as [-> | ->]; [exact FDS1 | exact FDS2].
  - (* the channel reader: [cs_ok]'s [co_rdr] *) exact (co_rdr HC).
  - exact (co_halt HC).
  - exact (co_lazy HC).
  - lia.
  - lia.
  - rewrite length_map. (first [ (clear DISJ Hf Hfdv SWINc; lia) | lia ]).
  - lia.
  - rewrite length_map. unfold rw_bytes_max, DN.RW_MAX in *. lia.
  - rewrite length_map. unfold DN.RW_MAX in *. lia.
  - unfold DN.SPLO, DN.FR_SW in Hsp. lia.
  - unfold DN.FR_SW in *. lia.
  - unfold DN.SPHI in *. lia.
  - rewrite length_map, Lpend. exact Rpend.
  - rewrite estart_SA in Rext. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (reg cs 11))), Us. exact Rext.
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
      apply (know_after_sw E M mem' (kn cs) spb spk su f buf bsz (co_know HC)); try assumption; try (first [ (clear Hwr Hfdv SWINc; lia) | lia ]).
      unfold DN.SPLO, DN.FR_SW in Hsp. lia.
    + intros a Ha. cbn [a_vis]. rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
      destruct POST as [AG GR _ _ _]. pose proof (u64_range a) as Hau.
      split.
      2:{ intros Hn0. apply Ha. rewrite Hn0. destruct (M a) eqn:Hma; [|reflexivity]. exfalso. exact (GR a ltac:(congruence) Hn0). }
      destruct (Z_lt_le_dec (bv_unsigned a) (su - 112)) as [Hlow|Hhigh]; [|destruct (Z_lt_le_dec (bv_unsigned a) su) as [Hin|Habove]].
      * (* [comment removed for export] *) right. right. right. apply SWINc.
        assert (~ (~ f + 32 <= bv_unsigned a < f + 48 /\ ~ f + 56 <= bv_unsigned a < f + 64)) as Hx by (intros [X1 X2]; apply Ha; apply AG; lia).
        unfold DN.FILE1, DN.FILE2 in *. (first [ (clear HW DISJ Hwr Hf Hfdv Hk Ecs1; lia) | lia ]).
      * (* [comment removed for export] *) right. right. left. rewrite <- (co_top HC).
        unfold DN.frame_ok in Hfr. rewrite Hsq in Hfr.
        assert (Hrng : estart E (SA spb (spk - DN.FR_SW)) <= bv_unsigned a < estart E (SA spb (spk - DN.FR_SW)) + elenZ E (ELit DN.FR_SW)).
        { rewrite estart_SA. unfold elenZ, DN.FR_SW in *. cbn [edenot]. rewrite u64_lit by lia. (first [ (clear Hwr Hf Hfdv; lia) | lia ]). }
        exact (proj1 (GPS.in_floor_sound RSEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - DN.FR_SW) (ELit DN.FR_SW) a (co_know HC) Hfr (co_floor HC) Hrng)).
      * exfalso. unfold DN.SPLO, DN.FR_SW, DN.FILE1, DN.FILE2 in *. apply Ha. apply AG; (first [ (clear HW DISJ Hwr Hfdv; lia) | lia ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem XNd_sound : GPS.ext_stmt RSEGS nx0 (DN.XNd RSEGS) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof using FDS2 FDS1 AINV_frame SWIN.
  intros id args cs cs' E fx R M model T HT HC Hp Hn Hk. unfold DN.XNd in Hn.
  do 63 (destruct id as [|id]; [discriminate|]).
  destruct id as [|id]; [exact (node_ioctl_sound cs cs' E fx R M model T HT HC Hp Hn Hk) | discriminate].
Qed.

Theorem XEd_sound : GPS.emit_stmt RSEGS nx0 (DN.XEd RSEGS nx0) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof using FDS2 FDS1 SWINc SR_det UINV_agree AINV_frame SWIN.
  intros id args cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN.XEd in Hn.
  do 64 (destruct id as [|id]; [discriminate|]).
  destruct id as [|id]; [exact (node_stdio_write_sound cs fd ps cs' E fx R M model T HC Hn HT Hk)|].
  destruct id as [|id]; [exact (node_exit_sound cs fd ps cs' E fx R M model T HC Hn HT Hk)|].
  discriminate.
Qed.

End Sound.
