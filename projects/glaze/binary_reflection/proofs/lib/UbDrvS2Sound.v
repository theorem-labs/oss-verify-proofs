(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.UbDrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
(* [comment removed for export] *)
Ltac lia ::= Zify.zify; xlia zchecker.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Strategy opaque [hR0 hV0b hVSb1 hVSb2 hVFb hV0n hV1_0 hV1_Sn hV1_Sb hV1_F].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma entails_t_tenv : forall {RC : run_ceil} PERMc SPTOPc FS0 FDS0 AINV (U U' : env -> Prop) (E : env) (cs T : acs) (th : list expr) fx R M model,
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U E cs fx R M model ->
  entails_t ADRV 0 cs T th = true ->
  U' (tenv E th) ->
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U' (tenv E th) T fx R M model /\ pc T = pc cs.
Proof.
  intros RC PERMc SPTOPc FS0 FDS0 AINV U U' E cs T th fx R M model HC H HU'. unfold entails_t in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => clear Hl end.
  match goal with Hl : th_id_below 0 th = true |- _ => clear Hl end.
  match goal with Hl : regs_ent _ _ _ _ = true |- _ => rename Hl into Hregs end.
  match goal with Hl : kn_ent _ _ _ = true |- _ => rename Hl into Hkn end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_vis T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hvis end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_ghost T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hgh end.
  match goal with Hl : expr_eqb (tsubst th (a_brk T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hbrk end.
  match goal with Hl : Z.leb (a_ylo T) (a_ylo cs) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hylo end.
  match goal with Hl : list_eqb amap_eqb (a_maps cs) (a_maps T) = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hl; rename Hl into Hmaps end.
  match goal with Hl : AP.maps_vars_lt 0 (a_maps T) = true |- _ => rename Hl into Hmv end.
  set (E' := tenv E th).
  split; [|symmetry; exact Hpc].
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor; try assumption.
  - (* [comment removed for export] *)
    apply (proj1 (GPS.regs_ok_tsubst E th (s_regs (a_ss T)) R)).
    destruct (GPS.regs_ent_sound RSEGS E M (kn cs) _ _ 0%nat CK Hregs) as [Hlen Hn].
    intros r. rewrite (CR r). unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|]. symmetry. apply Hn.
    intros Hz. cbn in Hz. unfold ridx in Hz. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0. apply Hr0.
    change (bv_unsigned r = 0). pose proof (u5_range r). (first [ (clear - H Hr0 Hz; lia) | lia ]).
  - (* [comment removed for export] *)
    apply (proj1 (GPS.know_ok_ktsubst RSEGS E th M (kn T))). eapply (GPS.kn_ent_sound RSEGS ADRV ubsan_in_hull ubsan_hull_ok); [exact CK | exact Hkn].
  - (* [comment removed for export] *)
    unfold E'. rewrite <- GPS.blocks_den_ptsubst, <- GPS.bcost_ptsubst, Hvis. unfold bcount in *. rewrite <- (length_map (ptsubst th)), Hvis. exact CA.
  - (* [comment removed for export] *) unfold E'. rewrite <- GPS.wins_den_ptsubst, Hgh. exact CP.
  - (* [comment removed for export] *) unfold E'. rewrite <- GPS.sptop_den_tsubst, Hbrk. exact CT.
  - (* [comment removed for export] *)
    rewrite <- Hmaps. eapply (GPS.floor_sem_xfer E E' (a_maps cs) (a_brk cs) (a_brk T) (a_ylo cs) (a_ylo T)); [| | exact Hylo | exact CFL].
    + intros f l kd r Hm. unfold uE. rewrite <- Hmaps, Hm in Hmv. cbn [AP.maps_vars_lt forallb am_base am_len] in Hmv.
      apply andb_prop in Hmv as [Hmv _]. apply andb_prop in Hmv as [Hf _].
      assert (Hag : env_agree 0 E E') by (split; [intros n Hn; (first [ (clear - CA CFL CK CP CR CT CU HU' Hn; lia) | lia ]) | reflexivity]).
      rewrite <- (edenot_agree' 0 E E' f Hag Hf). reflexivity.
    + unfold E'. rewrite <- GPS.sptop_den_tsubst, Hbrk. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ENT_tenv : forall {RC : run_ceil} PERMc SPTOPc FS0 FDS0 AINV (U U' : env -> Prop) (E : env) (h T : acs) (w : tbind) fx R M model,
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U E h fx R M model ->
  ENT h T w = true ->
  U' (tenv E (TH h T w)) ->
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U' (tenv E (TH h T w)) T fx R M model /\ pc T = pc h.
Proof.
  intros RC PERMc SPTOPc FS0 FDS0 AINV U U' E h T w fx R M model HC H HU'. unfold ENT in H. rewrite APC.entails_tw_eq in H.
  apply andb_prop in H as [_ H]. unfold TH. exact (entails_t_tenv PERMc SPTOPc FS0 FDS0 AINV U U' E h T _ fx R M model HC H HU').
Qed.

(* [comment removed for export] *)
Lemma cs_ok_uinv : forall {RC : run_ceil} PERMc SPTOPc FS0 FDS0 AINV (U U' : env -> Prop) E cs fx R M model,
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U E cs fx R M model -> (U E -> U' E) ->
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U' E cs fx R M model.
Proof. intros RC PERMc SPTOPc FS0 FDS0 AINV U U' E cs fx R M model HC HU. destruct HC; constructor; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FDS3 (p : Fs.path) (off : word) : list (word * FdEntry) := (Z_to_bv 64 3, State.FdFile p off) :: fds_std.
Lemma fds3_1 : forall p off, fd_lookup (FDS3 p off) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)). Proof. reflexivity. Qed.
Lemma fds3_2 : forall p off, fd_lookup (FDS3 p off) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
Lemma fds3_3 : forall p off, fd_lookup (FDS3 p off) (Z_to_bv 64 3) = Some (State.FdFile p off). Proof. reflexivity. Qed.
Lemma fds3_insert : forall p off off', fd_insert (FDS3 p off) (Z_to_bv 64 3) (State.FdFile p off') = FDS3 p off'. Proof. reflexivity. Qed.
Lemma fds3_remove : forall p off, fd_remove (FDS3 p off) (Z_to_bv 64 3) = fds_std. Proof. reflexivity. Qed.
Lemma fds_std_1' : fd_lookup fds_std (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)). Proof. reflexivity. Qed.
Lemma fds_std_2' : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wseg_ok_le : forall segs a n m, wseg_ok segs a n = true -> (m <= n)%nat -> wseg_ok segs a m = true.
Proof.
  intros segs a n. revert a. induction n as [|n IH]; intros a m H Hm.
  - replace m with 0%nat by lia. reflexivity.
  - destruct m as [|m]; [reflexivity|]. cbn [wseg_ok] in H |- *.
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|discriminate].
    apply andb_prop in H as [H1 H2]. rewrite H1. cbn [andb]. apply IH; [exact H2 | lia].
Qed.
Lemma wseg_ok_read_stage : wseg_ok RSEGS (Z_to_bv 64 READ_STAGE) (Z.to_nat 65536) = true.
Proof. apply StoreOk.WsegFast.wseg_fast_ok. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_file_node : forall ms model x8 p off data w,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 63 ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (State.FdFile p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  fs_lookup (m_fs model) p = Some data ->
  read_bytes_map (ms_writable_byte RSEGS ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some w ->
  bv_unsigned (ms_gpr ms 2) <= rw_bytes_max ->
  0 < bv_unsigned (ms_gpr ms 2) ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  node_ok RSEGS (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms
                 (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
                           (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) [])))
              (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                           (State.FdFile p (bv_add off (len_word (file_read data off (ms_gpr ms 2)))))) model)).
Proof.
  intros ms model x8 p off data w Hh Hlazy Hsvc Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok.
  set (bs := file_read data off (ms_gpr ms 2)).
  assert (HL : bv_unsigned (len_word (file_read data off (ms_gpr ms 2))) <= bv_unsigned (ms_gpr ms 2)).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat. rewrite Z.mod_small; lia. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input RSEGS ms x8) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
     /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (State.FdFile p (bv_add off (len_word bs)))) model
     /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 RSEGS ms x8 eff model Hno). unfold check_read.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    unfold bs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
    - cbv beta iota. rewrite check_ret_only_ok_iff. cbn [delivered_writes length]. tauto.
    - destruct eff as [ret ws zs us cs copyins]. split.
      + intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))%bool eqn:Hb;
          try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr]. apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes]. repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff. inversion Heff; subst.
        rewrite bv_eqb_refl. rewrite (proj2 (listN_eqb_eq _ _) eq_refl). rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
  apply (node_det RSEGS ms model x8 _ _ [] Hh Hsvc).
  - exact Hchk.
  - intros eff Hs'.
    rewrite (check_syscall_63 RSEGS ms x8 _ model Hno) in Hs'. unfold check_read in Hs'.
    rewrite Hfd32, Hfd in Hs'. cbv beta iota in Hs'.
    rewrite Haok in Hs'. cbn [negb] in Hs'. cbv beta iota in Hs'.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs'.
    rewrite Hfs in Hs'. cbv beta iota zeta in Hs'.
    rewrite in_wmem_si in Hs'.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs'. cbv beta iota in Hs'.
    revert Hs'. destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs'.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs').
    + destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate Hs'.
      destruct zs as [|? ?]; [|discriminate Hs']. destruct us as [|? ?]; [|discriminate Hs'].
      destruct cs as [|? ?]; [|discriminate Hs']. destruct copyins as [|? ?]; [|discriminate Hs'].
      revert Hs'. match goal with |- (if ?c then _ else _) = _ -> False => destruct c; intros Hs'; discriminate Hs' end.
  - cbn [m_halted with_fds]. exact Hh.
  - cbn [m_vm_lazy with_fds]. exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma close_node : forall ms model x8 e,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 57 ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some e ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  node_ok RSEGS (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model)).
Proof.
  intros ms model x8 e Hh Hlazy Hsvc Hno Hfd Hfd32.
  apply (node_ret_only RSEGS ms model x8 (Z_to_bv 64 0) _ [] Hh Hsvc).
  - intros eff. rewrite (check_syscall_57 RSEGS ms x8 eff model Hno). unfold check_close. rewrite Hfd32, Hfd. reflexivity.
  - cbn [m_halted with_fds]. exact Hh.
  - cbn [m_vm_lazy with_fds]. exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma store_ok_wseg : forall segs a n M, wseg_ok segs a n = true -> RiscvSemantics.store_ok segs M a n = true.
Proof.
  intros segs a n. revert a. induction n as [|n IH]; intros a M H; [reflexivity|].
  cbn [wseg_ok] in H. cbn [RiscvSemantics.store_ok]. unfold RiscvSemantics.wview at 1.
  destruct (M a) as [b|].
  - destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H0 H1]. apply IH. exact H2.
  - destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H0 H1]. rewrite H0.
    destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))); [|discriminate].
    apply IH. exact H2.
Qed.
Lemma RSW_ok : forall E M, kentry_ok RSEGS E M RSW.
Proof.
  intros E M. cbn [kentry_ok RSW]. unfold flat, elenZ. rewrite estart_lit0, edenot_lit, u64_lit by lia. unfold READ_STAGE.
  split; [lia|]. intros d m Hd Hdm.
  replace (Z_to_bv 64 (499737 + d)) with (bv_add (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 d))
    by (apply bv_eq; unfold READ_STAGE; rewrite bv_add_unsigned, !u64_lit by lia; rewrite bv_wrap64_mod, Z.mod_small by lia; reflexivity).
  apply store_ok_wseg.
  assert (W : wseg_ok RSEGS (bv_add (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 d)) (Z.to_nat 65536 - Z.to_nat d) = true).
  { assert (G : forall k a, Z.of_nat k <= 65536 -> wseg_ok RSEGS a k = true -> forall j, (j <= k)%nat -> wseg_ok RSEGS (bv_add a (Z_to_bv 64 (Z.of_nat j))) (k - j) = true).
    { intros k. induction k as [|k IH]; intros a Hk H j Hj.
      - replace j with 0%nat by lia. cbn. reflexivity.
      - destruct j as [|j].
        + replace (bv_add a (Z_to_bv 64 (Z.of_nat 0))) with a; [exact H|]. apply bv_eq. rewrite bv_add_unsigned, u64_lit by lia. rewrite Z.add_0_r, bv_wrap64_mod, Z.mod_small; [reflexivity | apply u64_range].
        + cbn [wseg_ok] in H. destruct (find_segment RSEGS (bv_unsigned a) 1) as [seg|]; [|discriminate].
          apply andb_prop in H as [H1 H2].
          replace (bv_add a (Z_to_bv 64 (Z.of_nat (S j)))) with (bv_add (bv_add a 1%bv) (Z_to_bv 64 (Z.of_nat j))).
          * replace (S k - S j)%nat with (k - j)%nat by lia. apply IH; [lia | exact H2 | lia].
          * apply bv_eq. rewrite !bv_add_unsigned, !u64_lit by lia. change (bv_unsigned (1%bv : word)) with 1.
            rewrite !bv_wrap64_mod, Zplus_mod_idemp_l. f_equal. lia. }
    rewrite <- (Z2Nat.id d) at 1 by lia. apply (G (Z.to_nat 65536)); [rewrite Z2Nat.id; lia | exact wseg_ok_read_stage | lia]. }
  eapply wseg_ok_le; [exact W | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section S2.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
(* [comment removed for export] *)
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GUBSAN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okR TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok U).

(* [comment removed for export] *)
Lemma AINVcS_vm : forall TOP M0 Lc B C M mdl mdl', AINVcS TOP M0 Lc B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINVcS TOP M0 Lc B C M mdl'.
Proof using. intros TOP M0. exact (AINV_f_vm SWIN_T GUBSAN AINV_R AINV_R_vm PERM_Tc TOP [] M0 0 0). Qed.

(* [comment removed for export] *)
Lemma RS_owned : forall TOP Lc (a : word), READ_STAGE <= bv_unsigned a < READ_STAGE + 65536 -> owned SWIN_T PERM_Tc TOP Lc a.
Proof using.
  intros TOP Lc a Ha. right. right. right. unfold in_wins, SWIN_T, RSTAGE_W.
  exists 0x7a019, 0x8a019. split; [| unfold READ_STAGE in Ha; lia].
  apply in_app_iff. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma xfer_ok : forall TOP FS0 FDS FDS' M0 (U : env -> Prop) E (T T' : acs) (rv : expr) (news rest : list kentry)
                       fx R M model (bs : list byte) (v : word),
  cs_okR TOP FS0 FDS M0 U E T fx R M model ->
  s_regs (a_ss T') = sr_upd (s_regs (a_ss T)) 10 rv -> s_log (a_ss T') = [] ->
  kn T' = news ++ RSW :: rest ->
  forallb (fun K => existsb (kentry_eqb K) (kn T)) rest = true ->
  kn_havoc rest (ELit 0) READ_STAGE (ELit 65536) = rest ->
  a_vis T' = a_vis T -> a_ghost T' = a_ghost T -> a_brk T' = a_brk T -> a_ylo T' = a_ylo T -> a_maps T' = a_maps T ->
  edenot E rv = v ->
  Z.of_nat (length bs) <= 65536 ->
  Forall (kentry_ok RSEGS E (write_to_mem M (Z_to_bv 64 READ_STAGE) bs)) news ->
  cs_okR TOP FS0 FDS' M0 U E T' fx (regupd R (Z_to_bv 5 10) v) (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds FDS' model).
Proof using.
  intros TOP FS0 FDS FDS' M0 U E T T' rv news rest fx R M model bs v HC Hregs Hlog Hkn Hsub Hhav Hvis Hgh Hbrk Hylo Hmaps Hrv Hbs Hnews.
  set (M' := write_to_mem M (Z_to_bv 64 READ_STAGE) bs).
  assert (HM' : forall x : word, bv_unsigned x < READ_STAGE \/ READ_STAGE + Z.of_nat (length bs) <= bv_unsigned x -> M' x = M x).
  { intros x Hx. unfold M'. rewrite write_to_mem_wbytes. apply wbytes_out; rewrite u64_lit by (unfold READ_STAGE; lia); unfold READ_STAGE in *; lia. }
  assert (HG : StoreOk.mem_grows M M') by (unfold M'; rewrite write_to_mem_wbytes; apply wbytes_grows).
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL].
  constructor.
  - rewrite Hregs. change (Z_to_bv 5 10) with (Z_to_bv 5 (Z.of_nat 10)). apply regs_ok_set_n; [exact CR | lia | exact Hrv].
  - exact Hlog.
  - rewrite Hkn. apply Forall_app. split; [exact Hnews|]. constructor; [apply RSW_ok|].
    rewrite <- Hhav. eapply know_ok_havoc; [| | exact HG].
    + apply Forall_forall. intros K HK. pose proof (proj1 (forallb_forall _ _) Hsub K HK) as HX.
      apply existsb_exists in HX as (K' & HK' & HKK). apply kentry_eqb_eq in HKK. subst K'.
      exact (proj1 (Forall_forall _ _) CK K HK').
    + intros x Hx. apply HM'. rewrite estart_lit0 in Hx. unfold elenZ in Hx. rewrite edenot_lit, u64_lit in Hx by lia. lia.
  - cbn [m_halted with_fds]. exact CH.
  - cbn [m_vm_lazy with_fds]. exact CZ.
  - cbn [m_fs with_fds]. exact CF.
  - reflexivity.
  - rewrite Hvis. apply (AINVcS_vm TOP M0 _ _ _ _ model); [|reflexivity].
    apply (AF_S TOP M0 _ _ _ M M' model CA). intros a Ha. split.
    + apply RS_owned. destruct (Z_lt_ge_dec (bv_unsigned a) READ_STAGE); [exfalso; apply Ha; apply HM'; lia|].
      destruct (Z_lt_ge_dec (bv_unsigned a) (READ_STAGE + Z.of_nat (length bs))); [lia | exfalso; apply Ha; apply HM'; lia].
    + intros Hn. apply Ha. destruct (M a) as [b|] eqn:HMa; [|exact Hn]. exfalso. exact (HG a ltac:(rewrite HMa; discriminate) Hn).
  - exact CU.
  - exact CX.
  - rewrite Hgh. exact CP.
  - rewrite Hbrk. exact CT.
  - cbn [m_vm_materialized with_fds]. exact CM.
  - rewrite Hmaps, Hbrk, Hylo. exact CFL.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Variables (p : Fs.path) (data : list byte).
Definition L : Z := Z.of_nat (length data).
(* [comment removed for export] *)
Definition LB : Z := Z.min L (2 ^ 40).
Definition hdr : list byte := firstn 3 data.
(* [comment removed for export] *)
Variables (TOP : Z) (M0 : word -> option byte).

(* [comment removed for export] *)
Definition RD (cap : Z) (fs : Fs.Fs) : TSet := t_body data fs.

(* [comment removed for export] *)
Definition U_rd (len cap : Z) (E : env) : Prop := uE E LEN = len /\ uE E CAP = cap /\ uE E FLEN = LB /\ eb E 7 = hdr.
Definition U_1 (E : env) : Prop := uE E FLEN = LB /\ eb E 7 = hdr.
Definition nthb (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition U_cl1 (E : env) : Prop := uE E LEN = L.
Definition U_cl3 (E : env) : Prop := uE E LEN = L /\ uE E B0 = nthb 0 /\ uE E B1 = nthb 1 /\ uE E B2 = nthb 2.

Lemma uE_agree : forall E E' i, env_agree NXD E E' -> (i < NXD)%nat -> uE E' (EVar i) = uE E (EVar i).
Proof using. intros E E' i [H _] Hi. unfold uE. cbn [edenot]. rewrite (H i Hi). reflexivity. Qed.
Lemma U_rd_agree : forall len cap E E', env_agree NXD E E' -> U_rd len cap E -> U_rd len cap E'.
Proof using.
  intros len cap E E' Hag (H1 & H2 & H3 & H4). unfold U_rd, LEN, CAP, FLEN.
  rewrite !(uE_agree E E') by (try exact Hag; unfold NXD; lia). rewrite <- (proj2 Hag). auto.
Qed.
Lemma U_1_agree : forall E E', env_agree NXD E E' -> U_1 E -> U_1 E'.
Proof using. intros E E' Hag (H1 & H2). unfold U_1, FLEN. rewrite !(uE_agree E E') by (try exact Hag; unfold NXD; lia). rewrite <- (proj2 Hag). auto. Qed.
Lemma U_cl1_agree : forall E E', env_agree NXD E E' -> U_cl1 E -> U_cl1 E'.
Proof using. intros E E' Hag H1. unfold U_cl1, LEN. rewrite !(uE_agree E E') by (try exact Hag; unfold NXD; lia). auto. Qed.
Lemma U_cl3_agree : forall E E', env_agree NXD E E' -> U_cl3 E -> U_cl3 E'.
Proof using. intros E E' Hag (H1 & H2 & H3 & H4). unfold U_cl3, LEN, B0, B1, B2. rewrite !(uE_agree E E') by (try exact Hag; unfold NXD; lia). auto. Qed.

(* [comment removed for export] *)
Definition FDSr (len : Z) : list (word * FdEntry) := FDS3 p (Z_to_bv 64 len).

(* [comment removed for export] *)
Lemma kn_In_ok : forall FS0 FDS U E cs fx R M model K,
  cs_okR TOP FS0 FDS M0 U E cs fx R M model -> In K (kn cs) -> kentry_ok RSEGS E M K.
Proof using. intros FS0 FDS U E cs fx R M model K HC HK. exact (proj1 (Forall_forall _ _) (co_know HC) K HK). Qed.
Lemma reg_lit_get : forall FS0 FDS U E cs fx R M model n z,
  cs_okR TOP FS0 FDS M0 U E cs fx R M model -> (0 < n < 32)%nat -> reg_lit cs n = Some z -> getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z.
Proof using. intros FS0 FDS U E cs fx R M model n z HC Hn Hl. exact (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model n z HC Hn Hl)). Qed.
Lemma reg_expr_get : forall FS0 FDS U E cs fx R M model n,
  cs_okR TOP FS0 FDS M0 U E cs fx R M model -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof using. intros FS0 FDS U E cs fx R M model n HC Hn. exact (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model n HC Hn). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd32_3 : fd32 (Z_to_bv 64 3) = Z_to_bv 64 3. Proof using. vm_compute. reflexivity. Qed.
Lemma rs_access_ok : forall c, 0 <= c <= 65536 -> access_okb (Z_to_bv 64 READ_STAGE) c = true.
Proof using. intros c Hc. unfold access_okb, TASK_SIZE, READ_STAGE. rewrite u64_lit by lia. apply andb_true_intro. split; apply Z.leb_le; lia. Qed.
Lemma rs_cnt_max : forall c, 0 <= c <= 65536 -> c <= rw_bytes_max.
Proof using. intros c Hc. unfold rw_bytes_max. lia. Qed.

(* [comment removed for export] *)
Lemma read_step : forall FS0 U E (T : acs) fx R M model (len cnt : Z) (X : TSet),
  cs_okR TOP FS0 (FDSr len) M0 U E T fx R M model ->
  is_ecall_at RSEGS T = true -> pc T = P_ECALL ->
  reg_lit T 17 = Some 63 -> reg_lit T 10 = Some 3 -> reg_lit T 11 = Some READ_STAGE ->
  bv_unsigned (getr R (Z_to_bv 5 12)) = cnt -> 0 < cnt <= 65536 ->
  fs_lookup FS0 p = Some data -> 0 <= len -> len + 65536 < 2 ^ 64 ->
  (let bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt) in
   RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) (len_word bs)) P_AFTER_ECALL (write_to_mem M (Z_to_bv 64 READ_STAGE) bs)
            (with_fds (FDSr (len + Z.of_nat (length bs))) model)) X) ->
  RZ (cfgF RSEGS fx R (pc T) M model) X.
Proof using.
  intros FS0 U E T fx R M model len cnt X HC Hec Hpc H17 H10 H11 Hcnt Hcr Hfs Hlen Hlen64 HK.
  cbv zeta in HK.
  destruct (GPS.is_ecall_at_sound RSEGS T Hec) as (w & HF & HE & Hpc0 & Hpc4).
  pose proof (reg_lit_get FS0 _ U E T fx R M model 17 63 HC ltac:(lia) H17) as G17.
  pose proof (reg_lit_get FS0 _ U E T fx R M model 10 3 HC ltac:(lia) H10) as G10.
  pose proof (reg_lit_get FS0 _ U E T fx R M model 11 READ_STAGE HC ltac:(lia) H11) as G11.
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 12 = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in Hcnt.
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc T)) M (seg_rom RSEGS) (getr R 17)) with (@epend fx R (Z_to_bv 64 (pc T)) M (seg_rom RSEGS) (getr R 17)).
  assert (Hcw : word_to_nat (getr R 12) = Z.to_nat cnt) by (unfold word_to_nat; rewrite Hcnt; reflexivity).
  destruct (wseg_ok_wdef RSEGS (Z_to_bv 64 READ_STAGE) (getr R 12) (@epend fx R (Z_to_bv 64 (pc T)) M (seg_rom RSEGS) (getr R 17))
              ltac:(rewrite Hcw; eapply wseg_ok_le; [exact wseg_ok_read_stage | lia])) as [wm Hwm].
  eapply (sr_silent1 RSEGS SR).
  { eapply (read_file_node (@epend fx R (Z_to_bv 64 (pc T)) M (seg_rom RSEGS) (getr R 17)) model (getr R 17) p (Z_to_bv 64 len) data wm (co_halt HC) (co_lazy HC) (epend_svc _ _ _ _ _)).
    - rewrite G17. apply u64_lit. lia.
    - rewrite ms_gpr_epend0, G10, (co_fds HC). apply fds3_3.
    - rewrite ms_gpr_epend0, G10. apply fd32_3.
    - rewrite (co_fs HC). exact Hfs.
    - rewrite ms_gpr_epend1, ms_gpr_epend2, G11. exact Hwm.
    - rewrite ms_gpr_epend2. apply rs_cnt_max. lia.
    - rewrite ms_gpr_epend2. lia.
    - rewrite ms_gpr_epend1, ms_gpr_epend2, G11. apply rs_access_ok. lia. }
  cbv beta.
  rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, G10, G11.
  replace (getr R 12) with (Z_to_bv 64 cnt) by (apply bv_eq; rewrite u64_lit by lia; symmetry; exact Hcnt).
  unfold epend. rewrite (@adv_apply_delivered fx). rewrite v_addi_pc4 by (unfold two64; lia). rewrite Hpc.
  rewrite (co_fds HC). unfold FDSr. rewrite fds3_insert.
  match goal with |- RZ (mkCfg ?ms (with_fds (FDS3 p ?o) model)) X =>
    replace o with (Z_to_bv 64 (len + Z.of_nat (length (file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt))))) end.
  - exact HK.
  - apply bv_eq. unfold len_word. rewrite bv_add_unsigned, !u64_lit; rewrite ?bv_wrap64_mod, ?length_file_read; try lia.
    all: pose proof (Nat.le_min_l (word_to_nat (Z_to_bv 64 cnt)) (length data - word_to_nat (Z_to_bv 64 len))) as Hm;
         unfold word_to_nat in Hm |- *; rewrite ?u64_lit in Hm |- * by lia; try lia.
    rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma close_step : forall FS0 U E (T : acs) fx R M model (len : Z) (X : TSet),
  cs_okR TOP FS0 (FDSr len) M0 U E T fx R M model ->
  is_ecall_at RSEGS T = true -> pc T = P_ECALL ->
  reg_lit T 17 = Some 57 -> reg_lit T 10 = Some 3 ->
  RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 0)) P_AFTER_ECALL M (with_fds fds_std model)) X ->
  RZ (cfgF RSEGS fx R (pc T) M model) X.
Proof using.
  intros FS0 U E T fx R M model len X HC Hec Hpc H17 H10 HK.
  destruct (GPS.is_ecall_at_sound RSEGS T Hec) as (w & HF & HE & Hpc0 & Hpc4).
  pose proof (reg_lit_get FS0 _ U E T fx R M model 17 57 HC ltac:(lia) H17) as G17.
  pose proof (reg_lit_get FS0 _ U E T fx R M model 10 3 HC ltac:(lia) H10) as G10.
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10.
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc T)) M (seg_rom RSEGS) (getr R 17)) with (@epend fx R (Z_to_bv 64 (pc T)) M (seg_rom RSEGS) (getr R 17)).
  eapply (sr_silent1 RSEGS SR).
  { eapply (close_node (@epend fx R (Z_to_bv 64 (pc T)) M (seg_rom RSEGS) (getr R 17)) model (getr R 17) (State.FdFile p (Z_to_bv 64 len)) (co_halt HC) (co_lazy HC) (epend_svc _ _ _ _ _)).
    - rewrite G17. apply u64_lit. lia.
    - rewrite ms_gpr_epend0, G10, (co_fds HC). apply fds3_3.
    - rewrite ms_gpr_epend0, G10. apply fd32_3. }
  cbv beta. rewrite ms_gpr_epend0, G10, (co_fds HC). unfold FDSr. rewrite fds3_remove.
  rewrite adv_set_epend. rewrite v_addi_pc4 by (unfold two64; lia). rewrite Hpc. exact HK.
Qed.
End S2.
