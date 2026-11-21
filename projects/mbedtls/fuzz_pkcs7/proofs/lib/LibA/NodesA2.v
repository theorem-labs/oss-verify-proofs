(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (copy_iovecs_accesses_in restated for per-descriptor records of 16 or 8 bytes; the sys_rob premise on rz_ret_only_copyinsK_silent_chk and rz_openK, discharged at the writev and openat nodes with a new lemma open_robA; the channel-reader premise on the writev lemmas; path_atA, cstr_access_len_of_rdn and rz_openat_toolongA bound the path below TASK_SIZE; the changed encoded statements decoded to plain text; imports of RomBase, RomWrite and RomWritev). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.   (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb RelSpec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeX StoreOk AgentLib Hoare.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes AgentNodes SysNodes NodesDir LibWritev.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA NodesA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require RomBase.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require RomWrite RomWritev.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_NodesA2 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.copy_iovecs_accesses"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Logic.ex"; "Corelib.Init.Peano.lt"; "stdpp.bitvector.definitions.bv_add"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.iov_prefix_accesses"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.LibA.ALazy.aok_addr"; "OSSVerify.KrLib.LibA.ALazy.acc_ok"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "WithSegs.matK"; "LinuxProcessSemantics.LinuxProcessSem.State.import_iovecs_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_ret_only_copyins"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.LibA.NodesA.vm_same"; "OSSVerify.KrLib.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE"; "OSSVerify.KrLib.Sys.LibWritev.iov_array"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "OSSVerify.KrLib.Sys.LibWritev.iov_bufs_ok"; "OSSVerify.KrLib.Sys.LibWritev.iov_bufs"; "Stdlib.Lists.List.concat"; "LinuxProcessSemantics.LinuxProcessSem.State.iovs_total"; "OSSVerify.KrLib.Lib.Shape.t_alt"; "OSSVerify.KrLib.BB.ShapeX.wr_index"; "OSSVerify.KrLib.Lib.Shape.t_emit"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Specif.proj1_sig"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.Lib.PropExec.rdn"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "OSSVerify.KrLib.Lib.PropExec.regupd"; "OSSVerify.KrLib.Lib.PropExec.v_addi"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.S"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.BB.FileSim.mrb"; "Corelib.Init.Nat.add"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.State.cstr_access_len_aux"; "LinuxProcessSemantics.LinuxProcessSem.Monad.outcome"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_spec"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.AT_FDCWD32"; "WithSegs.Openat.path_atA"; "OSSVerify.KrLib.BB.FileSim.open_copyins"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.ENAMETOOLONG"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOENT"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.dot_path"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei.path_has_slash"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.Fs.path_eqb"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei.dotdot_path"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.BB.RelSpec.open_out"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_errnos"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_fd"; "OSSVerify.KrLib.Lib.Shape.t_alt2"; "LinuxProcessSemantics.LinuxProcessSem.State.with_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_insert"; "LinuxProcessSemantics.LinuxProcessSem.State.FdDir"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFile"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* LPS revision: [copy_iovecs_accesses] records [iovec_entry_accesses mp a] per descriptor
   (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/State.v:1713-1738): the 16
   bytes when both fields read, only the length field [(a + 8, 8)] when the base faults.  The old
   statement (n = 16 always) is false there; each recorded range is still inside its descriptor. *)
Lemma copy_iovecs_accesses_in : forall (mp : word -> option byte) (k : nat) (a x : word) (n : nat),
  In (x, n) (copy_iovecs_accesses mp a k) ->
  exists i, (i < k)%nat /\
    ((n = 16%nat /\ x = bv_add a (Z_to_bv 64 (16 * Z.of_nat i)))
     \/ (n = 8%nat /\ x = bv_add a (Z_to_bv 64 (16 * Z.of_nat i + 8)))).
Proof.
  intros mp k. induction k as [|k IH]; intros a x n Hin; cbn [copy_iovecs_accesses] in Hin.
  - destruct Hin.
  - apply in_app_or in Hin as [Hin | Hin].
    + unfold iovec_entry_accesses in Hin.
      destruct (read_u64 mp (a + 8)); [|destruct Hin].
      destruct (read_u64 mp a); destruct Hin as [E | []]; injection E as <- <-;
        exists 0%nat; (split; [lia|]).
      * left. split; [reflexivity|].
        apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. cbn [Z.of_nat Z.mul]. change (bv_wrap 64 0) with 0%Z.
        rewrite Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
      * right. split; [reflexivity|].
        apply bv_eq. rewrite !bv_add_unsigned, Z_to_bv_unsigned. f_equal.
    + destruct (read_iovec_entry mp a) as [? len| |]; [|destruct Hin|destruct Hin].
      destruct (IH _ _ _ Hin) as (i & Hi & [[-> ->] | [-> ->]]);
        exists (S i); (split; [lia|]); [left | right]; (split; [reflexivity|]);
        apply bv_eq;
        rewrite !bv_add_unsigned, !Z_to_bv_unsigned; change (bv_unsigned (16 : word)) with 16%Z;
        unfold bv_wrap; rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_r, Zplus_mod_idemp_l;
        f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma iov_prefix_accesses_in : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Piovs,(?.(4.(0.&40.)(0.&40.)))Pleft,$2.Px,(0.&40.)Pn,$2.P,(3.(4.(0.&40.)$2.)(5.(0.&40.)$2.R2.R1.)(10.R4.R3.))(9.(0.&40.)Llen,(0.&40.)(7.(3.(4.(0.&40.)(0.&40.))(5.(0.&40.)(0.&40.)R4.R1.)R6.)(11.R3.(12.R1.))))")
(* [comment removed for export] *).
Proof.
  induction iovs as [|[base len] rest IH]; intros left x n Hin.
  - destruct left; cbn in Hin; destruct Hin.
  - destruct left as [|l]; cbn [iov_prefix_accesses] in Hin; [destruct Hin|].
    rewrite word_to_nat_bounded_eq_min in Hin.   (* [comment removed for export] *)
    destruct (Nat.eqb (Nat.min (word_to_nat len) (S l)) 0) eqn:E.
    + destruct (IH _ _ _ Hin) as (len' & Hin' & Hle). exists len'. split; [right; exact Hin'|exact Hle].
    + destruct Hin as [E2 | Hin].
      * injection E2 as <- <-. exists len. split; [left; reflexivity|]. lia.
      * destruct (IH _ _ _ Hin) as (len' & Hin' & Hle). exists len'. split; [right; exact Hin'|exact Hle].
Qed.

Section WithLayout.
Variable AL : asan_layout.
Variable CS : Z -> Prop.

#[using="Type"] Lemma acc_ok_app : forall l1 l2, acc_ok AL CS l1 -> acc_ok AL CS l2 -> acc_ok AL CS (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2 z (a & n & Hin & Hz). apply in_app_or in Hin as [Hin|Hin]; [apply H1 | apply H2]; exists a, n; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma acc_ok_copy_iovecs : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pmp,P,(0.&40.)(1.(0.&8.))Piov,(0.&40.)Pcnt,$2.P,(13.(14.(15.&40.R2.)(=.+10.(>.R1.)))(16.+2.+40.))P,Pz,$17.P,(7.(13.(15.&40.R4.)R1.)(18.R1.(14.(15.&40.R4.)(=.+10.(>.R3.)))))(19.VAL,VCS,R2.)(1:.VAL,VCS,(6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros mp iov cnt Hnw H z (a & n & Hin & Hz).
  destruct (copy_iovecs_accesses_in _ _ _ _ _ Hin) as (i & Hi & [[-> ->] | [-> ->]]);
  pose proof (bv_unsigned_in_range 64 iov) as R; unfold bv_modulus in R;
  rewrite bv_add_unsigned, Z_to_bv_unsigned in Hz; unfold bv_wrap in Hz;
  (assert (Hi16 : (0 <= 16 * Z.of_nat i /\ 16 * Z.of_nat i + 16 <= 16 * Z.of_nat cnt)%Z) by lia);
  unfold bv_modulus in Hz;
  rewrite Zplus_mod_idemp_r, Z.mod_small in Hz by (cbn in Hnw, R |- *; lia);
  apply H; cbn [Z.of_nat] in Hz; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma acc_ok_iov_prefix : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Piovs,(?.(4.(0.&40.)(0.&40.)))Pleft,$2.P,(1;.(4.(0.&40.)(0.&40.))Lbl,(4.(0.&40.)(0.&40.))Pz,$17.P,(7.(13.(15.&40.(1<.(0.&40.)(0.&40.)R2.))R1.)(18.R1.(14.(15.&40.(1<.(0.&40.)(0.&40.)R2.))(15.&40.(1=.(0.&40.)(0.&40.)R2.)))))(19.VAL,VCS,R2.)R2.)(1:.VAL,VCS,(10.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros iovs left H z (a & n & Hin & Hz).
  destruct (iov_prefix_accesses_in _ _ _ _ Hin) as (len & Hin' & Hle).
  apply Forall_forall with (x := (a, len)) in H; [|exact Hin']. apply H. cbn.
  unfold word_to_nat in Hle. pose proof (bv_unsigned_in_range 64 len). lia.
Qed.
End WithLayout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Variable AL : asan_layout.
Variable CS : Z -> Prop.
Variable K : Model -> Prop.
Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pmo,$1>.Pacc,(?.(4.(0.&40.)$2.))P,A1.VK,R2.P,(1:.VAL,VCS,R2.)(9.$1>.Lmo',$1>.(7.(8.(1.$1>.)(1?.R5.R4.)(20.$1>.R1.))(7.A1.VK,R1.(21.R5.R1.))))")
(* [comment removed for export] *).
Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pmo,$1>.Pmo',$1>.P,A1.VK,R2.P,(8.$22.(23.R2.)(23.R3.))P,(8.(?.(4.(0.&40.)(0.&40.)))(24.R3.)(24.R4.))P,(8.(?.(0.&40.))(25.R4.)(25.R5.))P,(8.(1.(0.&40.))(26.R5.)(26.R6.))A1.VK,R6.")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition matK (mo : Model) (acc : list (word * nat)) : Model :=
  match materialize_model_accesses mo acc with Some m => m | None => mo end.

#[using="K_mat"] Lemma matK_spec : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pmo,$1>.Pacc,(?.(4.(0.&40.)$2.))P,A1.VK,R2.P,(1:.VAL,VCS,R2.)(7.(8.(1.$1>.)(1?.R4.R3.)(20.$1>.(27.R4.R3.)))(7.A1.VK,(27.R4.R3.)(21.R4.(27.R4.R3.))))")
(* [comment removed for export] *).
Proof.
  intros mo acc HK OK. destruct (K_mat mo acc HK OK) as (mo' & Hm & HK' & MM).
  unfold matK. rewrite Hm. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma import_iovecs_accesses_incl : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pmp,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,(0.&40.)Px,(0.&40.)Pk,$2.P,(3.(4.(0.&40.)$2.)(5.(0.&40.)$2.R2.R1.)(28.R5.R4.R3.))(3.(4.(0.&40.)$2.)(5.(0.&40.)$2.R3.R2.)(6.R6.R5.(12.R4.)))")
(* [comment removed for export] *).
Proof.
  intros mp a n x k H. unfold import_iovecs_accesses in H.
  destruct (bv_eqb n (Z_to_bv 64 1)) eqn:E1.
  - unfold bv_eqb in E1. apply Z.eqb_eq in E1. rewrite u64_lit in E1 by lia.
    assert (Hn : word_to_nat n = 1%nat) by (unfold word_to_nat; rewrite E1; reflexivity).
    (* LPS revision: a one-entry import records [iovec_entry_accesses mp a] (State.v:1823-1830) *)
    rewrite Hn. cbn [copy_iovecs_accesses]. destruct (negb (access_okb a 16)); [destruct H|].
    apply in_or_app. left. exact H.
  - destruct (bv_eqb n (Z_to_bv 64 0)); [destruct H|]. destruct (IOV_MAX <? bv_unsigned n)%Z; [destruct H|].
    destruct (negb _); [destruct H|]. exact H.
Qed.

#[using="Type"] Lemma acc_ok_import_iovecs : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pmp,P,(0.&40.)(1.(0.&8.))Piov,(0.&40.)Pcnt,$2.P,(13.(14.(15.&40.R2.)(=.+10.(>.R1.)))(16.+2.+40.))P,Pz,$17.P,(7.(13.(15.&40.R4.)R1.)(18.R1.(14.(15.&40.R4.)(=.+10.(>.R3.)))))(19.VAL,VCS,R2.)(1:.VAL,VCS,(28.R5.R4.(<.&40.(>.R3.))))")
(* [comment removed for export] *).
Proof.
  intros mp iov cnt Hnw H z (a & n & Hin & Hz).
  apply import_iovecs_accesses_incl in Hin. pose proof (u64_range iov).
  rewrite word_to_nat_Z, Nat2Z.id in Hin by lia.
  apply (acc_ok_copy_iovecs AL CS mp iov cnt Hnw H). exists a, n. auto.
Qed.

(* [comment removed for export] *)
(* Was an encoded statement (CDefT.buildp); written out from its decode (cdeft_print.py), not
   re-encoded, with one premise added, [RomBase.sys_rob segs (mkCfg ms mo)], for the node
   [NodesA.rz_ret_only_copyinsK_silent] builds (LPS revision, run_segments). *)
#[using="K_halted K_mat K_vmonly"] Lemma rz_ret_only_copyinsK_silent_chk : forall (ms : machine_state) (mo : Model)
    (x8 : bv 64) (reads : list (bv 64 * nat)) (r : bv 64) (m' : Model) (T : TSet),
  K mo ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = check_ret_only_copyins reads eff r m' []) ->
  vm_same mo m' ->
  acc_ok AL CS reads ->
  RomBase.sys_rob segs (mkCfg ms mo) ->
  (forall mo'', K mo'' -> mo_mat m' mo'' -> srealizesJ segs (mkCfg (advance_past_svc (set_gpr0 ms r)) mo'') T) ->
  srealizesJ segs (mkCfg ms mo) T.
Proof.
  intros ms mo x8 reads r m' T HK Hsvc Hchk VS OK Hrob Hc.
  apply (rz_ret_only_copyinsK_silent segs AL CS K K_halted K_mat K_vmonly ms mo x8 reads r m' T HK Hsvc);
    [| exact VS | exact OK | exact Hrob | exact Hc].
  intros o. destruct o as [eff m'' evs|]; split.
  - intros Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs as (-> & -> & ->). reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->). apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_refl.
  - intros Hs. exfalso. apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs. exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
  - intros H. exfalso. exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat"] Lemma rz_writev_pendingA : 
  (* plain text: the revision's writev needs the channel reader *)
  (forall ms : @LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state, (forall x8 : (@stdpp.bitvector.definitions.bv 64%N), (forall mo : @LinuxProcessSemantics.LinuxProcessSem.State.Model, (forall fd : @Corelib.Numbers.BinNums.Z, (forall iov : (@stdpp.bitvector.definitions.bv 64%N), (forall iovs : (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N))), (forall bss : (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))), (forall T : (@Corelib.Init.Datatypes.nat -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.TSet), ((@Corelib.Init.Logic.eq ((@stdpp.bitvector.definitions.bv 64%N) -> (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom ms) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) -> ((K mo) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 64%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending ms) (@Corelib.Init.Datatypes.Some (@stdpp.bitvector.definitions.bv 64%N) x8)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds mo) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)))) -> ((@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader mo = true) -> ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt 0%Z fd) (@Stdlib.ZArith.BinInt.Z.lt fd (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z))) -> ((@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned 64%N x8) 66%Z) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr ms 0%nat) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr ms 1%nat) iov) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr ms 2%nat) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)) iovs)))) -> ((@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat (@Corelib.Init.Datatypes.length (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)) iovs)) (@Corelib.Init.Peano.le (@Corelib.Init.Datatypes.length (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)) iovs) 1024%nat)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) (@Stdlib.ZArith.BinInt.Z.mul 16%Z (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)) iovs)))) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys.LibWritev.iov_array segs (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem ms) iov iovs) -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys.LibWritev.iov_bufs_ok iovs) -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys.LibWritev.iov_bufs segs (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem ms) iovs bss) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) (@Stdlib.ZArith.BinInt.Z.mul 16%Z (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)) iovs)))))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((@Corelib.Lists.ListDef.Forall (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)) (fun bl : (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)) => (forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N (@Corelib.Init.Datatypes.fst (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N) bl)) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N (@Corelib.Init.Datatypes.fst (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N) bl)) (@stdpp.bitvector.definitions.bv_unsigned 64%N (@Corelib.Init.Datatypes.snd (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N) bl))))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z)))) iovs) -> (let bs : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) := (@Stdlib.Lists.List.concat (@stdpp.bitvector.definitions.bv 8%N) bss) in ((@Stdlib.ZArith.BinInt.Z.le 1%Z (@LinuxProcessSemantics.LinuxProcessSem.State.iovs_total iovs)) -> ((@Stdlib.ZArith.BinInt.Z.le (@LinuxProcessSemantics.LinuxProcessSem.State.iovs_total iovs) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 30%Z)) -> ((forall k : @Corelib.Init.Datatypes.nat, ((@Corelib.Init.Peano.le 1%nat k) -> ((@Corelib.Init.Peano.le k (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) bs)) -> (forall mo'' : @LinuxProcessSemantics.LinuxProcessSem.State.Model, ((K mo'') -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.mo_mat mo mo'') -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0 ms (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.of_nat k)))) mo'') (T k)))))))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg ms mo) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_alt (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.ShapeX.wr_index bs) (fun i : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.ShapeX.wr_index bs) => (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Lists.ListDef.firstn (@stdpp.bitvector.definitions.bv 8%N) (@Corelib.Init.Specif.proj1_sig (@Corelib.Init.Datatypes.nat) (fun n : @Corelib.Init.Datatypes.nat => (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat n) (@Corelib.Init.Peano.le n (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) bs)))) i) bs)) (T (@Corelib.Init.Specif.proj1_sig (@Corelib.Init.Datatypes.nat) (fun n : @Corelib.Init.Datatypes.nat => (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat n) (@Corelib.Init.Peano.le n (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) bs)))) i)))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
Proof.
  intros ms x8 mo fd iov iovs bss T Hrom HK Hsvc Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs AOKiov AOKbufs bs Ht1 Ht30 Hk.
  pose proof (K_halted mo HK) as Hh.
  destruct (writev_check segs ms x8 mo fd iov iovs bss Hrom Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  pose (accs := fun i : wr_index bs => CA ++ iov_prefix_accesses iovs (proj1_sig i)).
  assert (Eacc : forall i, syscall_effect_accesses (effs i) = accs i).
  { intros i. unfold effs, accs, syscall_effect_accesses. cbn. apply app_nil_r. }
  assert (OKi : forall i, acc_ok AL CS (accs i)).
  { intros i. unfold accs. apply acc_ok_app; [| apply acc_ok_iov_prefix; assumption].
    unfold CA. apply acc_ok_import_iovecs; [unfold TASK_SIZE in Hiok; lia | assumption]. }
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) (matK mo (accs i))
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (matK mo (accs i))).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (srzJ_node segs (mkCfg ms mo) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) (matK mo (accs i)))
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig].
      destruct (matK_spec mo (accs (exist _ k (conj Hk1 Hk2))) HK (OKi _)) as (_ & HK' & MM).
      apply Hk; assumption. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff mo = CheckOk m' ev ->
            exists i : wr_index bs, eff = effs i /\ m' = mo /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
  { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate].
    destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
      [|discriminate].
    destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
      [|discriminate].
    injection Hc as <- <-.
    apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
    assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
    exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
  assert (Hnode : node_ok segs (mkCfg ms mo) (wr_index bs)
                    (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (matK mo (accs i)))).
  { split; [|split].
    - intros i. apply (sstep_of_spec_mat segs ms mo x8 (effs i) mo (matK mo (accs i)));
        [exact Hh | exact Hsvc | | exact Hh | rewrite Eacc; exact (proj1 (matK_spec mo (accs i) HK (OKi i)))].
      apply check_syscall_ok_iff.
      destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
      rewrite (Hku k Hk2), Nat2Z.id.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
      replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
        by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
      rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
    - intros e st Hss.
      destruct (sstep_svc_inv_chk segs ms mo x8 e st Hsvc Hss)
        as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
           | (eff & Hc & -> & ->)].
      + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
        rewrite Eacc, (proj1 (matK_spec mo (accs i) HK (OKi i))) in Hmat. injection Hmat as <-.
        exists i. split; reflexivity.
      + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
        rewrite Eacc, (proj1 (matK_spec mo (accs i) HK (OKi i))) in Hmat. discriminate.
      + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
      + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
        destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
    - exact (writev_rob segs ms x8 mo fd iov iovs bss Hrom Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Ht30). }
  destruct Hnode as [Hn1 [Hn2 Hn3]]. split; [|split].
  - intros i. rewrite Enx. apply Hn1.
  - intros e st Hss. destruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
  - exact Hn3.
Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat"] Lemma rz_writev2A : 
  (* plain text: the revision's writev needs the channel reader *)
  (forall regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall pc : (@stdpp.bitvector.definitions.bv 64%N), (forall mem : ((@stdpp.bitvector.definitions.bv 64%N) -> (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall mo : @LinuxProcessSemantics.LinuxProcessSem.State.Model, (forall w : (@stdpp.bitvector.definitions.bv 32%N), (forall fd : @Corelib.Numbers.BinNums.Z, (forall iov : (@stdpp.bitvector.definitions.bv 64%N), (forall b1 : (@stdpp.bitvector.definitions.bv 64%N), (forall n1 : (@stdpp.bitvector.definitions.bv 64%N), (forall b2 : (@stdpp.bitvector.definitions.bv 64%N), (forall n2 : (@stdpp.bitvector.definitions.bv 64%N), (forall bs1 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall bs2 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall T : (@Corelib.Init.Datatypes.nat -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.TSet), ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 32%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word segs pc) (@Corelib.Init.Datatypes.Some (@stdpp.bitvector.definitions.bv 32%N) w)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall w) (@Corelib.Init.Datatypes.true)) -> ((K mo) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds mo) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)))) -> ((@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader mo = true) -> ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt 0%Z fd) (@Stdlib.ZArith.BinInt.Z.lt fd (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z))) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 17%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 66%Z)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 11%Z (@Corelib.Init.Logic.I))) iov) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 12%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 2%Z)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem iov 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 8%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat n1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 16%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b2))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 24%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat n2))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem b1 (@LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat n1)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) bs1)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem b2 (@LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat n2)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) bs2)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 32%Z) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b2) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2)) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le 1%Z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N n1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2))) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N n1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2)) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 30%Z)) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 32%Z))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N b2) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b2) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2)))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall k : @Corelib.Init.Datatypes.nat, ((@Corelib.Init.Peano.le 1%nat k) -> ((@Corelib.Init.Peano.le k (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2))) -> (forall mo'' : @LinuxProcessSemantics.LinuxProcessSem.State.Model, ((K mo'') -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.mo_mat mo mo'') -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.regupd regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I)) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.of_nat k))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.v_addi pc 4%Z) mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo'') (T k)))))))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) regs pc mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_alt (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.ShapeX.wr_index (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2)) (fun i : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.ShapeX.wr_index (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2)) => (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Lists.ListDef.firstn (@stdpp.bitvector.definitions.bv 8%N) (@Corelib.Init.Specif.proj1_sig (@Corelib.Init.Datatypes.nat) (fun n : @Corelib.Init.Datatypes.nat => (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat n) (@Corelib.Init.Peano.le n (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2))))) i) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2))) (T (@Corelib.Init.Specif.proj1_sig (@Corelib.Init.Datatypes.nat) (fun n : @Corelib.Init.Datatypes.nat => (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat n) (@Corelib.Init.Peano.le n (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2))))) i)))))))))))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE HK Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 AOKiov AOK1 AOK2 Hk.
  pose proof (K_halted mo HK) as Hh.
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pendingA (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) mo fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact HK | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros z Hz. apply AOKiov. change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z in Hz. lia.
  - constructor; [|constructor; [|constructor]]; cbn; assumption.
  - intros k Hk1 Hk2 mo'' HK'' MM. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat"] Lemma rz_writev1A : 
  (* plain text: the revision's writev needs the channel reader *)
  (forall regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall pc : (@stdpp.bitvector.definitions.bv 64%N), (forall mem : ((@stdpp.bitvector.definitions.bv 64%N) -> (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall mo : @LinuxProcessSemantics.LinuxProcessSem.State.Model, (forall w : (@stdpp.bitvector.definitions.bv 32%N), (forall fd : @Corelib.Numbers.BinNums.Z, (forall iov : (@stdpp.bitvector.definitions.bv 64%N), (forall b1 : (@stdpp.bitvector.definitions.bv 64%N), (forall n1 : (@stdpp.bitvector.definitions.bv 64%N), (forall bs1 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall T : (@Corelib.Init.Datatypes.nat -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.TSet), ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 32%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word segs pc) (@Corelib.Init.Datatypes.Some (@stdpp.bitvector.definitions.bv 32%N) w)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall w) (@Corelib.Init.Datatypes.true)) -> ((K mo) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds mo) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)))) -> ((@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader mo = true) -> ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt 0%Z fd) (@Stdlib.ZArith.BinInt.Z.lt fd (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z))) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 17%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 66%Z)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 11%Z (@Corelib.Init.Logic.I))) iov) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 12%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 1%Z)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem iov 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 8%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat n1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem b1 (@LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat n1)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) bs1)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 16%Z) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le 1%Z (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)) -> ((@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N n1) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 30%Z)) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 16%Z))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall k : @Corelib.Init.Datatypes.nat, ((@Corelib.Init.Peano.le 1%nat k) -> ((@Corelib.Init.Peano.le k (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) bs1)) -> (forall mo'' : @LinuxProcessSemantics.LinuxProcessSem.State.Model, ((K mo'') -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.mo_mat mo mo'') -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.regupd regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I)) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.of_nat k))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.v_addi pc 4%Z) mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo'') (T k)))))))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) regs pc mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_alt (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.ShapeX.wr_index bs1) (fun i : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.ShapeX.wr_index bs1) => (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Lists.ListDef.firstn (@stdpp.bitvector.definitions.bv 8%N) (@Corelib.Init.Specif.proj1_sig (@Corelib.Init.Datatypes.nat) (fun n : @Corelib.Init.Datatypes.nat => (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat n) (@Corelib.Init.Peano.le n (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) bs1)))) i) bs1)) (T (@Corelib.Init.Specif.proj1_sig (@Corelib.Init.Datatypes.nat) (fun n : @Corelib.Init.Datatypes.nat => (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat n) (@Corelib.Init.Peano.le n (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) bs1)))) i)))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd iov b1 n1 bs1 T HF HE HK Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 AOKiov AOK1 Hk.
  pose proof (K_halted mo HK) as Hh.
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pendingA (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) mo fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact HK | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros z Hz. apply AOKiov. change (Z.of_nat (length [(b1, n1)])) with 1%Z in Hz. lia.
  - constructor; [|constructor]; cbn; assumption.
  - intros k Hk1 Hk2 mo'' HK'' MM. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat"] Lemma rz_writev2_wallA : 
  (* plain text: the revision's writev needs the channel reader *)
  (forall regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall pc : (@stdpp.bitvector.definitions.bv 64%N), (forall mem : ((@stdpp.bitvector.definitions.bv 64%N) -> (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall mo : @LinuxProcessSemantics.LinuxProcessSem.State.Model, (forall w : (@stdpp.bitvector.definitions.bv 32%N), (forall fd : @Corelib.Numbers.BinNums.Z, (forall iov : (@stdpp.bitvector.definitions.bv 64%N), (forall b1 : (@stdpp.bitvector.definitions.bv 64%N), (forall n1 : (@stdpp.bitvector.definitions.bv 64%N), (forall b2 : (@stdpp.bitvector.definitions.bv 64%N), (forall n2 : (@stdpp.bitvector.definitions.bv 64%N), (forall bs1 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall bs2 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall KK : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.TSet, ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 32%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word segs pc) (@Corelib.Init.Datatypes.Some (@stdpp.bitvector.definitions.bv 32%N) w)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall w) (@Corelib.Init.Datatypes.true)) -> ((K mo) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds mo) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)))) -> ((@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader mo = true) -> ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt 0%Z fd) (@Stdlib.ZArith.BinInt.Z.lt fd (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z))) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 17%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 66%Z)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 11%Z (@Corelib.Init.Logic.I))) iov) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 12%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 2%Z)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem iov 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 8%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat n1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 16%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b2))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 24%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat n2))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem b1 (@LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat n1)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) bs1)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem b2 (@LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat n2)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) bs2)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 32%Z) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b2) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2)) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le 1%Z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N n1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2))) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N n1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2)) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 30%Z)) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 32%Z))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N b2) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b2) (@stdpp.bitvector.definitions.bv_unsigned 64%N n2)))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((KK (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event))) -> ((forall k : @Corelib.Init.Datatypes.nat, ((@Corelib.Init.Peano.le 1%nat k) -> ((@Corelib.Init.Peano.le k (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2))) -> (forall mo'' : @LinuxProcessSemantics.LinuxProcessSem.State.Model, ((K mo'') -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.mo_mat mo mo'') -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.regupd regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I)) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.of_nat k))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.v_addi pc 4%Z) mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo'') (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Lists.ListDef.skipn (@stdpp.bitvector.definitions.bv 8%N) k (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2))) KK)))))))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) regs pc mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) bs1 bs2)) KK))))))))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2 KK HF HE HK Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 AOKiov AOK1 AOK2 HKK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply srzJ_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HKK |].
  eapply (rz_writev2A regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) KK)); eassumption.
Qed.

#[using="K_halted K_mat"] Lemma rz_writev1_wallA : 
  (* plain text: the revision's writev needs the channel reader *)
  (forall regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall pc : (@stdpp.bitvector.definitions.bv 64%N), (forall mem : ((@stdpp.bitvector.definitions.bv 64%N) -> (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall mo : @LinuxProcessSemantics.LinuxProcessSem.State.Model, (forall w : (@stdpp.bitvector.definitions.bv 32%N), (forall fd : @Corelib.Numbers.BinNums.Z, (forall iov : (@stdpp.bitvector.definitions.bv 64%N), (forall b1 : (@stdpp.bitvector.definitions.bv 64%N), (forall n1 : (@stdpp.bitvector.definitions.bv 64%N), (forall bs1 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall KK : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.TSet, ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 32%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word segs pc) (@Corelib.Init.Datatypes.Some (@stdpp.bitvector.definitions.bv 32%N) w)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall w) (@Corelib.Init.Datatypes.true)) -> ((K mo) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds mo) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)))) -> ((@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader mo = true) -> ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt 0%Z fd) (@Stdlib.ZArith.BinInt.Z.lt fd (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z))) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 17%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 66%Z)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 11%Z (@Corelib.Init.Logic.I))) iov) -> ((@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV 5%N 12%Z (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv 64%N 1%Z)) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem iov 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 8%Z)) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat n1))) -> ((@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn segs mem b1 (@LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat n1)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) bs1)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 16%Z) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)) (@LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE)) -> ((@Stdlib.ZArith.BinInt.Z.le 1%Z (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)) -> ((@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N n1) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 30%Z)) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N iov) 16%Z))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((forall z : @Corelib.Numbers.BinNums.Z, ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) z) (@Stdlib.ZArith.BinInt.Z.lt z (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b1) (@stdpp.bitvector.definitions.bv_unsigned 64%N n1)))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.aok_addr AL CS z))) -> ((KK (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event))) -> ((forall k : @Corelib.Init.Datatypes.nat, ((@Corelib.Init.Peano.le 1%nat k) -> ((@Corelib.Init.Peano.le k (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) bs1)) -> (forall mo'' : @LinuxProcessSemantics.LinuxProcessSem.State.Model, ((K mo'') -> ((@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.ALazy.mo_mat mo mo'') -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.regupd regs (@stdpp.bitvector.definitions.BV 5%N 10%Z (@Corelib.Init.Logic.I)) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.of_nat k))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.v_addi pc 4%Z) mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo'') (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) (@Corelib.Lists.ListDef.skipn (@stdpp.bitvector.definitions.bv 8%N) k bs1)) KK)))))))) -> (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA.SRz.srealizesJ segs (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) regs pc mem (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs)) mo) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N fd)) bs1) KK))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd iov b1 n1 bs1 KK HF HE HK Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 AOKiov AOK1 HKK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply srzJ_wall; [unfold word_to_nat in L1; lia | exact HKK |].
  eapply (rz_writev1A regs pc mem mo w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) KK)); eassumption.
Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat K_vmonly"] Lemma rz_writev1_zeroA : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pregs,(4>.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(1.(0.&8.))Pmo,$1>.Pw,(0.&20.)Pfd,$17.Piov,(0.&40.)Pb1,(0.&40.)PKK,$2:.P,(8.(1.(0.&20.))(4?.Vsegs,R8.)(20.(0.&20.)R5.))P,(8.$50.(51.R6.)$52.)P,A1.VK,R8.P,(8.(1.$3:.)(3;.(3<.R9.)(<.&40.R7.))(20.$3:.(3=.(<.&40.R7.))))P,(7.(18.=R8.)(18.R8.(16.+2.+1?.)))P,(8.(0.&40.)(53.R>.(54.&5.+11.$55.))(<.&40.+42.))P,(8.(0.&40.)(53.R?.(54.&5.+:.$55.))(<.&40.R:.))P,(8.(0.&40.)(53.R10.(54.&5.+;.$55.))R:.)P,(8.(0.&40.)(53.R11.(54.&5.+<.$55.))(<.&40.+1.))P,(8.(1.(?.(0.&8.)))(56.Vsegs,R10.R<.#8.)(20.(?.(0.&8.))(57.#8.R;.)))P,(8.(1.(?.(0.&8.)))(56.Vsegs,R11.(<.&40.(14.(15.&40.R=.)+8.))#8.)(20.(?.(0.&8.))(57.#8.(<.&40.=))))P,(13.(14.(15.&40.R>.)+10.)$40.)P,(13.(15.&40.R>.)$40.)P,Pz,$17.P,(7.(13.(15.&40.R11.)R1.)(18.R1.(14.(15.&40.R11.)+10.)))(19.VAL,VCS,R2.)P,Pmo'',$1>.P,A1.VK,R1.P,(21.R16.R2.)(34.Vsegs,(35.(59.$5:.(5;.R1:.(54.&5.+:.$55.)(<.&40.=))(5<.R19.+4.)R18.(39.Vsegs,))R3.)R12.)(34.Vsegs,(35.(59.$5:.R18.R17.R16.(39.Vsegs,))R15.)R10.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd iov b1 KK HF HE HK Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 AOKiov Hc.
  pose proof (K_halted mo HK) as Hh.
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    exact (iovec_entry_accesses_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr). }
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  (* the check, closed, for any state with these registers and these iovec reads: the node's own
     state and every larger read-only backing of it (LPS revision: [RomBase.sys_rob]); the same
     shape as Sys/LibWritev.rz_writev1_zero *)
  assert (Hcl : forall ms0,
     ms_gpr ms0 0 = Z_to_bv 64 fd -> ms_gpr ms0 1 = iov -> ms_gpr ms0 2 = Z_to_bv 64 1 ->
     import_iovecs (ms_read_byte ms0) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)] ->
     import_iovecs_accesses (ms_read_byte ms0) iov (Z_to_bv 64 1) = [(iov, 16%nat)] ->
     forall eff, check_syscall (sys_input segs ms0 (getr regs 17)) eff mo
                 = check_ret_only_copyins [(iov, 16%nat)] eff (Z_to_bv 64 0) mo []).
  { intros ms0 F0 F1 F2 Himp0 Hacc0 eff.
    rewrite (check_syscall_writev (sys_input segs ms0 (getr regs 17)) eff mo) by (rewrite in_sysno_si; exact Hno).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si.
    rewrite F0, F1, F2.
    rewrite fd32_id by (rewrite u64_lit; lia).
    unfold check_writev. rewrite Hfd.
    replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
    change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    rewrite in_mem_si, Himp0, Hacc0.
    unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
    change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity. }
  assert (Hsv : ms_svc_pending ms = Some (getr regs 17)) by reflexivity.
  eapply (rz_ret_only_copyinsK_silent_chk ms mo (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) mo);
    [exact HK | exact Hsv | exact (Hcl ms G0 G1 G2 Himp Hacc) | apply vm_same_refl | |
    | unfold ms; rewrite adv_set_epend; exact Hc].
  - intros z (a & n & [E|[]] & Hz). injection E as <- <-. apply AOKiov. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. lia.
  - apply (RomBase.sys_rob_of_check segs ms mo). intros r x8' Hr Hs' eff.
    rewrite Hsv in Hs'. injection Hs' as <-.
    pose proof (RomWritev.import_iovecs_wrom ms r _ _ _ Hr Himp) as Himp'.
    pose proof (eq_trans (RomWritev.import_iovecs_accesses_wrom ms r _ _ _ Hr Himp) Hacc) as Hacc'.
    rewrite (Hcl (RomBase.wrom ms r) G0 G1 G2 Himp' Hacc'), (Hcl ms G0 G1 G2 Himp Hacc). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma cstr_access_len_le : forall mp a fuel, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp a fuel. revert a. induction fuel as [|fuel IH]; intros a; cbn [cstr_access_len_aux]; [lia|].
  destruct (negb (access_okb a 1)); [lia|].
  destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)). lia.
Qed.

#[using="Type"] Lemma rdn_S_inv : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pmem,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pk,$2.Pbs,(?.(0.&8.))P,(8.(1.(?.(0.&8.)))(56.Vsegs,R4.R3.(5>.R2.))(20.(?.(0.&8.))R1.))(9.(0.&8.)Lb,(0.&8.)(9.(?.(0.&8.))Lrest,(?.(0.&8.))(7.(8.(?.(0.&8.))R4.(5?.(0.&8.)R2.R1.))(7.(8.(1.(0.&8.))(60.Vsegs,R7.R6.)(20.(0.&8.)R2.))(8.(1.(?.(0.&8.)))(56.Vsegs,R7.(;.&40.R6.(54.&40.+1.$55.))R5.)(20.(?.(0.&8.))R1.))))))")
(* [comment removed for export] *).
Proof.
  intros mem a k bs H. cbn [rdn] in H. unfold mrb.
  destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
  destruct (rdn segs mem (a + 1) k) as [rest|]; [|discriminate].
  injection H as <-. exists b, rest. repeat split; reflexivity.
Qed.

(* At the revision [cstr_access_len_aux] stops at TASK_SIZE (the
   [access_okb a 1] test it shares with [read_cstr_aux]), so the count is
   the path's length only when the path ends below TASK_SIZE. *)
#[using="Type"] Lemma cstr_access_len_of_rdn : forall (mem : word -> option byte) (p : list byte) (a : word) (fuel : nat),
  rdn segs mem a (length p + 1)%nat = Some (p ++ [Z_to_bv 8 0]) ->
  ~ In (Z_to_bv 8 0) p ->
  (length p + 1 <= fuel)%nat ->
  (bv_unsigned a + Z.of_nat (length p) < TASK_SIZE)%Z ->
  cstr_access_len_aux (mrb segs mem) a fuel = (length p + 1)%nat.
Proof.
  intros mem p. induction p as [|c p IH]; intros a fuel Hrd Hnin Hf Hts.
  - destruct fuel as [|fuel]; [cbn in Hf; lia|].
    cbn [length Nat.add app] in Hrd. destruct (rdn_S_inv _ _ _ _ Hrd) as (b & rest & E & Hb & _).
    injection E as <- <-. cbn [cstr_access_len_aux length Nat.add].
    rewrite access_okb_one. cbn [length Z.of_nat] in Hts.
    replace (bv_unsigned a <? TASK_SIZE)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    rewrite Hb. cbn. reflexivity.
  - destruct fuel as [|fuel]; [cbn in Hf; lia|].
    cbn [length app] in Hrd. rewrite Nat.add_succ_l in Hrd.
    destruct (rdn_S_inv _ _ _ _ Hrd) as (b & rest & E & Hb & Hrest). injection E as <- <-.
    cbn [length] in Hts. rewrite Nat2Z.inj_succ in Hts.
    pose proof (bv_unsigned_in_range 64 a) as Ha.
    cbn [cstr_access_len_aux].
    rewrite access_okb_one. replace (bv_unsigned a <? TASK_SIZE)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    rewrite Hb.
    destruct (bv_eqb c (Z_to_bv 8 0)) eqn:Ec.
    + exfalso. apply Hnin. left. unfold bv_eqb in Ec. apply Z.eqb_eq in Ec. apply bv_eq. exact Ec.
    + cbn [length]. rewrite Nat.add_succ_l. f_equal. apply IH; [exact Hrest | | cbn [length] in Hf; lia |].
      * intros Hin. apply Hnin. right. exact Hin.
      * rewrite bv_unsigned_succ_below_task_size by lia. lia.
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (mo : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis HK : K mo.
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds mo.
  Let Hh : m_halted mo = None := K_halted mo HK.

  #[using="H17"] Lemma Hno56A : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  #[using="H17 H10"] Lemma openat_spec_headA : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Po,(64.$2<.)(65.(66.(2?.Vsegs,Vms,(53.Vregs,(54.&5.+11.$55.)))Vmo,R1.)(67.$68.(53.Vregs,(54.&5.+;.$55.))(53.Vregs,(54.&5.+<.$55.))(2?.Vsegs,Vms,(53.Vregs,(54.&5.+11.$55.)))Vmo,R1.))")
(* [comment removed for export] *).
  Proof.
    intros o. cbv delta [ms].
    rewrite (syscall_spec_56 _ mo o) by (rewrite in_sysno_si; exact Hno56A).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10.
    reflexivity.
  Qed.

  #[using="Type"] Lemma open_in_memA : in_mem (sys_input segs ms (getr regs 17)) = mrb segs mem.
  Proof. cbv delta [ms]. rewrite in_mem_si, ms_read_byte_epend. reflexivity. Qed.

  (* [RomBase.sys_rob] at an openat node whose path read does not fault ([BB.RomWrite.openat_rob]). *)
  #[using="H17"] Lemma open_robA : read_cstr (mrb segs mem) (getr regs 11) <> CstrFault ->
    RomBase.sys_rob segs (mkCfg ms mo).
  Proof.
    intros Hnf. apply (RomWrite.openat_rob segs ms mo (getr regs 17) eq_refl Hno56A).
    cbv delta [ms]. rewrite ms_gpr_epend1, ms_read_byte_epend. exact Hnf.
  Qed.

  #[using="Hfl"] Lemma open_flags_modeledA : modeled_open_flags (getr regs 12) = true.
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  #[using="Type"] Lemma open_reads_msA : open_reads (sys_input segs ms (getr regs 17)) (getr regs 11) = open_copyins ms.
  Proof. cbv delta [ms]. unfold open_reads, open_copyins. rewrite in_mem_si, ms_gpr_epend1. reflexivity. Qed.

  (* [comment removed for export] *)
  (* At the revision [read_cstr] refuses a byte at or above TASK_SIZE, so
     the path must end below it (plain text: the old encoded definition
     had three conjuncts). *)
  Definition path_atA (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1)%nat = Some (p ++ [Z_to_bv 8 0])
    /\ (bv_unsigned (getr regs 11) + Z.of_nat (length p) < TASK_SIZE)%Z.

  #[using="Type"] Lemma path_atA_cstr : forall p, path_atA p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3 & H4). apply read_cstr_of_rdn; assumption. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma open_copyins_path : forall p, path_atA p -> open_copyins ms = [(getr regs 11, (length p + 1)%nat)].
  Proof.
    intros p (H1 & H2 & H3 & H4). unfold open_copyins. cbv delta [ms]. rewrite ms_gpr_epend1, ms_read_byte_epend.
    rewrite (cstr_access_len_of_rdn mem p (getr regs 11) path_max H3 H2); [reflexivity | unfold path_max; lia | exact H4].
  Qed.

  #[using="Type"] Lemma acc_ok_path : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pp,(?.(0.&8.))P,(69.R1.)P,Pz,$17.P,(7.(13.(15.&40.(53.Vregs,(54.&5.+;.$55.)))R1.)(18.R1.(14.(14.(15.&40.(53.Vregs,(54.&5.+;.$55.)))(>.(3?.(0.&8.)R3.)))+1.)))(19.VAL,VCS,R2.)(1:.VAL,VCS,(6:.Vms,))")
(* [comment removed for export] *).
  Proof.
    intros p Hp AOK. rewrite (open_copyins_path p Hp). intros z (a & n & [E|[]] & Hz). injection E as <- <-.
    apply AOK. lia.
  Qed.

  (* [comment removed for export] *)
  (* Plain text: the revision's [read_cstr] needs the 4096 bytes below
     TASK_SIZE (new premise after the NUL-free one). *)
  #[using="K_halted K_mat K_vmonly w HF HE HK H17 H10 Hfl ms Hh"] Lemma rz_openat_toolongA : forall (bs : list byte) (KK : TSet),
    rdn segs mem (getr regs 11) 4096%nat = Some bs ->
    ~ In (Z_to_bv 8 0) bs ->
    (bv_unsigned (getr regs 11) + 4096 <= TASK_SIZE)%Z ->
    (forall z : Z, (bv_unsigned (getr regs 11) <= z < bv_unsigned (getr regs 11) + 4096)%Z -> aok_addr AL CS z) ->
    (forall mo'' : Model, K mo'' -> mo_mat mo mo'' -> srealizesJ segs (mkCfg (post (errno_ret ENAMETOOLONG)) mo'') KK) ->
    srealizesJ segs (mkCfg (mkst regs pc mem (seg_rom segs)) mo) KK.
  Proof.
    intros bs KK Hrd Hnz Hts AOK Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hts Hrd) as Hp.
    eapply rz_sysA; [exact Hh | exact HF | exact HE |].
    eapply (rz_ret_only_copyinsK_silent segs AL CS K K_halted K_mat K_vmonly);
      [exact HK | reflexivity | | apply vm_same_refl | | exact (open_robA ltac:(rewrite Hp; discriminate))
      | cbv delta [ms]; rewrite adv_set_epend; exact Hc].
    - intros o. fold ms. rewrite openat_spec_headA.
      apply (openat_toolong_outcome _ _ _ _ mo open_flags_modeledA). rewrite open_in_memA. exact Hp.
    - unfold open_reads. cbv delta [ms]. rewrite in_mem_si, ms_read_byte_epend.
      pose proof (cstr_access_len_le (mrb segs mem) (getr regs 11) path_max) as HL. unfold path_max in HL |- *.
      revert HL. generalize (cstr_access_len_aux (mrb segs mem) (getr regs 11) 4096) as N. intros N HL.
      intros z (a & n & [E|[]] & Hz). injection E as <- <-. apply AOK. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="K_halted K_mat K_vmonly w HF HE HK H17 H10 Hfl ms Hh"] Lemma rz_openat_emptyA : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "PKK,$2:.P,(69.(31.(0.&8.)))P,(19.VAL,VCS,(15.&40.(53.Vregs,(54.&5.+;.$55.))))P,Pmo'',$1>.P,A1.VK,R1.P,(21.Vmo,R2.)(34.Vsegs,(35.A1.Vpost,(6;.$6=.)R3.)R6.)(34.Vsegs,(35.(59.$5:.Vregs,Vpc,Vmem,(39.Vsegs,))Vmo,)R4.)")
(* [comment removed for export] *).
  Proof.
    intros KK Hp AOK Hc. cbv delta [post] in *.
    eapply rz_sysA; [exact Hh | exact HF | exact HE |].
    eapply (rz_ret_only_copyinsK_silent segs AL CS K K_halted K_mat K_vmonly);
      [exact HK | reflexivity | | apply vm_same_refl | | exact (open_robA ltac:(rewrite (path_atA_cstr [] Hp); discriminate))
      | cbv delta [ms]; rewrite adv_set_epend; exact Hc].
    - intros o. fold ms. rewrite openat_spec_headA.
      apply (openat_empty_outcome _ _ _ _ mo open_flags_modeledA). rewrite open_in_memA. exact (path_atA_cstr [] Hp).
    - apply (acc_ok_path [] Hp). intros z Hz. cbn [length] in Hz. replace z with (bv_unsigned (getr regs 11)) by lia. exact AOK.
  Qed.

  (* [comment removed for export] *)
  #[using="K_halted K_mat K_vmonly w HF HE HK H17 H10 Hfl ms Hh"] Lemma rz_openat_absentA : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pp,(?.(0.&8.))PKK,$2:.P,(69.R2.)P,(62.(8.(?.(0.&8.))R3.(31.(0.&8.))))P,(62.(8.(?.(0.&8.))R4.$6>.))P,(8.$50.(6?.R5.)$70.)P,(8.$50.(71.R6.$72.)$70.)P,(8.(1.(?.(0.&8.)))(73.(74.Vmo,)R7.)(75.(?.(0.&8.))))P,Pz,$17.P,(7.(13.(15.&40.(53.Vregs,(54.&5.+;.$55.)))R1.)(18.R1.(14.(14.(15.&40.(53.Vregs,(54.&5.+;.$55.)))(>.(3?.(0.&8.)R9.)))+1.)))(19.VAL,VCS,R2.)P,Pmo'',$1>.P,A1.VK,R1.P,(21.Vmo,R2.)(34.Vsegs,(35.A1.Vpost,(6;.$6=.)R3.)R;.)(34.Vsegs,(35.(59.$5:.Vregs,Vpc,Vmem,(39.Vsegs,))Vmo,)R9.)")
(* [comment removed for export] *).
  Proof.
    intros p KK Hp Hne Hnd Hsl Hdd Hfs AOK Hc. cbv delta [post] in *.
    eapply rz_sysA; [exact Hh | exact HF | exact HE |].
    eapply (rz_ret_only_copyinsK_silent segs AL CS K K_halted K_mat K_vmonly);
      [exact HK | reflexivity | | apply vm_same_refl | | exact (open_robA ltac:(rewrite (path_atA_cstr p Hp); discriminate))
      | cbv delta [ms]; rewrite adv_set_epend; exact Hc].
    - intros o. fold ms. rewrite openat_spec_headA.
      apply (openat_absent_outcome _ _ _ _ mo open_flags_modeledA eq_refl Hfl p);
        [rewrite open_in_memA; exact (path_atA_cstr p Hp) | exact Hne | exact Hnd | exact Hsl | exact Hdd | exact Hfs].
    - exact (acc_ok_path p Hp AOK).
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  (* Was an encoded statement (CDefT.buildp); written out from its decode (cdeft_print.py), not
     re-encoded, with one premise added, [RomBase.sys_rob segs (mkCfg ms mo)], for the open node. *)
  #[using="K_halted K_mat K_vmonly HK Hh Hfree"] Lemma rz_openK : forall (reads : list (bv 64 * nat))
      (mk : bv 64 -> Model) (A B : TSet),
    (forall o, syscall_spec (sys_input segs ms (getr regs 17)) mo o <-> open_out reads mo mk o) ->
    (forall fd, vm_same mo (mk fd)) ->
    acc_ok AL CS reads ->
    RomBase.sys_rob segs (mkCfg ms mo) ->
    (forall e, In e openat_errnos -> forall mo'', K mo'' -> mo_mat mo mo'' ->
       srealizesJ segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) mo'') A) ->
    (forall mo'', K mo'' -> mo_mat (mk (alloc_fd fds)) mo'' ->
       srealizesJ segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd fds))) mo'') B) ->
    srealizesJ segs (mkCfg ms mo) (t_alt2 A B)
(* [comment removed for export] *).
  Proof.
    intros reads mk A B Hchk VS OK Hrob HA HB.
    pose (effs := fun i : open_I mo => match i with
            | inl (exist _ e _) => with_copyins reads (mkEffect (errno_ret e) [] [])
            | inr _ => with_copyins reads (mkEffect (alloc_fd fds) [] []) end).
    pose (ms' := fun i : open_I mo => match i with inl _ => mo | inr _ => mk (alloc_fd fds) end).
    pose (ms'' := fun i : open_I mo => matK (ms' i) reads).
    assert (HKi : forall i, K (ms' i)).
    { intros [[e He]|[]]; cbn [ms']; [exact HK | eapply (K_vm_same K K_vmonly); [exact HK | apply VS]]. }
    assert (Eacc : forall i, syscall_effect_accesses (effs i) = reads).
    { intros [[e He]|[]]; cbn [effs]; apply syscall_effect_accesses_copyins. }
    assert (Hnode : node_ok segs (mkCfg ms mo) (open_I mo) (fun _ => [])
                      (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i))).
    { apply (node_family_mat segs ms mo (getr regs 17) (open_I mo) effs ms' ms'' (fun _ => []) _ Hh eq_refl Hchk).
      - intros [[e He] | []]; [left; exists e; auto | right; auto].
      - intros o [(e & He & ->) | (Hlk & ->)]; [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity.
      - intros i. exact (K_halted _ (HKi i)).
      - intros i. rewrite Eacc. unfold ms''. exact (proj1 (matK_spec (ms' i) reads (HKi i) OK)).
      - exact Hrob. }
    apply (srzJ_alt2 segs (mkCfg ms mo) {e : Z | In e openat_errnos} unit
             (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i)) A B
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt Hnode).
    - intros [e He]. cbn [effs ms'' ms']. rewrite apply_effect_copyins_no_write.
      destruct (matK_spec mo reads HK OK) as (_ & HK' & MM). apply HA; assumption.
    - intros []. cbn [effs ms'' ms']. rewrite apply_effect_copyins_no_write.
      destruct (matK_spec (mk (alloc_fd fds)) reads (HKi (inr tt)) OK) as (_ & HK' & MM). apply HB; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="K_halted K_mat K_vmonly w HF HE HK H17 H10 Hfl ms Hh Hfree"] Lemma rz_openat_dotA : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "PKA,$2:.PKB,$2:.P,(69.$6>.)P,Pz,$17.P,(7.(13.(15.&40.(53.Vregs,(54.&5.+;.$55.)))R1.)(18.R1.(14.(15.&40.(53.Vregs,(54.&5.+;.$55.)))+2.)))(19.VAL,VCS,R2.)P,Pe,$17.P,(3.$17.R1.$77.)Pmo'',$1>.P,A1.VK,R1.P,(21.Vmo,R2.)(34.Vsegs,(35.A1.Vpost,(6;.R5.)R3.)R9.)P,Pmo'',$1>.P,A1.VK,R1.P,(21.(7:.(7;.Vfds,(78.Vfds,)$7<.)Vmo,)R2.)(34.Vsegs,(35.A1.Vpost,(78.Vfds,)R3.)R7.)(34.Vsegs,(35.(59.$5:.Vregs,Vpc,Vmem,(39.Vsegs,))Vmo,)(79.R6.R5.))")
(* [comment removed for export] *).
  Proof.
    intros KA KB Hp AOK HA HB. cbv delta [post] in *.
    eapply rz_sysA; [exact Hh | exact HF | exact HE |].
    eapply (rz_openK (open_reads (sys_input segs ms (getr regs 17)) (getr regs 11)) (fun fd => with_fds (fd_insert fds fd FdDir) mo)).
    - intros o. fold ms. rewrite openat_spec_headA.
      apply (openat_dot_outcome _ _ _ _ mo open_flags_modeledA eq_refl Hfl). rewrite open_in_memA. exact (path_atA_cstr _ Hp).
    - intros fd. apply vm_same_with_fds.
    - rewrite open_reads_msA. apply (acc_ok_path dot_path Hp). intros z Hz. apply AOK. unfold dot_path in Hz. cbn [length] in Hz. lia.
    - exact (open_robA ltac:(rewrite (path_atA_cstr _ Hp); discriminate)).
    - intros e He mo'' HK'' MM. cbv delta [ms]. rewrite adv_set_epend. apply HA; assumption.
    - intros mo'' HK'' MM. cbv delta [ms]. rewrite adv_set_epend. apply HB; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="K_halted K_mat K_vmonly w HF HE HK H17 H10 Hfl ms Hh Hfree"] Lemma rz_openat_fileA : ltac2:(CDefT.buildp (gd_tbl_NodesA2 ()) "Pp,(?.(0.&8.))Pd,(?.(0.&8.))PKA,$2:.PKB,$2:.P,(69.R4.)P,(62.(8.(?.(0.&8.))R5.(31.(0.&8.))))P,(62.(8.(?.(0.&8.))R6.$6>.))P,(8.$50.(6?.R7.)$70.)P,(8.$50.(71.R8.$72.)$70.)P,(8.(1.(?.(0.&8.)))(73.(74.Vmo,)R9.)(20.(?.(0.&8.))R8.))P,Pz,$17.P,(7.(13.(15.&40.(53.Vregs,(54.&5.+;.$55.)))R1.)(18.R1.(14.(14.(15.&40.(53.Vregs,(54.&5.+;.$55.)))(>.(3?.(0.&8.)R;.)))+1.)))(19.VAL,VCS,R2.)P,Pe,$17.P,(3.$17.R1.$77.)Pmo'',$1>.P,A1.VK,R1.P,(21.Vmo,R2.)(34.Vsegs,(35.A1.Vpost,(6;.R5.)R3.)R>.)P,Pmo'',$1>.P,A1.VK,R1.P,(21.(7:.(7;.Vfds,(78.Vfds,)(7=.R>.(<.&40.=)))Vmo,)R2.)(34.Vsegs,(35.A1.Vpost,(78.Vfds,)R3.)R<.)(34.Vsegs,(35.(59.$5:.Vregs,Vpc,Vmem,(39.Vsegs,))Vmo,)(79.R;.R:.))")
(* [comment removed for export] *).
  Proof.
    intros p d KA KB Hp Hne Hnd Hsl Hdd Hfs AOK HA HB. cbv delta [post] in *.
    eapply rz_sysA; [exact Hh | exact HF | exact HE |].
    eapply (rz_openK (open_reads (sys_input segs ms (getr regs 17)) (getr regs 11)) (fun fd => with_fds (fd_insert fds fd (FdFile p (Z_to_bv 64 0))) mo)).
    - intros o. fold ms. rewrite openat_spec_headA.
      apply (openat_file_outcome _ _ _ _ mo open_flags_modeledA eq_refl Hfl p d);
        [rewrite open_in_memA; exact (path_atA_cstr p Hp) | exact Hne | exact Hnd | exact Hsl | exact Hdd | exact Hfs].
    - intros fd. apply vm_same_with_fds.
    - rewrite open_reads_msA. exact (acc_ok_path p Hp AOK).
    - exact (open_robA ltac:(rewrite (path_atA_cstr p Hp); discriminate)).
    - intros e He mo'' HK'' MM. cbv delta [ms]. rewrite adv_set_epend. apply HA; assumption.
    - intros mo'' HK'' MM. cbv delta [ms]. rewrite adv_set_epend. apply HB; assumption.
  Qed.
End Openat.

End WithSegs.
