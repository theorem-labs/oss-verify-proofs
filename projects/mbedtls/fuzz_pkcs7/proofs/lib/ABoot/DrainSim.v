(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamExec WallSim StreamSim.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_DrainSim () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.InputStream"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.ABoot.StreamSim.chunks"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "procs"; "Stdlib.Lists.List.concat"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Datatypes.app"; "reads_ch"; "Traces.out_tail"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.State.ExitEv"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "Traces.drain_from_ch"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.IEof"; "Traces.drain_from"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.fst"; "LinuxProcessSemantics.LinuxProcessSem.State.stream_take"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.State.ReadEv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Drain.to_out"; "OSSVerify.KrLib.ABoot.WallSim.to_wall_tail"; "OSSVerify.KrLib.ABoot.ExitSim.to_exit"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Drain.to_rd"; "Drain.ReadPend"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "OSSVerify.KrLib.ABoot.CatSim.fd1chan"; "OSSVerify.KrLib.ABoot.CatSim.buf_modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.State.m_stdin"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "LinuxProcessSemantics.LinuxProcessSem.State.read_bytes_map"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_writable_byte"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.access_okb"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.check_read"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.fd32"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckOk"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.with_stdin"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "OSSVerify.KrLib.ABoot.StreamSim.M_loop"; "reads"; "out_tail"; "drain_from"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_ms"; "OSSVerify.KrLib.ABoot.ExitSim.on_path"; "Drain.dinv"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"; "LinuxProcessSemantics.LinuxProcessSem.State.in_stdin"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.coexec"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.never_errors"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_corun"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_cosafe"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.rw_bytes_max"; "to_rd"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.

Fixpoint procs (a : A) (bs : list byte) : option A :=
  match bs with
  | [] => Some a
  | b :: rest => match f a b with Some a' => procs a' rest | None => None end
  end.

#[using="Type"] Lemma procs_app : forall bs1 bs2 a,
  procs a (bs1 ++ bs2) =
  match procs a bs1 with Some a' => procs a' bs2 | None => None end.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 a; [reflexivity|].
  cbn [procs app]. destruct (f a b); [apply IH | reflexivity].
Qed.
End Proc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition block_ok (cnt : word) (bs : list byte) : Prop :=
  (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.

(* [comment removed for export] *)
Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
  flat_map (fun bs => map (ReadEv rch) bs) blocks.

Lemma reads_ch_cons : forall rch bs blocks,
  reads_ch rch (bs :: blocks) = map (ReadEv rch) bs ++ reads_ch rch blocks.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition reads (blocks : list (list byte)) : list event :=
  reads_ch (Z_to_bv 64 0) blocks.

Lemma reads_cons : forall bs blocks,
  reads (bs :: blocks) = map (ReadEv (Z_to_bv 64 0)) bs ++ reads blocks.
Proof. exact (reads_ch_cons (Z_to_bv 64 0)). Qed.

Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.

(* [comment removed for export] *)
Definition out_tail (s : InputStream) (a : A) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition drain_from_ch (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop := ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "(0.(1.(2.(2.(3.&8.)))Lblocks,(2.(2.(3.&8.)))(1.$4.Ls',$4.(1.VA,La',VA,(5.(6.Vcnt,O2.R3.R2.)(5.(7.(8.VA,)(9.VA,Vf,O4.(:.(3.&8.)R3.))(;.VA,R1.))(<.$=.O1.(>.$=.(?.O5.R3.)(10.R2.R1.O3.))))))))(1.(2.(2.(3.&8.)))Lblocks,(2.(2.(3.&8.)))(1.(2.(3.&8.))Lbs,(2.(3.&8.))(1.$4.Ls',$4.(1.VA,La',VA,(5.(6.Vcnt,O2.(>.(2.(3.&8.))R4.(11.(2.(3.&8.))R3.(12.(2.(3.&8.)))))R2.)(5.(7.(8.VA,)(9.VA,Vf,O4.(:.(3.&8.)R4.))(;.VA,R1.))(5.(7.(8.VA,)(9.VA,Vf,R1.R3.)(13.VA,))(<.$=.O1.(>.$=.(?.O5.(>.(2.(3.&8.))R4.(11.(2.(3.&8.))R3.(12.(2.(3.&8.))))))(11.$=.(14.Vec,O3.)(12.$=.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition drain_from (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  drain_from_ch (Z_to_bv 64 0) a fs s tr.

#[using="Type"] Lemma drain_from_ch_prefix : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Prch,(3.&40.)Pa,VA,Pfs,$15.Ps,$4.Ptr,(2.$=.)Ptr',(2.$=.)P,(16.R6.R5.R4.R3.R2.)P,(<.$=.R2.R3.)(16.R8.R7.R6.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros rch a fs s tr tr' [ (blocks & s' & a' & HC & Hp & Hpref)
                           | (blocks & bs & s' & a' & HC & Hp & Hn & Hpref) ] Hp'.
  - left. exists blocks, s', a'.
    split; [exact HC | split; [exact Hp | eapply is_prefix_trans; eauto]].
  - right. exists blocks, bs, s', a'.
    split; [exact HC | split; [exact Hp |
    split; [exact Hn | eapply is_prefix_trans; eauto]]].
Qed.

#[using="Type"] Lemma drain_from_prefix : forall a fs s tr tr',
  drain_from a fs s tr -> is_prefix tr' tr -> drain_from a fs s tr'.
Proof. exact (drain_from_ch_prefix (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_nil : forall rch a fs s, drain_from_ch rch a fs s [].
Proof.
  intros rch a fs s. left. exists [], s, a.
  split; [constructor | split; [reflexivity | apply is_prefix_nil]].
Qed.

#[using="Type"] Lemma drain_from_nil : forall a fs s, drain_from a fs s [].
Proof. exact (drain_from_ch_nil (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma drain_from_ch_out : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Prch,(3.&40.)Pa,VA,Pfs,$15.Ptr,(2.$=.)P,(<.$=.R1.(>.$=.(17.(3.&8.)$=.(18.(19.&40.+1.))A1.Vout,R3.)(11.$=.(14.(19.&40.=)R2.)(12.$=.))))(16.R5.R4.R3.$1:.R2.)")
(* [comment removed for export] *).
Proof.
  intros rch a fs tr Hp. left. exists [], IEof, a.
  split; [constructor | split; [reflexivity | exact Hp]].
Qed.

#[using="Type"] Lemma drain_from_out : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pa,VA,Pfs,$15.Ptr,(2.$=.)P,(<.$=.R1.(>.$=.(17.(3.&8.)$=.(18.(19.&40.+1.))A1.Vout,R3.)(11.$=.(14.(19.&40.=)R2.)(12.$=.))))(1;.R4.R3.$1:.R2.)")
(* [comment removed for export] *).
Proof. exact (drain_from_ch_out (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_block : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Prch,(3.&40.)Pa,VA,Pa1,VA,Pfs,$15.Ps,$4.Pbs,(2.(3.&8.))Ptr,(2.$=.)P,(1<.+1.(1=.(1>.(3.&8.)R2.)))P,(1<.(1=.(1>.(3.&8.)R3.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.R5.(1>.(3.&8.)R4.)))R4.)P,(7.(8.VA,)(9.VA,Vf,R9.R5.)(;.VA,R8.))P,(16.R;.R9.R8.(22.(2.(3.&8.))$4.(21.R7.(1>.(3.&8.)R6.)))R5.)(16.R<.R;.R9.R8.(>.$=.(17.(3.&8.)$=.(23.R<.)R7.)R6.))")
(* [comment removed for export] *).
Proof.
  intros rch a a1 fs s bs tr Hlo Hhi Hpre Hs
    [ (blocks & s' & a' & HC & Hp & Hpref)
    | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
  - left. exists (bs :: blocks), s', a'.
    split; [eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
  - right. exists (bs :: blocks), bsE, s', a'.
    split; [change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE]));
            eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    split; [exact Hn |].
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
Qed.

#[using="Type"] Lemma drain_from_block : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pa,VA,Pa1,VA,Pfs,$15.Ps,$4.Pbs,(2.(3.&8.))Ptr,(2.$=.)P,(1<.+1.(1=.(1>.(3.&8.)R2.)))P,(1<.(1=.(1>.(3.&8.)R3.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.R5.(1>.(3.&8.)R4.)))R4.)P,(7.(8.VA,)(9.VA,Vf,R9.R5.)(;.VA,R8.))P,(1;.R9.R8.(22.(2.(3.&8.))$4.(21.R7.(1>.(3.&8.)R6.)))R5.)(1;.R;.R9.R8.(>.$=.(17.(3.&8.)$=.(23.(19.&40.=))R7.)R6.))")
(* [comment removed for export] *).
Proof. exact (drain_from_ch_block (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_err : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Prch,(3.&40.)Pa,VA,Pfs,$15.Ps,$4.Pbs,(2.(3.&8.))Ptr,(2.$=.)P,(1<.+1.(1=.(1>.(3.&8.)R2.)))P,(1<.(1=.(1>.(3.&8.)R3.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.R5.(1>.(3.&8.)R4.)))R4.)P,(7.(8.VA,)(9.VA,Vf,R8.R5.)(13.VA,))P,(<.$=.R5.(11.$=.(14.Vec,R8.)(12.$=.)))(16.R;.R:.R9.R8.(>.$=.(17.(3.&8.)$=.(23.R;.)R7.)R6.))")
(* [comment removed for export] *).
Proof.
  intros rch a fs s bs tr Hlo Hhi Hpre Hn Hp. right.
  exists [], bs, (snd (stream_take s (length bs))), a.
  split; [cbn [app]; eapply chunks_cons;
          try eassumption; constructor |].
  split; [reflexivity |].
  split; [exact Hn |].
  cbn [app]. unfold reads_ch. cbn [flat_map]. rewrite app_nil_r.
  apply is_prefix_app_mono. exact Hp.
Qed.

#[using="Type"] Lemma drain_from_err : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pa,VA,Pfs,$15.Ps,$4.Pbs,(2.(3.&8.))Ptr,(2.$=.)P,(1<.+1.(1=.(1>.(3.&8.)R2.)))P,(1<.(1=.(1>.(3.&8.)R3.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.R5.(1>.(3.&8.)R4.)))R4.)P,(7.(8.VA,)(9.VA,Vf,R8.R5.)(13.VA,))P,(<.$=.R5.(11.$=.(14.Vec,R8.)(12.$=.)))(1;.R:.R9.R8.(>.$=.(17.(3.&8.)$=.(23.(19.&40.=))R7.)R6.))")
(* [comment removed for export] *).
Proof. exact (drain_from_ch_err (Z_to_bv 64 0)). Qed.

End Traces.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd1chan_with_stdin : forall s m, fd1chan m -> fd1chan (with_stdin s m).
Proof. intros s m H. exact H. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drain.
Context {A : Type}.
Variable segs : list Segment.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.

(* [comment removed for export] *)
Definition lh_next (a : A) (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH a ms'.

(* [comment removed for export] *)
Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).

(* [comment removed for export] *)
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_out bs ms' -> to_out bs ms.

(* [comment removed for export] *)
Definition ReadPend (a : A) (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
             = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (* [comment removed for export] *)
  buf_modeled (out a) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     match procs f a bs with
     | Some a' => lh_next a'
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     | None => to_exit segs ec
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     end).

(* [comment removed for export] *)
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd a ms' -> to_rd a ms.

#[using="Type"] Lemma msteps_to_rd : forall a ms ms',
  msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof.
  intros a ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

#[using="Type"] Lemma msteps_to_out : forall bs ms ms',
  msteps segs ms ms' -> to_out bs ms' -> to_out bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Ho. eapply tout_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_out_wall_tail : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pbs,(2.(3.&8.))Pms,$24.P,(25.R2.R1.)(26.Vsegs,(19.&40.+1.)R2.R3.(27.Vsegs,(19.&40.=)))")
(* [comment removed for export] *).
Proof.
  intros bs ms H;
    induction H as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH].
  - apply twt_done. exact Hte.
  - destruct HWF as [Hnb Hwl]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

#[using="H_LH"] Lemma lh_next_to_rd : forall a ms, lh_next a ms -> to_rd a ms.
Proof.
  intros a ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_rd_star : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pa,VA,Pms,$24.Pmodel,$28.P,(7.(8.(3.&40.))(29.R1.)(13.(3.&40.)))P,(7.(2.(2:.(3.&40.)(3.&40.)))(2;.R2.)(12.(2:.(3.&40.)(3.&40.))))P,(2<.R5.R4.)(1.$24.LmsR,$24.(5.(2=.R7.R1.)(2>.Vsegs,(2?.R6.R5.)(12.$=.)(2?.R1.R5.))))")
(* [comment removed for export] *).
Proof.
  intros a ms model Hh Hlazy Hrd.
  induction Hrd as [a ms HRP | a ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma msteps_star : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Pms',$24.Pmodel,$28.P,(7.(8.(3.&40.))(29.R1.)(13.(3.&40.)))P,(7.(2.(2:.(3.&40.)(3.&40.)))(2;.R2.)(12.(2:.(3.&40.)(3.&40.))))P,(30.Vsegs,R5.R4.)(2>.Vsegs,(2?.R6.R4.)(12.$=.)(2?.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Hh Hlazy H. induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
  - apply star_refl.
  - change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms1 model) | exact IH];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_out_star_admits : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pbs,(2.(3.&8.))Pms,$24.Pmodel,$28.P,(31.R1.)P,(7.(8.(3.&40.))(29.R2.)(13.(3.&40.)))P,(7.(2.(2:.(3.&40.)(3.&40.)))(2;.R3.)(12.(2:.(3.&40.)(3.&40.))))P,(25.R6.R5.)P,(32.R7.)(1.$33.Lc,$33.(2>.Vsegs,(2?.R8.R7.)(>.$=.(17.(3.&8.)$=.(18.(19.&40.+1.))R9.)(11.$=.(14.(19.&40.=)(34.R7.))(12.$=.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH]; intro Hbm.
  - cbn [map app].
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms model Hh Hlazy Hte) as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 |].
    intros ms' Hex.
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex)
      as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct (IH Hbm) as [c Hstar]. exists c.
    replace (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
      with ([] ++ (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]))
      by reflexivity.
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma to_out_star_only : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pbs,(2.(3.&8.))Pms,$24.Pmodel,$28.P,(31.R1.)P,(7.(8.(3.&40.))(29.R2.)(13.(3.&40.)))P,(7.(2.(2:.(3.&40.)(3.&40.)))(2;.R3.)(12.(2:.(3.&40.)(3.&40.))))P,(25.R6.R5.)P,(32.R7.)Ptr,(2.$=.)Pc,$33.P,(2>.Vsegs,(2?.R9.R8.)R2.R1.)(<.$=.R3.(>.$=.(17.(3.&8.)$=.(18.(19.&40.+1.))R;.)(11.$=.(14.(19.&40.=)(34.R9.))(12.$=.))))")
(* [comment removed for export] *).
Proof.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH];
    intros Hbm tr c Hstar.
  - cbn [map app].
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms model Hh Hlazy Hte tr c Hstar)
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_only segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 | | exact Hstar].
    intros ms' tr' c' Hex Hstar'.
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex tr' c' Hstar')
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst; [apply is_prefix_nil|].
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm tr2 _ Hstar2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt"] Lemma read0_check_eof_cnt : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Px8,(3.&40.)Pmodel,$28.Pw,(2.(3.&8.))P,(7.$35.(1?.&40.R3.)+3?.)P,(7.(8.$36.)(37.(38.R3.)(19.&40.=))(;.$36.(39.(19.&40.=))))P,(7.$4.(3:.R4.)$1:.)P,(7.(3.&40.)(3;.R7.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R8.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R9.)(3;.R9.#1.)Vcnt,)(;.(2.(3.&8.))R6.))P,(7.$3>.(3?.(3;.R:.#1.)(1?.&40.Vcnt,))$40.)(7.$41.(42.(43.Vsegs,R;.R:.)(44.(3;.R;.#0.))(3;.R;.#1.)(3;.R;.#2.)(45.(19.&40.=)(12.(2:.(3.&40.)(2.(3.&8.))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.)))R9.)(48.R9.(12.$=.)))")
(* [comment removed for export] *).
Proof. apply (StreamSim.read0_check_eof cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_eof_cnt : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Px8,(3.&40.)Pmodel,$28.Pw,(2.(3.&8.))P,(7.$35.(1?.&40.R3.)+3?.)P,(7.(8.$36.)(37.(38.R3.)(19.&40.=))(;.$36.(39.(19.&40.=))))P,(7.$4.(3:.R4.)$1:.)P,(7.(3.&40.)(3;.R7.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R8.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R9.)(3;.R9.#1.)Vcnt,)(;.(2.(3.&8.))R6.))P,(7.$3>.(3?.(3;.R:.#1.)(1?.&40.Vcnt,))$40.)(49.(43.Vsegs,R;.R:.)R9.(4:.$4;.(45.(19.&40.=)(12.(2:.(3.&40.)(2.(3.&8.))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.)))R9.(12.$=.)))")
(* [comment removed for export] *).
Proof. apply (StreamSim.read0_ok_eof cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_check_bytes_cnt : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Px8,(3.&40.)Pmodel,$28.Pw,(2.(3.&8.))Pbs,(2.(3.&8.))P,(7.$35.(1?.&40.R4.)+3?.)P,(7.(8.$36.)(37.(38.R4.)(19.&40.=))(;.$36.(39.(19.&40.=))))P,(7.(3.&40.)(3;.R7.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R8.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R9.)(3;.R9.#1.)Vcnt,)(;.(2.(3.&8.))R6.))P,(7.$3>.(3?.(3;.R:.#1.)(1?.&40.Vcnt,))$40.)P,(1<.+1.(1=.(1>.(3.&8.)R7.)))P,(1<.(1=.(1>.(3.&8.)R8.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.(3:.R;.)(1>.(3.&8.)R9.)))R9.)(7.$41.(42.(43.Vsegs,R>.R=.)(44.(3;.R>.#0.))(3;.R>.#1.)(3;.R>.#2.)(45.(4<.(3.&8.)R:.)(11.(2:.(3.&40.)(2.(3.&8.)))(4=.(3.&40.)(2.(3.&8.))(3;.R>.#1.)R:.)(12.(2:.(3.&40.)(2.(3.&8.)))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.)))R<.)(48.(4>.(22.(2.(3.&8.))$4.(21.(3:.R<.)(1>.(3.&8.)R:.)))R<.)(17.(3.&8.)$=.(23.(19.&40.=))R:.)))")
(* [comment removed for export] *).
Proof. apply (StreamSim.read0_check_bytes cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_bytes_cnt : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Px8,(3.&40.)Pmodel,$28.Pw,(2.(3.&8.))Pbs,(2.(3.&8.))P,(7.$35.(1?.&40.R4.)+3?.)P,(7.(8.$36.)(37.(38.R4.)(19.&40.=))(;.$36.(39.(19.&40.=))))P,(7.(3.&40.)(3;.R7.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R8.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R9.)(3;.R9.#1.)Vcnt,)(;.(2.(3.&8.))R6.))P,(7.$3>.(3?.(3;.R:.#1.)(1?.&40.Vcnt,))$40.)P,(1<.+1.(1=.(1>.(3.&8.)R7.)))P,(1<.(1=.(1>.(3.&8.)R8.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.(3:.R;.)(1>.(3.&8.)R9.)))R9.)(49.(43.Vsegs,R>.R=.)R<.(4:.$4;.(45.(4<.(3.&8.)R:.)(11.(2:.(3.&40.)(2.(3.&8.)))(4=.(3.&40.)(2.(3.&8.))(3;.R>.#1.)R:.)(12.(2:.(3.&40.)(2.(3.&8.)))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.)))(4>.(22.(2.(3.&8.))$4.(21.(3:.R<.)(1>.(3.&8.)R:.)))R<.)(17.(3.&8.)$=.(23.(19.&40.=))R:.)))")
(* [comment removed for export] *).
Proof. apply (StreamSim.read0_ok_bytes cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_inv_cnt : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Px8,(3.&40.)Pmodel,$28.Pbuf,(3.&40.)Pw,(2.(3.&8.))Peff,$4;.Pmodel',$28.Pevs,(2.$=.)P,(7.$35.(1?.&40.R7.)+3?.)P,(7.(8.$36.)(37.(38.R7.)(19.&40.=))(;.$36.(39.(19.&40.=))))P,(7.(3.&40.)(3;.R:.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R;.#1.)R8.)P,(7.(3.&40.)(3;.R<.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R=.)R:.Vcnt,)(;.(2.(3.&8.))R9.))P,(7.$3>.(3?.R;.(1?.&40.Vcnt,))$40.)P,(49.(43.Vsegs,R?.R>.)R=.(4:.$4;.R:.R9.R8.))(0.(5.(7.$4.(3:.R>.)$1:.)(5.(7.$4;.R;.(45.(19.&40.=)(12.(2:.(3.&40.)(2.(3.&8.))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.))))(5.(7.$28.R:.R>.)(7.(2.$=.)R9.(12.$=.)))))(1.(2.(3.&8.))Lbs,(2.(3.&8.))(5.(1<.+1.(1=.(1>.(3.&8.)R1.)))(5.(1<.(1=.(1>.(3.&8.)R1.))(1?.&40.Vcnt,))(5.(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.(3:.R?.)(1>.(3.&8.)R1.)))R1.)(5.(7.$4;.R<.(45.(4<.(3.&8.)R1.)(11.(2:.(3.&40.)(2.(3.&8.)))(4=.(3.&40.)(2.(3.&8.))R>.R1.)(12.(2:.(3.&40.)(2.(3.&8.)))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.))))(5.(7.$28.R;.(4>.(22.(2.(3.&8.))$4.(21.(3:.R?.)(1>.(3.&8.)R1.)))R?.))(7.(2.$=.)R:.(17.(3.&8.)$=.(23.(19.&40.=))R1.)))))))))")
(* [comment removed for export] *).
Proof. apply (StreamSim.read0_ok_inv cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_no_err_cnt : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Px8,(3.&40.)Pmodel,$28.Pw,(2.(3.&8.))P,(7.$35.(1?.&40.R3.)+3?.)P,(7.(8.$36.)(37.(38.R3.)(19.&40.=))(;.$36.(39.(19.&40.=))))P,(7.(3.&40.)(3;.R6.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R7.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R8.)(3;.R8.#1.)Vcnt,)(;.(2.(3.&8.))R5.))P,(7.$3>.(3?.(3;.R9.#1.)(1?.&40.Vcnt,))$40.)(4?.(49.(43.Vsegs,R:.R9.)R8.(50.$4;.)))")
(* [comment removed for export] *).
Proof. apply (StreamSim.read0_no_unmodeled cnt Hcnt). Qed.

#[using="Hcnt"] Lemma sstep_read_inv_cnt : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pms,$24.Pmodel,$28.Pbuf,(3.&40.)Px8,(3.&40.)Pw,(2.(3.&8.))Pevs,(2.$=.)Pst,$51.P,(7.(8.(3.&40.))(29.R6.)(13.(3.&40.)))P,(7.(2.(2:.(3.&40.)(3.&40.)))(2;.R7.)(12.(2:.(3.&40.)(3.&40.))))P,(7.(8.$36.)(37.(38.R8.)(19.&40.=))(;.$36.(39.(19.&40.=))))P,(7.(8.(3.&40.))(52.R:.)(;.(3.&40.)R7.))P,(7.$35.(1?.&40.R8.)+3?.)P,(7.(3.&40.)(3;.R<.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R=.#1.)R;.)P,(7.(3.&40.)(3;.R>.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R?.)R=.Vcnt,)(;.(2.(3.&8.))R;.))P,(7.$3>.(3?.R>.(1?.&40.Vcnt,))$40.)P,(53.Vsegs,(2?.R11.R10.)R<.R;.)(0.(5.(7.$4.(3:.R11.)$1:.)(5.(7.(2.$=.)R=.(12.$=.))(7.$51.R<.(54.(2?.(55.(56.R12.(19.&40.=)))R11.)))))(1.(2.(3.&8.))Lbs,(2.(3.&8.))(5.(1<.+1.(1=.(1>.(3.&8.)R1.)))(5.(1<.(1=.(1>.(3.&8.)R1.))(1?.&40.Vcnt,))(5.(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.(3:.R12.)(1>.(3.&8.)R1.)))R1.)(5.(7.(2.$=.)R>.(17.(3.&8.)$=.(23.(19.&40.=))R1.))(7.$51.R=.(54.(2?.(55.(57.R13.(45.(4<.(3.&8.)R1.)(11.(2:.(3.&40.)(2.(3.&8.)))(4=.(3.&40.)(2.(3.&8.))R11.R1.)(12.(2:.(3.&40.)(2.(3.&8.)))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.)))))(4>.(22.(2.(3.&8.))$4.(21.(3:.R12.)(1>.(3.&8.)R1.)))R12.))))))))))")
(* [comment removed for export] *).
Proof. apply (StreamSim.sstep_read_inv cnt Hcnt). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Hcnt"] Lemma drain_read_step : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pbs,(2.(3.&8.))Pms,$24.Pmodel,$28.Pbuf,(3.&40.)Px8,(3.&40.)Pw,(2.(3.&8.))P,(58.R4.)P,(7.(8.(3.&40.))(52.R6.)(;.(3.&40.)R3.))P,(7.$35.(1?.&40.R4.)+3?.)P,(7.(3.&40.)(3;.R8.#0.)(19.&40.=))P,(7.(3.&40.)(3;.R9.#1.)R7.)P,(7.(3.&40.)(3;.R:.#2.)Vcnt,)P,(7.(8.(2.(3.&8.)))(3<.(3=.Vsegs,R;.)R9.Vcnt,)(;.(2.(3.&8.))R7.))P,(7.$3>.(3?.R:.(1?.&40.Vcnt,))$40.)P,(1<.+1.(1=.(1>.(3.&8.)R>.)))P,(1<.(1=.(1>.(3.&8.)R?.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.(3:.R>.)(1>.(3.&8.)R10.)))R10.)(53.Vsegs,(2?.R10.R?.)(17.(3.&8.)$=.(23.(19.&40.=))R11.)(54.(2?.(55.(57.R10.(45.(4<.(3.&8.)R11.)(11.(2:.(3.&40.)(2.(3.&8.)))(4=.(3.&40.)(2.(3.&8.))R>.R11.)(12.(2:.(3.&40.)(2.(3.&8.)))))(12.(2:.(3.&40.)(3.&40.)))(12.(2:.(3.&40.)(3.&40.)))(12.$46.)(12.(2:.(3.&40.)$47.)))))(4>.(22.(2.(3.&8.))$4.(21.(3:.R?.)(1>.(3.&8.)R11.)))R?.))))")
(* [comment removed for export] *).
Proof.
  intros bs ms model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi Hpre.
  pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  apply (sstep_syscall segs ms model x8
           (mkEffect (len_word bs) [(buf, bs)] [])
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (map (ReadEv (Z_to_bv 64 0)) bs));
    [exact Hh | exact Hsvc | | exact Hh |].
  - rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
    apply read0_ok_bytes_cnt with (w := w); assumption.
  - rewrite (materialize_model_accesses_no_lazy _ _).
    + reflexivity.
    + rewrite m_vm_lazy_with_stdin. exact Hlazy.
Qed.

#[using="Hcnt H_LH"] Lemma drain_star_admits_ok : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Ps,$4.Pblocks,(2.(2.(3.&8.)))Ps',$4.P,(6.Vcnt,R3.R2.R1.)Pa,VA,Pa',VA,Pms,$24.Pmodel,$28.P,(58.R1.)P,(7.$4.(3:.R2.)R9.)P,(2<.R6.R4.)P,(7.(8.VA,)(9.VA,Vf,R7.(:.(3.&8.)R:.))(;.VA,R6.))(1.$33.Lc,$33.(2>.Vsegs,(2?.R7.R6.)(>.$=.(59.R<.)(5:.VA,Vout,R;.R8.(34.R6.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' ms model HM Hst Hrd Hp;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    unfold reads, reads_ch. cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* [comment removed for export] *)
      destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & _).
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok.
          exact (read0_ok_eof_cnt msR x8 model w Hno Hfd0 Hst Hg0 Hg2 Hw
                   Haok).
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      destruct (to_out_star_admits (out a) _ model Hfd1 Hh Hlazy Hout Hobm) as [c Hstar2].
      exists c. cbn [out_tail].
      replace (map (WriteEv (Z_to_bv 64 1)) (out a)
                 ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
        with (([] : list event)
                ++ ([] ++ (map (WriteEv (Z_to_bv 64 1)) (out a)
                             ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])))
        by reflexivity.
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* [comment removed for export] *)
      cbn [out_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* [comment removed for export] *)
    cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' advB model' HM' Hst' Hrd1 Hp) as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads blocks ++ out_tail out s'' a' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads blocks ++ out_tail out s'' a' (m_fs model))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

#[using="Hcnt Hec H_LH"] Lemma drain_star_admits_err : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Ps,$4.Pblocks,(2.(2.(3.&8.)))Ps1,$4.P,(6.Vcnt,R3.R2.R1.)Pa,VA,Pa',VA,PbsE,(2.(3.&8.))Pms,$24.Pmodel,$28.P,(58.R1.)P,(7.$4.(3:.R2.)R:.)P,(2<.R7.R4.)P,(7.(8.VA,)(9.VA,Vf,R8.(:.(3.&8.)R;.))(;.VA,R7.))P,(1<.+1.(1=.(1>.(3.&8.)R7.)))P,(1<.(1=.(1>.(3.&8.)R8.))(1?.&40.Vcnt,))P,(7.(2.(3.&8.))(20.(2.(3.&8.))$4.(21.R=.(1>.(3.&8.)R9.)))R9.)P,(7.(8.VA,)(9.VA,Vf,R;.R:.)(13.VA,))(1.$33.Lc,$33.(2>.Vsegs,(2?.R;.R:.)(>.$=.(59.(>.(2.(3.&8.))R11.(11.(2.(3.&8.))R<.(12.(2.(3.&8.))))))(11.$=.(14.Vec,(34.R:.))(12.$=.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros s blocks s1 HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bsE HloE HhiE) as Hcont.
    rewrite Hn in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bsE) [(buf, bsE)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bsE))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (Hlazy' : m_vm_lazy model' = [])
      by (unfold model'; rewrite m_vm_lazy_with_stdin; exact Hlazy).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bsE)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bsE msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                HloE HhiE); rewrite Hst; exact HpreE. }
    destruct (to_exit_star_admits segs ec advB model' Hh' Hlazy' Hcont) as [c Hstar2].
    rewrite land_255_small in Hstar2 by exact Hec.
    change (m_fs model') with (m_fs model) in Hstar2.
    exists c.
    cbn [app]. unfold reads, reads_ch. cbn [flat_map]. rewrite app_nil_r.
    replace (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)]))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar2].
  - cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' bsE advB model' HM' Hst' Hrd1 Hp HloE HhiE HpreE Hn)
      as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt Hec H_LH"] Lemma star_drain_only : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pc0,$33.Ptr,(2.$=.)Pc',$33.P,(2>.Vsegs,R3.R2.R1.)Pa,VA,Pms,$24.Pmodel,$28.P,(7.$33.R7.(2?.R2.R1.))P,(58.R2.)P,(2<.R5.R4.)(5;.VA,Vcnt,Vf,Vout,Vec,R6.(34.R4.)(3:.R4.)R9.)")
(* [comment removed for export] *).
Proof.
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros a ms model Heq HM Hrd; subst.
  - apply drain_from_nil.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms' Hsvc Hstep Hrd'].
    + (* [comment removed for export] *)
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs (SNext c2)
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * (* [comment removed for export] *)
        pose proof (to_out_star_only (out a) _ model Hfd1 Hh Hlazy Hout Hobm
                      tr2 c3 Hstar) as Hpref.
        cbn [app]. rewrite Hs. apply drain_from_out. exact Hpref.
      * (* [comment removed for export] *)
        pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
           apply drain_from_block with (a1 := a1);
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           exact (IH a1 _ _ eq_refl (M_loop_take (length bs) model HM) Hrd1).
        -- apply drain_from_err;
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           destruct (to_exit_star_only segs ec _
                       (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                                   model) Hh ltac:(rewrite m_vm_lazy_with_stdin; exact Hlazy)
                       Hcont tr2 c3 Hstar)
             as [-> | ->].
           ++ apply is_prefix_nil.
           ++ change (m_fs (with_stdin
                              (snd (stream_take (m_stdin model) (length bs)))
                              model)) with (m_fs model).
              rewrite land_255_small by exact Hec. apply is_prefix_refl.
    + (* [comment removed for export] *)
      destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                  Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
      subst evs. inversion Hc2; subst c2. cbn [app].
      exact (IH a _ model eq_refl HM Hrd').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dinv (c : config) : Prop := ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "(0.(5.(58.(5<.O1.))(1.VA,La,VA,(2<.R1.(5=.O1.))))(0.(5.(31.(5<.O1.))(5.(7.(8.(3.&40.))(29.(5<.O1.))(13.(3.&40.)))(5.(7.(2.(2:.(3.&40.)(3.&40.)))(2;.(5<.O1.))(12.(2:.(3.&40.)(3.&40.))))(1.(2.(3.&8.))Lrest,(2.(3.&8.))(5.(32.R1.)(26.Vsegs,(19.&40.+1.)(5=.O1.)R1.(27.Vsegs,(19.&40.=))))))))(0.(5>.Vsegs,(19.&40.=)O1.)(5>.Vsegs,Vec,O1.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma wall_out_dinv_step : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Prest,(2.(3.&8.))Pms,$24.Pmodel,$28.Pevs,(2.$=.)Pms',$24.Pmodel',$28.P,(31.R4.)P,(7.(8.(3.&40.))(29.R5.)(13.(3.&40.)))P,(7.(2.(2:.(3.&40.)(3.&40.)))(2;.R6.)(12.(2:.(3.&40.)(3.&40.))))P,(32.R9.)P,(26.Vsegs,(19.&40.+1.)R9.R:.(27.Vsegs,(19.&40.=)))P,(53.Vsegs,(2?.R:.R9.)R8.(54.(2?.R7.R6.)))(5?.(2?.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss.
  assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
    by (apply fd1chan_fdchan; exact Hfd1).
  revert Hbm.
  inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                  | msS msS' restS kS HsvcS HstepS Ht']; subst; intro Hbm.
  - (* [comment removed for export] *)
    right. right. left.
    apply (on_path_step segs (Z_to_bv 64 0) (mkCfg ms model) evs); [|exact Hss].
    left. repeat split; assumption.
  - (* [comment removed for export] *)
    destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                ms rest _ model evs (SNext (mkCfg ms' model'))
                Hh Hlazy Hfdc Hbm Hwl Hss) as (n & Hn1 & Hn2 & _ & Hc2 & Ht2).
    inversion Hc2; subst.
    right. left. cbn. repeat split; try assumption.
    exists (skipn n rest).
    split; [apply buf_modeled_skipn; exact Hbm | exact Ht2].
  - (* [comment removed for export] *)
    destruct (sstep_instr_inv segs ms model msS' evs (SNext (mkCfg ms' model'))
                Hlazy HsvcS HstepS Hss) as [_ Hc2].
    inversion Hc2; subst.
    right. left. cbn. repeat split; try assumption.
    exists rest. split; [exact Hbm | exact Ht'].
Qed.
#[using="Hcnt H_LH"] Lemma dinv_step : forall c evs c',
  dinv c -> sstep segs c evs (SNext c') -> dinv c'.
Proof.
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs
                  (SNext (mkCfg ms' model'))
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * right. left. cbn. repeat split; try assumption.
        exists (out a).
        split; [exact Hobm | exact (to_out_wall_tail _ _ Hout)].
      * pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           left. cbn. split; [apply M_loop_take; exact HM|].
           exists a1. exact (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)).
        -- right. right. right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hcont].
    + destruct (sstep_instr_inv segs ms model ms1 evs
                  (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
      inversion Hc2; subst.
      left. cbn. split; [exact HM |]. exists a. exact Hrd'.
  - exact (wall_out_dinv_step rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss).
  - right. right. left. eapply on_path_step; eauto.
  - right. right. right. eapply on_path_step; eauto.
Qed.

#[using="Hcnt"] Lemma dinv_no_error : forall c evs, dinv c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs SError
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
    + destruct (sstep_instr_inv segs ms model ms1 evs SError
                  Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
  - assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                    | msS msS' restS kS HsvcS HstepS Ht']; subst.
    + eapply (on_path_no_error segs (Z_to_bv 64 0) (mkCfg ms model));
        [left; repeat split; assumption | exact Hss].
    + exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               ms rest _ model evs Hh Hlazy Hfdc Hbm Hwl Hss).
    + destruct (sstep_instr_inv segs ms model msS' evs SError
                  Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
  - eapply on_path_no_error; eauto.
Qed.

#[using="Hcnt H_LH"] Lemma star_dinv : forall c tr c', dinv c -> star segs c tr c' -> dinv c'.
Proof. exact (star_inv segs dinv dinv_step). Qed.

#[using="Hcnt H_LH"] Lemma to_rd_no_error : forall a ms model,
  M_loop model -> to_rd a ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
  intros a ms model HM Hrd.
  apply (inv_no_reaches_error segs dinv dinv_step dinv_no_error).
  left; cbn; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt Hec H_LH"] Lemma drain_obs_iff : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Ppc,$60.Pph,$61.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$62.Plim,$35.Pinp,$63.Pa0,VA,P,(2<.R1.(64.Vsegs,R9.R8.R7.R4.(65.R2.)(66.R2.)(67.R2.)(68.R2.)))Ptr,(2.$=.)(69.(6:.Vsegs,(6;.Vsegs,R;.R:.R9.R8.R7.R6.R5.R4.)R1.)(5;.VA,Vcnt,Vf,Vout,Vec,R3.(6<.R4.)(6=.R4.)R1.))")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
  set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    pose proof (star_drain_only _ _ _ Hstar a0 ms0 model0 eq_refl HM0 Hrd) as Hd.
    rewrite Hst0, Hfs0 in Hd.
    eapply drain_from_prefix; eauto.
  - intros [ (blocks & s' & a' & HC & Hp & Hpref)
           | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
    + destruct (drain_star_admits_ok _ blocks s' HC a0 a' ms0 model0
                  HM0 Hst0 Hrd Hp) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
    + destruct (chunks_split _ blocks [bsE] _ _ HC) as (s1 & HC1 & HC2).
      destruct (chunks_single_inv _ _ _ _ HC2) as (HloE & HhiE & HpreE & _).
      destruct (drain_star_admits_err _ blocks s1 HC1 a0 a' bsE ms0 model0
                  HM0 Hst0 Hrd Hp HloE HhiE HpreE Hn) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
Qed.

#[using="Hcnt H_LH"] Lemma drain_no_error : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Ppc,$60.Pph,$61.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$62.Plim,$35.Pinp,$63.Pa0,VA,P,(2<.R1.(64.Vsegs,R9.R8.R7.R4.(65.R2.)(66.R2.)(67.R2.)(68.R2.)))(4?.(6>.Vsegs,(6;.Vsegs,R:.R9.R8.R7.R6.R5.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd.
  apply (to_rd_no_error a0); [apply init_M_loop | exact Hrd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma to_rd_coexec : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Pa,VA,Pms,$24.Pmodel,$28.P,(58.R1.)P,(2<.R4.R3.)(6?.Vsegs,(2?.R4.R3.)$70.)")
(* [comment removed for export] *).
Proof.
  intros a ms model HM Hrd.
  apply (inv_coexec segs dinv dinv_step dinv_no_error).
  left; cbn. split; [exact HM | exists a; exact Hrd].
Qed.

#[using="Hcnt H_LH"] Lemma drain_omni_corun : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Ppc,$60.Pph,$61.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$62.Plim,$35.Pinp,$63.Pa0,VA,P,(2<.R1.(64.Vsegs,R9.R8.R7.R4.(65.R2.)(66.R2.)(67.R2.)(68.R2.)))(71.(72.Vsegs,R:.R9.)R4.(73.R8.R7.R6.R5.)R3.$70.)")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_corun]. unfold init_config.
  apply (to_rd_coexec a0); [apply init_M_loop | exact Hrd].
Qed.

#[using="Hcnt Hec H_LH"] Lemma drain_omni_cosafe : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "Ppc,$60.Pph,$61.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$62.Plim,$35.Pinp,$63.Pa0,VA,P,(2<.R1.(64.Vsegs,R9.R8.R7.R4.(65.R2.)(66.R2.)(67.R2.)(68.R2.)))(74.(72.Vsegs,R:.R9.)R4.(73.R8.R7.R6.R5.)R3.(5;.VA,Vcnt,Vf,Vout,Vec,R2.(6<.R3.)(6=.R3.)))")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_cosafe].
  apply cosafe_obs_iff.
  - (* [comment removed for export] *)
    intros t t' Ht Hp.
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd).
    eapply obs_trace_prefix_closed; [| exact Hp].
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Ht.
  - intros tr Hobs. apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Hobs.
Qed.

End Drain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma drain_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "PA,StPcnt,(3.&40.)Pf,P,R2.P,(3.&8.)(8.R4.)Pout,P,R3.(2.(3.&8.))Pec,(3.&40.)Pa0,R5.Psource_segs,(2.$75.)PrLH,Px,R7.Px0,$24.SpPrpc,$60.Prph,$61.Prsp,(3.&40.)Prbrk,(3.&40.)Prmb,(3.&40.)Prrnd,$62.Ptarget_segs,(2.$75.)PaLH,Px,R?.Px0,$24.SpPapc,$60.Paph,$61.Pasp,(3.&40.)Pabrk,(3.&40.)Pamb,(3.&40.)Parnd,$62.Pinp,$63.P,(76.(1?.&40.R13.)+100.)P,(5.(76.=(1?.&40.R17.))(1<.(1?.&40.R17.)$77.))P,Pa,R19.Pms,$24.P,A2.R14.R2.R1.(78.R1<.R16.R1;.R1:.R19.R18.R15.R3.R2.)P,Pa,R1:.Pms,$24.P,A2.R=.R2.R1.(78.R1=.R?.R1<.R1;.R1:.R19.R>.R3.R2.)P,(78.R1;.R15.R1:.R19.R18.R17.R14.R16.(64.R15.R13.R12.R11.R>.(65.R5.)(66.R5.)(67.R5.)(68.R5.)))P,(78.R1<.R>.R1;.R1:.R19.R18.R=.R17.(64.R>.R<.R;.R:.R7.(65.R6.)(66.R6.)(67.R6.)(68.R6.)))(79.(72.R17.R15.R14.)(72.R?.R=.R<.)(73.R13.R12.R11.R10.)(73.R;.R:.R9.R8.)R7.)")
(* [comment removed for export] *).
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp Hec Hcnt HrLH HaLH Hr Ha.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (drain_omni_corun source_segs cnt Hcnt f out ec rLH HrLH
                rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr tr).
    rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha tr).
    reflexivity.
  - exact (drain_omni_corun target_segs cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha).
Qed.

Lemma drain_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_DrainSim ()) "PA,StPcnt,(3.&40.)Pf,P,R2.P,(3.&8.)(8.R4.)Pout,P,R3.(2.(3.&8.))Pec,(3.&40.)Pa0,R5.Psource_segs,(2.$75.)PrLH,Px,R7.Px0,$24.SpPrpc,$60.Prph,$61.Prsp,(3.&40.)Prbrk,(3.&40.)Prmb,(3.&40.)Prrnd,$62.Prlim,$35.Ptarget_segs,(2.$75.)PaLH,Px,R10.Px0,$24.SpPapc,$60.Paph,$61.Pasp,(3.&40.)Pabrk,(3.&40.)Pamb,(3.&40.)Parnd,$62.Palim,$35.Pinp,$63.P,(76.(1?.&40.R15.)+100.)P,(5.(76.=(1?.&40.R19.))(1<.(1?.&40.R19.)$77.))P,Pa,R1;.Pms,$24.P,A2.R16.R2.R1.(78.R1>.R18.R1=.R1<.R1;.R1:.R17.R3.R2.)P,Pa,R1<.Pms,$24.P,A2.R>.R2.R1.(78.R1?.R10.R1>.R1=.R1<.R1;.R?.R3.R2.)P,(78.R1=.R17.R1<.R1;.R1:.R19.R16.R18.(64.R17.R15.R14.R13.R10.(65.R5.)(66.R5.)(67.R5.)(68.R5.)))P,(78.R1>.R?.R1=.R1<.R1;.R1:.R>.R19.(64.R?.R=.R<.R;.R8.(65.R6.)(66.R6.)(67.R6.)(68.R6.)))(5.(7:.(7;.(72.R19.R17.R16.)R11.(73.R15.R14.R13.R12.)R7.))(7<.(7;.(72.R19.R17.R16.)R11.(73.R15.R14.R13.R12.)R7.)(7;.(72.R10.R>.R=.)R8.(73.R<.R;.R:.R9.)R7.)))")
(* [comment removed for export] *).
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp Hec Hcnt HrLH HaLH Hr Ha.
  split.
  { apply no_error_run_modeled.
    apply (drain_no_error source_segs cnt Hcnt f out ec rLH HrLH
             rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr). }
  right. split.
  - intro tr. cbn.
    rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr tr).
    rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd alim inp a0 Ha tr).
    reflexivity.
  - cbn.
    apply (drain_no_error target_segs cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd alim inp a0 Ha).
Qed.
