(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe Sim MPaths Harness Adapter Driver Stdio TargetSafe StepB EquivShared.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section More.
Context {StG StC : Type} (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Local Notation fsimeq := (fsimeq debtG debtC stepG).
End More.
Section More1.
Context {St : Type} (dG dC : St -> list event) (stepG : node -> Model -> resp -> Model -> list event -> Prop).
End More1.
Section TargetSim.
Context {St ptr : Type}.
Variables (debtG debtC : St -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Variable RX : list ptr -> rel St St.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable new_handler : M St Empty_set.
Variable emit : Z -> M St unit.
Local Notation fsimeq := (fsimeq debtG debtC stepG).
Hypothesis Hm : forall X n, 0 <= n ->
fsimeq (RX X) (raw_malloc n) (raw_malloc n)
(fun r => match r with Some p => fun sG moG sC moC => RX (p :: X) sG moG sC moC /\ n < 2^63 | None => RX X end).
Hypothesis Hf : forall X p, fsimeq (RX (p :: X)) (raw_free p) (raw_free p) (fun _ => RX X).
Hypothesis Hperm : forall X Y sG moG sC moC, Permutation X Y -> RX X sG moG sC moC -> RX Y sG moG sC moC.
Hypothesis Hleak : forall X Y sG moG sC moC, RX (Y ++ X) sG moG sC moC -> RX X sG moG sC moC.
Hypothesis Hnh : forall X (Q : Empty_set -> rel St St), fsimeq (RX X) new_handler new_handler Q.
Hypothesis Hemit : forall X v, fsimeq (RX X) (emit v) (emit v) (fun _ => RX X).
End TargetSim.
Section DriverSim.
Context {St ptr : Type}.
Variables (debtG debtC : St -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Variables (ioG ioC : IOStyle St).
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variables (rsG rsC : Z).
Variable alloc_init : Z -> M St unit.
Variables (runG runC : Z -> list Z -> M St Z).
Variable alloc_count : M St Z.
Variables (R0 R1 : list ptr -> rel St St).
Local Notation fsimeq := (fsimeq debtG debtC stepG).
Hypothesis H01 : forall X sG moG sC moC, R0 X sG moG sC moC -> R1 X sG moG sC moC.
Hypothesis Hdm0 : forall X n, 0 <= n ->
fsimeq (R0 X) (drv_malloc n) (drv_malloc n)
(fun r => match r with Some p => fun sG moG sC moC => R0 (p :: X) sG moG sC moC /\ n < 2^63 | None => R0 X end).
Hypothesis Hdf0 : forall X p, fsimeq (R0 (p :: X)) (drv_free p) (drv_free p) (fun _ => R0 X).
Hypothesis Hdf1 : forall X p, fsimeq (R1 (p :: X)) (drv_free p) (drv_free p) (fun _ => R1 X).
Hypothesis Hperm0 : forall X Y sG moG sC moC, Permutation X Y -> R0 X sG moG sC moC -> R0 Y sG moG sC moC.
Hypothesis Hdiag0 : forall X d, diag_short d -> fsimeq (R0 X) (io_diag ioG d) (io_diag ioC d) (fun _ => R0 X).
Hypothesis Hinit : forall X bm, fsimeq (R0 X) (alloc_init bm) (alloc_init bm) (fun _ => R0 X).
Hypothesis Hcount : forall X, fsimeq (R1 X) alloc_count alloc_count (fun _ => R1 X).
Hypothesis Hrun : forall X cfg payload, fsimeq (R1 X) (runG cfg payload) (runC cfg payload) (fun _ => R1 X).
Hypothesis Hopen : forall X path, fsimeq (R0 X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => R0 X).
Hypothesis Hclose : forall X fd, fsimeq (R0 X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => R0 X).
Hypothesis Hread : forall X fd bufG bufC cnt, 0 <= cnt < 2^64 ->
fsimeq (R0 X) (msys (NRead fd bufG cnt) (dec_read bufG cnt)) (msys (NRead fd bufC cnt) (dec_read bufC cnt))
(fun a => match a with RdData bs => fun sG moG sC moC => R0 X sG moG sC moC /\ zlength bs <= cnt | RdErr _ => R0 X end).
#[using="Type"] Lemma zlength_app' {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62102050378.32000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma zlength_u8s' : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.
End DriverSim.
Lemma with_fds_self : forall mo, with_fds (m_fds mo) mo = mo.
Proof. intros [[t p] ? ? ? ? ? ?]. reflexivity. Qed.
Lemma nstep_open_xfer : forall path moG rsp moG' evs moC,
nstep (NOpen path) moG rsp moG' evs -> m_fds moG = m_fds moC -> m_fs moG = m_fs moC ->
nstep (NOpen path) moC rsp (with_fds (m_fds moG') moC) evs /\ moG' = with_fds (m_fds moG') moG.
Proof.
intros path moG rsp moG' evs moC H Ef Es. cbn [nstep] in H |- *. destruct H as [-> H].
rewrite <- Es.
destruct (path_max <=? length path)%nat; [destruct H as [-> ->]; rewrite (with_fds_self moG), Ef, with_fds_self; repeat split; reflexivity|].
destruct path as [|c p]; [destruct H as [-> ->]; rewrite (with_fds_self moG), Ef, with_fds_self; repeat split; reflexivity|].
assert (OR : forall ent, open_result moG ent rsp moG' -> open_result moC ent rsp (with_fds (m_fds moG') moC) /\ moG' = with_fds (m_fds moG') moG).
{ intros ent [(e & He & -> & ->)|(Hlk & -> & ->)].
- rewrite (with_fds_self moG), Ef, with_fds_self. split; [left; exists e; auto| reflexivity].
- split; [right|reflexivity]. unfold open_result. rewrite !m_fds_with_fds, <- Ef. repeat split; auto. }
destruct (Open.path_is_dirref (c :: p)); [split; [split; [reflexivity| exact (proj1 (OR _ H))]| exact (proj2 (OR _ H))]|].
destruct (Fs.fs_lookup (m_fs moG) (c :: p)); [|destruct H as [-> ->]; rewrite (with_fds_self moG), Ef, with_fds_self; repeat split; reflexivity].
split; [split; [reflexivity| exact (proj1 (OR _ H))]| exact (proj2 (OR _ H))].
Qed.
Lemma nstep_close_xfer : forall fd moG rsp moG' evs moC,
nstep (NClose fd) moG rsp moG' evs -> m_fds moG = m_fds moC ->
nstep (NClose fd) moC rsp (with_fds (m_fds moG') moC) evs /\ moG' = with_fds (m_fds moG') moG.
Proof.
intros fd moG rsp moG' evs moC (-> & Hfd & H) Ef. cbn [nstep]. rewrite <- Ef.
destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)); destruct H as [-> ->]; rewrite ?m_fds_with_fds; [|rewrite (with_fds_self moG), Ef, with_fds_self]; repeat split; auto; lia.
Qed.
Lemma nstep_read_xfer : forall fd bufG bufC cnt moG rsp moG' evs moC,
nstep (NRead fd bufG cnt) moG rsp moG' evs -> m_fds moG = m_fds moC -> m_fs moG = m_fs moC ->
exists rspC, nstep (NRead fd bufC cnt) moC rspC (with_fds (m_fds moG') moC) evs /\ moG' = with_fds (m_fds moG') moG
/\ dec_read bufC cnt rspC = dec_read bufG cnt rsp.
Proof.
intros fd bufG bufC cnt moG rsp moG' evs moC [-> H] Ef Es. cbn [nstep]. rewrite <- Ef, <- Es.
destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id wr|dnr dnw| ]|].
- destruct H.
- destruct (Fs.fs_lookup (m_fs moG) p) as [data|]; [|destruct H]. destruct H as [-> ->].
eexists. split; [split; [reflexivity|]; split; [reflexivity| rewrite m_fds_with_fds; reflexivity]|]. split; [rewrite m_fds_with_fds; reflexivity|].
unfold dec_read. cbn. unfold Uaccess.delivered_writes. destruct (Fs.file_read data off (Z_to_bv 64 cnt)); cbn; [reflexivity|].
rewrite !bv_eqb_refl. reflexivity.
- destruct H.
- destruct H.
- destruct H.
- destruct H as [-> ->]. exists (efferr EISDIR). rewrite (with_fds_self moG), Ef, with_fds_self. repeat split; reflexivity.
- destruct H.
- destruct H.
- destruct H.
- destruct H.
- destruct H as [-> ->]. exists (efferr EBADF). rewrite (with_fds_self moG), Ef, with_fds_self. repeat split; reflexivity.
Qed.
Section FdNodes.
Context {St : Type} (debtG debtC : St -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Hypothesis stepG_sub : forall n mo r mo' e, ~ nf_node n -> stepG n mo r mo' e -> nstep n mo r mo' e.
Variable R : rel St St.
Local Notation fsimeq := (fsimeq debtG debtC stepG).
Hypothesis Rmodels : forall sG moG sC moC, R sG moG sC moC ->
minv moG /\ minv moC /\ m_halted moG = None /\ m_halted moC = None /\ m_fds moG = m_fds moC /\ m_fs moG = m_fs moC.
Hypothesis Rtables : forall sG moG sC moC moG' moC', R sG moG sC moC ->
m_vmmaps moG' = m_vmmaps moG -> m_vmmaps moC' = m_vmmaps moC ->
minv moG' -> minv moC' -> m_halted moG' = None -> m_halted moC' = None ->
m_fds moG' = m_fds moC' -> m_fs moG' = m_fs moC' -> R sG moG' sC moC'.
End FdNodes.
