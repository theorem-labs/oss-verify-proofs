(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim CatSim PropExec SeqExec CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_WallSim () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "Corelib.Lists.ListDef.firstn"; "OSSVerify.KrLib.ABoot.PropExec.v_add"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.ABoot.PropExec.v_sub"; "Corelib.Lists.ListDef.skipn"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.ABoot.CatSim.fdchan"; "OSSVerify.KrLib.ABoot.CatSim.buf_modeled"; "WithFP1.WithSegsCh.to_wall"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "WithFP1.WithSegsCh.to_wall_tail"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Run.SError"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.Riscv.Sem.reg_get"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "WithFP1.WithSegsCh.to_wallexit"; "Corelib.Lists.ListDef.Forall"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.post"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exec"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.outcome"; "OSSVerify.KrLib.ABoot.CatSim.to_wexit"; "Corelib.Init.Datatypes.cons"; "LinuxProcessSemantics.LinuxProcessSem.State.ExitEv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exits_with"; "OSSVerify.KrLib.ABoot.CatSim.bufs_modeled"; "OSSVerify.KrLib.ABoot.CatSim.wevents_ch"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.cosafe"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.fd32"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "WithFP1.to_wallexit"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"].

Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
#[using="Type"] Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l H. unfold len_word. apply Z_to_bv_small.
  unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma len_word_firstn_nat : forall n (bs : list byte),
  (n <= length bs)%nat ->
  len_word (firstn n bs) = nat_to_word n.
Proof.
  intros n bs Hn. unfold len_word, nat_to_word.
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

#[using="Type"] Lemma u_len_word_firstn : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pn,$0.Pbs,(1.(2.&8.))P,(3.R2.(4.(2.&8.)R1.))P,(5.(6.(4.(2.&8.)R2.))(7.+2.+40.))(8.$9.(:.&40.(;.(2.&8.)(<.(2.&8.)R4.R3.)))(6.R4.))")
(* [comment removed for export] *).
Proof.
  intros n bs Hn Hlen.
  rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
                                unfold two_pow_64; lia).
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_add_len_firstn : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pp,(2.&40.)Pn,$0.Pbs,(1.(2.&8.))P,(3.R2.(4.(2.&8.)R1.))(8.(2.&40.)(=.R4.(;.(2.&8.)(<.(2.&8.)R3.R2.)))(>.&40.R4.(?.R3.)))")
(* [comment removed for export] *).
Proof.
  intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
  unfold v_add. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_add_len_firstn_Z : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pp,(2.&40.)Pn,$0.Pbs,(1.(2.&8.))P,(3.R2.(4.(2.&8.)R1.))P,(5.(6.(4.(2.&8.)R2.))(7.+2.+40.))(8.(2.&40.)(=.R5.(;.(2.&8.)(<.(2.&8.)R4.R3.)))(10.&40.(11.(:.&40.R5.)(6.R4.))))")
(* [comment removed for export] *).
Proof.
  intros p n bs Hn Hlen. unfold v_add.
  rewrite u_len_word_firstn by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_nat_Z : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pp,(2.&40.)Pk,$0.P,(5.(6.R1.)(7.+2.+40.))(8.(2.&40.)(>.&40.R3.(?.R2.))(10.&40.(11.(:.&40.R3.)(6.R2.))))")
(* [comment removed for export] *).
Proof.
  intros p k Hk. apply bv_eq.
  rewrite bv_add_unsigned. unfold nat_to_word.
  rewrite Z_to_bv_small
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_sub_len_firstn : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pn,$0.Pbs,(1.(2.&8.))P,(3.R2.(4.(2.&8.)R1.))P,(5.(6.(4.(2.&8.)R2.))(7.+2.+40.))(8.(2.&40.)(12.(;.(2.&8.)R3.)(;.(2.&8.)(<.(2.&8.)R4.R3.)))(;.(2.&8.)(13.(2.&8.)R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros n bs Hn Hlen. apply bv_eq.
  rewrite v_sub_small
    by (rewrite u_len_word_firstn by assumption;
        rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
  rewrite u_len_word_firstn by assumption.
  rewrite !len_word_unsigned
    by (unfold two_pow_64; rewrite ?length_skipn; lia).
  rewrite length_skipn. lia.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_to_wall_tail : forall ms ms' rest k,
  msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
  intros ms ms' rest k H; induction H; [auto|].
  intro Hw. eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wall_tail_nil_msteps : forall ms k,
  to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
  intros ms k H.
  remember ([] : list byte) as rest eqn:Hrest.
  induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
  - exists ms. split; [apply mst_refl | exact Hk].
  - subst rest. cbn in Hnb. lia.
  - destruct (IH Hrest) as (ms'' & Hm & Hk).
    exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma sstep_to_wall_inv : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpPmodel,$15.Pevs,(1.$16.)Pst,$17.P,(8.(18.(2.&40.))(19.R3.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R4.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R5.)P,(1?.R8.)P,(20.R:.R9.R8.)P,(21.Vsegs,(22.R;.R8.)R7.R6.)(23.$0.Ln,$0.(24.(3.#1.R1.)(24.(3.R1.(4.(2.&8.)R<.))(24.(8.(1.$16.)R9.(25.(2.&8.)$16.(26.Vch,)(<.(2.&8.)R1.R<.)))(24.(8.$17.R8.(27.(22.(28.(29.R=.(;.(2.&8.)(<.(2.&8.)R1.R<.))))R:.)))(2:.(28.(29.R=.(;.(2.&8.)(<.(2.&8.)R1.R<.))))(13.(2.&8.)R1.R<.)R;.))))))")
(* [comment removed for export] *).
Proof.
  intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
  revert Hbm.
  destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont]. intro Hbm.
  destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
              Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
  exists n. repeat split; try assumption.
  apply (Hcont n Hn1 Hn2).
Qed.

#[using="Hfd32"] Lemma to_wall_no_error_sstep : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpPmodel,$15.Pevs,(1.$16.)P,(8.(18.(2.&40.))(19.R2.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R3.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R4.)P,(1?.R7.)P,(20.R9.R8.R7.)(2;.(21.Vsegs,(22.R:.R7.)R6.$2<.))")
(* [comment removed for export] *).
Proof.
  intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
  destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
    as (n & _ & _ & _ & Hst & _).
  discriminate Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wall_star_admits_mut : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pmodel,$15.Ptr_k,(1.$16.)P,(8.(18.(2.&40.))(19.R2.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R3.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R4.)(24.Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(20.R3.R2.R1.)P,(1?.R3.)P,Pms',$14.P,A1.R4.R1.(23.$2=.Lc,$2=.(2>.Vsegs,(22.R3.R=.)R<.R1.))(23.$2=.Lc,$2=.(2>.Vsegs,(22.R7.R<.)(2?.$16.(25.(2.&8.)$16.(26.Vch,)R6.)R;.)R1.))Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(2:.R3.R2.R1.)P,(1?.R3.)P,Pms',$14.P,A1.R4.R1.(23.$2=.Lc,$2=.(2>.Vsegs,(22.R3.R=.)R<.R1.))(23.$2=.Lc,$2=.(2>.Vsegs,(22.R7.R<.)(2?.$16.(25.(2.&8.)$16.(26.Vch,)R6.)R;.)R1.)))")
(* [comment removed for export] *).
Proof.
  intros model tr_k Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
  - (* [comment removed for export] *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm Hk.
    destruct (IH (length rest) Hnb (Nat.le_refl _)
                (buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (map (WriteEv ch) (firstn (length rest) rest)
              ++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
      by (rewrite firstn_all, skipn_all; reflexivity).
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn (length rest) rest))
                  [(ms_gpr ms 1, length rest)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, length rest)]
                (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
             (map (WriteEv ch) (firstn (length rest) rest)));
      [exact Hh | exact Hsvc | | exact Hh |].
    eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
    rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* [comment removed for export] *)
    intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
  - (* [comment removed for export] *)
    intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
  - (* [comment removed for export] *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
    destruct (IH Hbm Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Hfd32"] Lemma to_wall_star_admits : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(20.R3.R2.R1.)P,(1?.R3.)Pmodel,$15.Ptr_k,(1.$16.)P,(8.(18.(2.&40.))(19.R2.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R3.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R4.)P,Pms',$14.P,A1.R9.R1.(23.$2=.Lc,$2=.(2>.Vsegs,(22.R3.R8.)R7.R1.))(23.$2=.Lc,$2=.(2>.Vsegs,(22.R<.R7.)(2?.$16.(25.(2.&8.)$16.(26.Vch,)R;.)R6.)R1.))")
(* [comment removed for export] *).
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

#[using="Hfd32"] Lemma to_wall_tail_star_admits : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(2:.R3.R2.R1.)P,(1?.R3.)Pmodel,$15.Ptr_k,(1.$16.)P,(8.(18.(2.&40.))(19.R2.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R3.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R4.)P,Pms',$14.P,A1.R9.R1.(23.$2=.Lc,$2=.(2>.Vsegs,(22.R3.R8.)R7.R1.))(23.$2=.Lc,$2=.(2>.Vsegs,(22.R<.R7.)(2?.$16.(25.(2.&8.)$16.(26.Vch,)R;.)R6.)R1.))")
(* [comment removed for export] *).
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wall_star_only_mut : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pmodel,$15.PT,(1.$16.)P,(8.(18.(2.&40.))(19.R2.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R3.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R4.)(24.Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(20.R3.R2.R1.)P,(1?.R3.)P,Pms',$14.Ptr,(1.$16.)Pc,$2=.P,A1.R6.R3.P,(2>.Vsegs,(22.R4.R>.)R3.R2.)(30.$16.R4.R>.)Ptr,(1.$16.)Pc,$2=.P,(2>.Vsegs,(22.R8.R=.)R2.R1.)(30.$16.R3.(2?.$16.(25.(2.&8.)$16.(26.Vch,)R8.)R=.))Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(2:.R3.R2.R1.)P,(1?.R3.)P,Pms',$14.Ptr,(1.$16.)Pc,$2=.P,A1.R6.R3.P,(2>.Vsegs,(22.R4.R>.)R3.R2.)(30.$16.R4.R>.)Ptr,(1.$16.)Pc,$2=.P,(2>.Vsegs,(22.R8.R=.)R2.R1.)(30.$16.R3.(2?.$16.(25.(2.&8.)$16.(26.Vch,)R8.)R=.)))")
(* [comment removed for export] *).
Proof.
  intros model T Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))).
  - (* [comment removed for export] *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
    subst evs. inversion Hc2; subst c2.
    pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
    rewrite <- (firstn_skipn n rest) at 2.
    rewrite map_app, <- app_assoc.
    apply is_prefix_app_mono. exact Hp.
  - (* [comment removed for export] *)
    intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
  - (* [comment removed for export] *)
    intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
  - (* [comment removed for export] *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
      as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm HK tr2 c Hstar2).
Qed.

#[using="Hfd32"] Lemma to_wall_star_only : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(20.R3.R2.R1.)P,(1?.R3.)Pmodel,$15.PT,(1.$16.)P,(8.(18.(2.&40.))(19.R2.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R3.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R4.)P,Pms',$14.Ptr,(1.$16.)Pc,$2=.P,A1.R;.R3.P,(2>.Vsegs,(22.R4.R9.)R3.R2.)(30.$16.R4.R9.)Ptr,(1.$16.)Pc,$2=.P,(2>.Vsegs,(22.R=.R8.)R2.R1.)(30.$16.R3.(2?.$16.(25.(2.&8.)$16.(26.Vch,)R=.)R8.))")
(* [comment removed for export] *).
Proof.
  intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
  exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma twl_write_rec : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pk,P,$14.SpPrest,(1.(2.&8.))Pregs,(31.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(18.(2.&8.))Prom,P,(2.&40.)(18.(2.&8.))P,(8.$9.(:.&40.(32.R4.(33.&5.+11.$34.)))+40.)P,(8.(2.&40.)(35.R5.(33.&5.+:.$34.))Vfd,)P,(8.(18.(1.(2.&8.)))(36.(37.R6.(38.Vfx,)R5.(39.(2.&40.)(32.R6.(33.&5.+11.$34.)))(1:.(2.&40.))(3:.Vfx,)R4.R3.)(35.R6.(33.&5.+;.$34.))(35.R6.(33.&5.+<.$34.)))(39.(1.(2.&8.))R7.))P,(3.#1.(4.(2.&8.)R8.))P,Pn,$0.P,(3.#1.R1.)P,(3.R2.(4.(2.&8.)R;.))(2:.(3;.Vfx,(3<.R;.(33.&5.+:.$34.)(;.(2.&8.)(<.(2.&8.)R3.R<.)))(3=.R:.+4.)R9.R8.)(13.(2.&8.)R3.R<.)R=.)(20.(37.R9.(38.Vfx,)R8.(39.(2.&40.)(32.R9.(33.&5.+11.$34.)))(1:.(2.&40.))(3:.Vfx,)R7.R6.)R:.R;.)")
(* [comment removed for export] *).
Proof.
  intros k rest regs pc mem rom H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  eapply twl_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wall_k_ex_mut : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "(24.Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(20.R3.R2.R1.)(23.$14.Lms',$14.A1.R3.R1.)Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(2:.R3.R2.R1.)(23.$14.Lms',$14.A1.R3.R1.))")
(* [comment removed for export] *).
Proof.
  apply (to_wall_mutind
           (fun ms rest k => exists ms', k ms')
           (fun ms rest k => exists ms', k ms')).
  - intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH.
    exact (IH (length rest) Hnb (Nat.le_refl _)).
  - intros ms k Hk. exists ms. exact Hk.
  - intros ms rest k Hnb Hw IH. exact IH.
  - intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.

#[using="Type"] Lemma to_wall_tail_k_ex : forall ms rest k,
  to_wall_tail ms rest k -> exists ms', k ms'.
Proof. exact (proj2 to_wall_k_ex_mut). Qed.

#[using="Type"] Lemma to_wallexit_bufs_nonempty : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pms,$14.P,(3>.R3.R2.R1.)(3?.(1.(2.&8.))Lb,(1.(2.&8.))(3.#1.(4.(2.&8.)R1.))R4.)")
(* [comment removed for export] *).
Proof.
  induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
  destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
  destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
  exact (IH code ms' Hk).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twe_step : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Pms',$14.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)P,(8.(18.(2.&40.))(40.R4.)(1:.(2.&40.)))P,(8.(41.$14.)(42.Vsegs,R5.)(43.$14.R4.))P,(3>.R4.R3.R5.)(3>.R5.R4.R7.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' bufs code Hsvc Hstep Hw.
  destruct bufs as [|buf rest].
  - eapply tw_step; eauto.
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply twt_step; eauto.
Qed.

#[using="Type"] Lemma msteps_to_wallexit : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Pms',$14.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)P,(44.Vsegs,R4.R3.)P,(3>.R3.R2.R4.)(3>.R4.R3.R6.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
  - exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply msteps_to_wall_tail; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wall_exec_mut : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pmodel,$15.PQ,$45.P,(8.(18.(2.&40.))(19.R2.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R3.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R4.)(24.Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(20.R3.R2.R1.)P,(1?.R3.)P,Pms',$14.P,A1.R4.R1.(46.Vsegs,(22.R2.R<.)R;.)(46.Vsegs,(22.R6.R;.)Ltr,(1.$16.)Lo,$47.(23.(1.$16.)Ltr',(1.$16.)(24.(8.(1.$16.)R3.(2?.$16.(25.(2.&8.)$16.(26.Vch,)R8.)R1.))A2.R=.R1.R2.)))Pms,$14.Prest,(1.(2.&8.))Pk,P,$14.SpP,(2:.R3.R2.R1.)P,(1?.R3.)P,Pms',$14.P,A1.R4.R1.(46.Vsegs,(22.R2.R<.)R;.)(46.Vsegs,(22.R6.R;.)Ltr,(1.$16.)Lo,$47.(23.(1.$16.)Ltr',(1.$16.)(24.(8.(1.$16.)R3.(2?.$16.(25.(2.&8.)$16.(26.Vch,)R8.)R1.))A2.R=.R1.R2.))))")
(* [comment removed for export] *).
Proof.
  intros model Q Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
  - (* [comment removed for export] *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK.
    assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
    apply exec_step; [exact Hh | | |].
    + (* [comment removed for export] *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv ch) (firstn (length rest) rest)));
        [exact Hh | exact Hsvc | | exact Hh |].
      * eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & _ & _ & _ & Habs & _).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & Hn1 & Hn2 & -> & Hc' & _).
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
      intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
      rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
  - (* [comment removed for export] *)
    intros ms k Hk Hbm HK.
    eapply exec_conseq; [exact (HK ms Hk) |].
    intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
  - (* [comment removed for export] *)
    intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
  - (* [comment removed for export] *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wexit_nil_exec_aux : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(48.Vsegs,R6.R5.R4.)P,(8.(1.(1.(2.&8.)))R6.(1=.(1.(2.&8.))))(46.Vsegs,(22.R8.R5.)Ltr,(1.$16.)Lo,$47.(24.(8.(1.$16.)R2.(49.$16.(4:.R8.(4;.R7.))(1=.$16.)))(4<.R8.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  intros ms bufs code model Hh Hlazy Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
  - apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * cbn beta. rewrite app_nil_r. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma to_wexit_nil_exec : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Pcode,(2.&40.)Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(48.Vsegs,R5.(1=.(1.(2.&8.)))R4.)(46.Vsegs,(22.R6.R4.)Ltr,(1.$16.)Lo,$47.(24.(8.(1.$16.)R2.(49.$16.(4:.R7.(4;.R6.))(1=.$16.)))(4<.R7.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  intros ms code model Hh Hlazy Hte.
  exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

(* [comment removed for export] *)
#[using="Hfd32"] Lemma to_wallexit_exec : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pms,$14.Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R3.)P,(4=.R7.)P,(3>.R8.R7.R6.)(46.Vsegs,(22.R7.R6.)Ltr,(1.$16.)Lo,$47.(24.(8.(1.$16.)R2.(2?.$16.(4>.Vch,R;.)(49.$16.(4:.R:.(4;.R8.))(1=.$16.))))(4<.R:.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
  - cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
  - destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq;
      [exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
                Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
    intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wallexit_star_admits : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pms,$14.Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R3.)P,(4=.R7.)P,(3>.R8.R7.R6.)(23.$2=.Lc,$2=.(2>.Vsegs,(22.R8.R7.)(2?.$16.(4>.Vch,R:.)(49.$16.(4:.R9.(4;.R7.))(1=.$16.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
#[using="Hfd32"] Lemma to_wallexit_no_other_exit : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pms,$14.Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R3.)P,(4=.R7.)P,(3>.R8.R7.R6.)Pcode',(2.&40.)P,(2;.(8.(2.&40.)R1.R9.))(2;.(46.Vsegs,(22.R9.R8.)(4<.R2.)))")
(* [comment removed for export] *).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne (eq_sym Hx')).
Qed.

#[using="Hfd32"] Lemma to_wallexit_trace_unique : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pms,$14.Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R3.)P,(4=.R7.)P,(3>.R8.R7.R6.)Ptr',(1.$16.)P,(2;.(8.(1.$16.)R1.(2?.$16.(4>.Vch,R:.)(49.$16.(4:.R9.(4;.R7.))(1=.$16.)))))(2;.(46.Vsegs,(22.R9.R8.)Ltr,(1.$16.)L,$47.(8.(1.$16.)R2.R4.)))")
(* [comment removed for export] *).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & o & Hm & Heq & _).
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
  apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.

#[using="Hfd32"] Lemma to_wallexit_not_silent : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pms,$14.Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R3.)P,(4=.R7.)P,(3>.R8.R7.R6.)(2;.(4?.Vsegs,(22.R7.R6.)Ltr,(1.$16.)(8.(1.$16.)R1.(1=.$16.))))")
(* [comment removed for export] *).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
  destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.

#[using="Hfd32"] Lemma to_wallexit_star_only : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pms,$14.Pmodel,$15.P,(8.(18.(2.&40.))(19.R1.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R2.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R3.)P,(4=.R7.)P,(3>.R8.R7.R6.)Ptr,(1.$16.)Pc,$2=.P,(2>.Vsegs,(22.R9.R8.)R2.R1.)(30.$16.R3.(2?.$16.(4>.Vch,R<.)(49.$16.(4:.R;.(4;.R9.))(1=.$16.))))")
(* [comment removed for export] *).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
    as (tr' & o & _ & HQ).
  cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wallexit_no_error : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pms,$14.Pmodel,$15.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)P,(8.(18.(2.&40.))(19.R3.)(1:.(2.&40.)))P,(8.(1.(1;.(2.&40.)(2.&40.)))(1<.R4.)(1=.(1;.(2.&40.)(2.&40.))))P,(1>.Vfd,Vch,R5.)P,(4=.R5.)P,(3>.R6.R5.R8.)(2;.(50.Vsegs,(22.R9.R8.)))")
(* [comment removed for export] *).
Proof.
  intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* [comment removed for export] *)
#[using="Type"] Lemma wevents_ch_fd1 : forall bufs,
  wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma wall_omni_run : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pfd,(2.&40.)Pch,(2.&40.)P,(8.(2.&40.)(51.R2.)R2.)Psegs,(1.$52.)Ppc,$53.Pph,$54.Psp,(2.&40.)Pbrk0,(2.&40.)Pmb,(2.&40.)Prnd,$55.Plim,$9.Pinp,$56.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)P,(1>.R>.R=.(57.(58.R;.)R7.R6.R8.R4.R3.))P,(4=.R3.)P,(59.R=.R10.R4.R3.(5:.R=.R<.R;.R:.R7.(5;.R5.)(5<.R5.)(5=.R5.)(5>.R5.)))(5?.(60.R>.R=.R<.)R7.(61.R;.R:.R9.R8.)R6.Ltr,(1.$16.)Lo,$47.(24.(8.(1.$16.)R2.(2?.$16.(4>.R12.R7.)(49.$16.(4:.R6.(62.R8.))(1=.$16.))))(4<.R6.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
  cbn [omni_run]. unfold init_config.
  exact (to_wallexit_exec segs fd ch Hfd32 bufs code _
           (init_model (segments_reserved segs) brk0 mb sp lim inp)
           eq_refl eq_refl Hfdc Hbm Hw).
Qed.

#[using="Type"] Lemma wall_obs_iff : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pfd,(2.&40.)Pch,(2.&40.)P,(8.(2.&40.)(51.R2.)R2.)Psegs,(1.$52.)Ppc,$53.Pph,$54.Psp,(2.&40.)Pbrk0,(2.&40.)Pmb,(2.&40.)Prnd,$55.Plim,$9.Pinp,$56.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)P,(1>.R>.R=.(57.(58.R;.)R7.R6.R8.R4.R3.))P,(4=.R3.)P,(59.R=.R10.R4.R3.(5:.R=.R<.R;.R:.R7.(5;.R5.)(5<.R5.)(5=.R5.)(5>.R5.)))Ptr,(1.$16.)(63.(64.R?.(65.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R1.)(30.$16.R1.(2?.$16.(4>.R11.R6.)(49.$16.(4:.R5.(62.R7.))(1=.$16.)))))")
(* [comment removed for export] *).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

#[using="Type"] Lemma wall_no_error_run : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Pfd,(2.&40.)Pch,(2.&40.)P,(8.(2.&40.)(51.R2.)R2.)Psegs,(1.$52.)Ppc,$53.Pph,$54.Psp,(2.&40.)Pbrk0,(2.&40.)Pmb,(2.&40.)Prnd,$55.Plim,$9.Pinp,$56.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)P,(1>.R>.R=.(57.(58.R;.)R7.R6.R8.R4.R3.))P,(4=.R3.)P,(59.R=.R10.R4.R3.(5:.R=.R<.R;.R:.R7.(5;.R5.)(5<.R5.)(5=.R5.)(5>.R5.)))(2;.(50.R>.(65.R>.R=.R<.R;.R:.R9.R8.R7.R6.)))")
(* [comment removed for export] *).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wall_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Psource_segs,(1.$52.)Prpc,$53.Prph,$54.Prsp,(2.&40.)Prbrk,(2.&40.)Prmb,(2.&40.)Prrnd,$55.Ptarget_segs,(1.$52.)Papc,$53.Paph,$54.Pasp,(2.&40.)Pabrk,(2.&40.)Pamb,(2.&40.)Parnd,$55.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pinp,$56.P,(59.R11.(10.&40.+1.)R3.R2.(5:.R11.R10.R?.R>.R;.(5;.R1.)(5<.R1.)(5=.R1.)(5>.R1.)))P,(59.R;.(10.&40.+1.)R4.R3.(5:.R;.R:.R9.R8.R5.(5;.R2.)(5<.R2.)(5=.R2.)(5>.R2.)))P,(4=.R5.)(66.(60.R14.R13.R12.)(60.R=.R<.R;.)(61.R11.R10.R?.R>.)(61.R:.R9.R8.R7.)R4.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
    by (split; reflexivity).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
    by (split; reflexivity).
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wall_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_WallSim ()) "Psource_segs,(1.$52.)Prpc,$53.Prph,$54.Prsp,(2.&40.)Prbrk,(2.&40.)Prmb,(2.&40.)Prrnd,$55.Prlim,$9.Ptarget_segs,(1.$52.)Papc,$53.Paph,$54.Pasp,(2.&40.)Pabrk,(2.&40.)Pamb,(2.&40.)Parnd,$55.Palim,$9.Pbufs,(1.(1.(2.&8.)))Pcode,(2.&40.)Pinp,$56.P,(59.R13.(10.&40.+1.)R3.R2.(5:.R13.R12.R11.R10.R=.(5;.R1.)(5<.R1.)(5=.R1.)(5>.R1.)))P,(59.R<.(10.&40.+1.)R4.R3.(5:.R<.R;.R:.R9.R6.(5;.R2.)(5<.R2.)(5=.R2.)(5>.R2.)))P,(4=.R5.)(24.(67.(68.(60.R16.R15.R14.)R?.(61.R13.R12.R11.R10.)R4.))(69.(68.(60.R16.R15.R14.)R?.(61.R13.R12.R11.R10.)R4.)(68.(60.R>.R=.R<.)R7.(61.R;.R:.R9.R8.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code inp Hsource Htarget Hbm.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp))
    by (split; reflexivity).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved target_segs) abrk amb asp alim inp))
    by (split; reflexivity).
  split.
  { apply no_error_run_modeled.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
             HfdS Hbm Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd alim inp bufs code
               HfdT Hbm Htarget tr).
    reflexivity.
  - cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd alim inp bufs code
             HfdT Hbm Htarget).
Qed.
End WithFP1.
