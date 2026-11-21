(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (tpath_msys_mret, is_err_false_of_ceiling, ev_step_specP and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe MSafeP MPaths STree Malloc KInv KStep PState KLink KEv StepB MI_NN.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_KEvP () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths=tpath_msys_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec6MPaths>tpath_mbind_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths:tpath_mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP6mspecPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP;mspecP_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths:tpath_munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP:mspecP_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6MSafeP6nstepPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec5KStep;mmap_len_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP<mspec_mspecPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP:mspecP_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP@mspecP_pointwiseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP:mspecP_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MI_NN3okzC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4negbK59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps>dec_mmap_fixedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps9neg_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode=dec_mmap_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_mmapC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec4KInv9brk_quietC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec4KEvP?tpath_msys_mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB7nf_nodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6DecodeBdec_mmap_none_SomeC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib6Decode9efferr_ciC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<mmap_addr_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib3Lib6DecodeBerrno_of_errno_retC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib6DecodeAmmap_addr_ok_trueC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib6Decode6avoidsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec4KEvPGis_err_false_of_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode=dec_mmap_SomeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps?dec_mprotect_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<dec_mprotectC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib3Lib6Decode9range_ans01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6DecodeAdec_mprotect_SomeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps7ev_stepC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01I59OSSVerify5KrLib6Malloc8ProgDeps9fixed_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode8mmap_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv:cpath_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink8frame_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5KLink2KL00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink<ev_step_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv<ev_step_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink:KL_atop_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib4Spec4KEvP;ev_step_okzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP<mspecP_pathsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP;mspecP_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MI_NN2nnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps6membedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP=mspecP_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ctree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv5cpath00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv5cpath01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec4KEvP=ev_step_specPC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv5cpath02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4Spec3KEv?event_post_atopC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv3OWNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP:mspecP_getC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv6creach00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec<MI_ContractsFcmalloc_contract_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MI_NN:cmalloc_nnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec4KEvP<membed_specPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_Contracts;creach_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5set_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP;mspecP_upd'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv6creach02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes<vm_only_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv;KL_set_liveC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List5NoDup02C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtC59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps9fresh_offC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List4inclC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv=raw_free_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv?raw_malloc_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tpath_msys_mret {A B} : forall n (dec : resp -> option A) (g : A -> B) (s s' : PState) mo tr (b : B) mo',
  tpath nstepP (mbind (msys n dec) (fun a => mret (g a)) s) mo tr (Ok (b, s')) mo' ->
  exists rsp a, nstepP n mo rsp mo' tr /\ dec rsp = Some a /\ b = g a /\ s' = s.
Proof.
  intros n dec g s s' mo tr b mo' Hp.
  apply tpath_mbind_ok in Hp as (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->).
  apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
  apply (tpath_mret (st:=nstepP)) in H2 as (E & -> & ->). injection E as -> ->.
  exists rsp, a. rewrite app_nil_r. auto.
Qed.

Lemma is_err_false_of_ceiling : forall x len atop, 0 < len -> atop < 2^63 -> x + mmap_len len <= atop -> is_err x = false.
Proof.
  intros x len atop Hlen Hat Hc. pose proof (mmap_len_ge len Hlen).
  unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma ev_step_okz : forall L e s mo tr z s' mo' atop, atop < 2^63 ->
  event_pre L e -> tpath nstepP (ev_step atop e s) mo tr (Ok (z, s')) mo' -> okz e z.
Proof.
  intros L e s mo tr z s' mo' atop Hat Hpre Hp. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [okz]; try exact I.
  -
    unfold ev_step in Hp. change MAP_FIXED_Z with MAP_FIXED in Hp.
    destruct (Z.land flags MAP_FIXED =? 0) eqn:EF; [| left; reflexivity]. right. cbn [negb] in Hp.
    cbn [event_pre] in Hpre. destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & _ & _ & _ & _ & ->)].
    2:{ exfalso. revert EF. cbv. discriminate. }
    destruct (prot =? 0).
    + apply tpath_msys_mret in Hp as (rsp & a & [Hst HnP] & Hd & -> & ->).
      specialize (HnP I). apply dec_mmap_none_Some in Hd as (ci & Hd).
      destruct a as [e|x].
      * destruct Hd as [-> He]. exfalso. cbn [eff_ret efferr_ci eff0_ci] in HnP. rewrite errno_of_errno_ret in HnP by lia. discriminate.
      * destruct Hd as [_ Hok]. apply mmap_addr_ok_true in Hok as [(_ & _ & Hc) _]. eapply is_err_false_of_ceiling; [| exact Hat| exact Hc]. lia.
    + apply tpath_msys_mret in Hp as (rsp & a & [Hst HnP] & Hd & -> & ->).
      specialize (HnP I). apply dec_mmap_Some in Hd as (ci & Hd).
      destruct a as [e|x].
      * destruct Hd as [-> He]. exfalso. cbn [eff_ret efferr_ci eff0_ci] in HnP. rewrite errno_of_errno_ret in HnP by lia. discriminate.
      * destruct Hd as [_ Hok]. apply mmap_addr_ok_true in Hok as [(_ & _ & Hc) _]. eapply is_err_false_of_ceiling; [| exact Hat| exact Hc]. lia.
  -
    unfold ev_step in Hp. apply tpath_msys_mret in Hp as (rsp & a & [Hst HnP] & Hd & -> & ->).
    specialize (HnP I). unfold dec_mprotect_rw in Hd.
    destruct (dec_mprotect addr len rsp) as [[e|[|]]|] eqn:Hd0; try discriminate.
    + exfalso. apply dec_mprotect_Some in Hd0 as (ci & -> & He). cbn [eff_ret efferr_ci eff0_ci] in HnP.
      rewrite errno_of_errno_ret in HnP by lia. discriminate.
    + injection Hd as <-. reflexivity.
  -
    unfold ev_step in Hp. apply (tpath_munr (st:=nstepP)) in Hp as (E & _). discriminate.
Qed.

(* [comment removed for export] *)
Lemma ev_step_specP : forall L e (G : PState -> Model -> Prop) s0,
  frame_ok G -> event_pre L e ->
  mspecP (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (ev_step (ld_atop L) e)
         (fun z s mo => ev_step_post L e G s0 z s mo /\ okz e z).
Proof.
  intros L e G s0 HG Hpre.
  eapply mspecP_post.
  - eapply (mspecP_paths _ _ _ (fun z _ => okz e z)).
    + apply mspec_mspecP. apply ev_step_spec; assumption.
    + intros s mo tr z s' mo' (_ & HK & _) Hp. eapply ev_step_okz; [exact (proj2 (KL_atop_lt _ _ _ HK))| exact Hpre| exact Hp].
  - intros z s mo [H1 H2]. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma membed_specP {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> ctree_ok L t Post -> nn P t ->
  mspecP (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed (ld_atop L) t)
         (fun r s mo => (exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                        /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0) /\ P r).
Proof.
  intros t. induction t as [r|e k IH]; intros Post P G L s0 HG Hok Hnn.
  - cbn [membed]. apply mspecP_ret. intros s mo (-> & HK & HGs). split; [| exact Hnn]. exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk]. cbn [nn] in Hnn.
    eapply mspecP_bind; [apply (ev_step_specP L e G s0 HG Hpre)|].
    intros z. unfold ev_step_post. apply mspecP_pointwise. intros s1 mo1 ((Hans & HK1 & HG1 & Hm & Hfa & Hso) & Hz).
    rewrite <- (event_post_atop L e z).
    eapply mspecP_conseq; [apply (IH z Post P G (event_post L e z) s1 HG (Hk z Hans) (Hnn z Hz))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo [(L' & Hp & HP & HK & HG' & Hm' & Hfa' & Hso') HPr]. split; [| exact HPr]. exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem raw_malloc_specP : forall X G n, frame_ok G -> 0 <= n -> size_overflows n = false ->
  mspecP (OWN X G) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => OWN (p :: X) G s mo /\ n < 2^63
                        | None => False
                        end).
Proof.
  intros X G n HG Hn Hov. unfold raw_malloc.
  eapply mspecP_bind; [apply mspecP_get|]. intros s0.
  apply mspecP_pointwise. intros s1 mo1 [-> [(L & Hc & HK & Hi) [Hnd HGs]]].
  eapply mspecP_bind.
  { rewrite (MI_Contracts.creach_atop _ _ Hc).
    eapply mspecP_pre; [apply (membed_specP (cmalloc (ps_m s1) n) _ _ G L s1 HG (MI_Contracts.cmalloc_contract_proof _ _ _ Hc Hn) (cmalloc_nn (ps_m s1) n Hov))|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspecP_pointwise. intros s2 mo2 [(L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso) HNN]. cbn [snd] in HPost, HNN.
  eapply mspecP_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspecP_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspecP_ret. intros s mo [-> ->].
  destruct p as [c|]; [| exfalso; apply HNN; reflexivity].
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  assert (Hcr : creach st' (set_live (c :: ld_live L') L')).
  { exact (creach_malloc _ _ _ _ _ (Some c) Hc Hn Hp). }
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  split.
  - split; [|split; [|exact HG2]].
    + exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
      cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
    + cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
  - unfold size_overflows in Hov. apply Z.leb_gt in Hov. lia.
Qed.

Theorem raw_free_specP : forall X G p, frame_ok G ->
  mspecP (OWN (p :: X) G) (raw_free p) (fun _ => OWN X G).
Proof. intros X G p HG. apply mspec_mspecP. apply raw_free_spec. exact HG. Qed.

(* [comment removed for export] *)
Theorem raw_malloc_specP_weak : forall X G n, frame_ok G -> 0 <= n ->
  mspecP (OWN X G) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => OWN (p :: X) G s mo /\ n < 2^63
                        | None => OWN X G s mo
                        end).
Proof. intros X G n HG Hn. apply mspec_mspecP. apply raw_malloc_spec; assumption. Qed.
