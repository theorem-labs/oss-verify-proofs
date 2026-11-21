(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (12 recorded proofs replaced by written proofs (fsimeq_drop, fuzz_malloc_sim, free_opt_sim and 9 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe Sim MPaths Harness Adapter Driver Stdio TargetSafe StepB EquivShared.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_EquivProg () := "C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3Sim3relC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec3Sim4fsimC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI4ELinuxProcessSemantics?LinuxProcessSem5State5event00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared6fsimeqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared;fsimeq_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared:fsimeq_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared:fsimeq_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared;fsimeq_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared:fsimeq_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared@fsimeq_pointwiseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared;fsimeq_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Adapter9run_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared9fsimeq_ifC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness;fuzz_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg;fsimeq_dropC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec7Adapter:target_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:TargetSafe5olistC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;Permutation>Permutation_inI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes9Empty_set00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec7Harness8free_optC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness7dt_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9dbuf_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg?fuzz_malloc_simC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg<free_opt_simC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationHPermutation_app_swap_appC46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib4Spec7Harness8fuzz_oneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=PRODUCER_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9WKSP_SIZEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg<fuzz_one_simC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib4Spec9EquivProg=run_calls_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg6rd_relC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec6Driver<u8s_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~K46Stdlib7Sorting;Permutation;Permutation03I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum02C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C47Corelib4Init5Logic3notK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib4Spec9EquivProg<zlength_u8s'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg<zlength_app'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum01K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05I59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared9PIECE_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProgBread_loop_body_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver8read_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9READ_FUELC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_closeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_openC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4ListAnth_in_or_defaultC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List2InI47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes4negbK59OSSVerify5KrLib4Spec6Driver8diag_msg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib4Spec;EquivShared:diag_shortC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg<read_all_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:main_modelC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib4Spec6Driver7HDR_MINC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9COUNT_MAXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7FdState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC56Stdlib5Arith8PeanoNat3Nat3lebC59OSSVerify5KrLib3Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open>path_is_dirrefC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C59OSSVerify5KrLib3Lib5Nodes;open_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC59OSSVerify5KrLib3Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC59OSSVerify5KrLib3Lib5Nodes>m_fds_with_fdsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib4Spec9EquivProg=with_fds_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State8path_maxC4ELinuxProcessSemantics?LinuxProcessSem5State<ENAMETOOLONGC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOENTI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeC4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFC4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8read_ans01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8read_ans02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRI4ELinuxProcessSemantics?LinuxProcessSem5State9SockState00C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib3Lib5NodesAm_vmmaps_with_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=m_fs_with_fdsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec5StepB7nf_nodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg?nstep_open_xferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>minv_preservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg5R_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3Sim8fsim_sysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9EquivProg@nstep_close_xferC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4Spec9EquivProg?nstep_read_xferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode>nstep_dec_readC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib3Lib6DecodeIlength_file_read_le_countC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6DecodeAnstep_dec_set_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode;dec_set_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=m_fs_with_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>m_fds_with_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesAm_vmmaps_with_tidC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPE".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section More.
Context {StG StC : Type} (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Local Notation fsim := (fsim debtG debtC stepG).
Local Notation fsimeq := (fsimeq debtG debtC stepG).

(* [comment removed for export] *)
Lemma fsim_bind_get {A B} (R : rel StG StC) (kG : StG -> M StG A) (kC : StC -> M StC B) Q :
  (forall sG moG sC moC, R sG moG sC moC ->
     fsim (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) (kG sG) (kC sC) Q) ->
  fsim R (mbind mget kG) (mbind mget kC) Q.
Proof.
  intros H sG moG sC moC HR. specialize (H _ _ _ _ HR). unfold mbind, mget. cbn [ebind fst snd].
  apply H. repeat split; reflexivity.
Qed.

End More.

Section More1.
Context {St : Type} (dG dC : St -> list event) (stepG : node -> Model -> resp -> Model -> list event -> Prop).
(* [comment removed for export] *)
Lemma fsimeq_drop {A} (R : rel St St) (phi : Prop) (m : M St A) Q :
  fsimeq dG dC stepG R m m Q -> fsimeq dG dC stepG (fun sG moG sC moC => R sG moG sC moC /\ phi) m m Q.
Proof. intros H. eapply fsimeq_pre; [exact H|]. intros ? ? ? ? [HR _]. exact HR. Qed.
End More1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
Local Notation fsim := (fsim debtG debtC stepG).

Hypothesis Hm : forall X n, 0 <= n ->
  fsimeq (RX X) (raw_malloc n) (raw_malloc n)
         (fun r => match r with Some p => fun sG moG sC moC => RX (p :: X) sG moG sC moC /\ n < 2^63 | None => RX X end).
Hypothesis Hf : forall X p, fsimeq (RX (p :: X)) (raw_free p) (raw_free p) (fun _ => RX X).
Hypothesis Hperm : forall X Y sG moG sC moC, Permutation X Y -> RX X sG moG sC moC -> RX Y sG moG sC moC.
Hypothesis Hleak : forall X Y sG moG sC moC, RX (Y ++ X) sG moG sC moC -> RX X sG moG sC moC.
Hypothesis Hnh : forall X (Q : Empty_set -> rel St St), fsimeq (RX X) new_handler new_handler Q.
Hypothesis Hemit : forall X v, fsimeq (RX X) (emit v) (emit v) (fun _ => RX X).

Local Ltac ret_same := apply fsimeq_ret; intros ? ? ? ? HH; exact HH.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fuzz_malloc_sim : forall X n,
  fsimeq (RX X) (fuzz_malloc raw_malloc new_handler n) (fuzz_malloc raw_malloc new_handler n) (fun r => RX (olist r ++ X)).
Proof.
  intros X n. unfold fuzz_malloc.
  apply fsimeq_if; intros C.
  - apply Z.ltb_lt in C.
    eapply fsimeq_bind; [apply Hm; lia|].
    intros [p|]; cbn beta iota.
    + apply fsimeq_drop. ret_same.
    + eapply fsimeq_bind; [apply (Hnh X (fun _ _ _ _ _ => False))|]. intros [].
  - ret_same.
Qed.

Lemma free_opt_sim : forall X o,
  fsimeq (RX (olist o ++ X)) (free_opt raw_free o) (free_opt raw_free o) (fun _ => RX X).
Proof. intros X [p|]; cbn [free_opt olist app]; [apply Hf| ret_same]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fuzz_one_sim : forall X data,
  fsimeq (RX X) (fuzz_one raw_malloc raw_free new_handler data) (fuzz_one raw_malloc raw_free new_handler data) (fun _ => RX X).
Proof.
ltac2:(KReplay.run1 (kr_t_EquivProg ()) ["TargetSim"] "h02_Hh11rh22PPh33moCh43moGh52sCh62sGh71Hh84dBufh92dth:1lh;8producerh<4wksph=2HHh>1Xh?4datap;1p;5p;2p;3p;4p;6p;=p;:p;@g008Oj1?Tg00Wnj1HTg00RHj56Tg00Ukj22Tg00A9j30Tg00nCj1GTg00o<j1FTg00mIj4<Tg00HQj3ATg001Rj54Tg0107j28Tg011:j2:Tg012:j4@Tg00TDj33Tg0130j4>Tg004Kj6=Tg00KFl=;Tg00JFl:ETg00IEl@9Tg013Nj6CTg00GUl:BTg00MGl@DTf2R0g00flR1g00hLR2f1R3f0R4D4p=7f4R5f3R6A003430p=1P4P3P0P6P5P1P2f5R7f6R8f7R9f8R:f9R;f:R<f;R=f<R>f=R?M@Dp=5p,3ptrR@#?RA%?2p,2StRBPBp,5debtGRCp,5debtCRDp,5stepGRE%H@RFP2p,2RXRGP3O1RHPBP@p,:raw_mallocRIp,;new_handlerRJg014HRKD6RLPLPG12@4RL=0@0RMO1RNX1FPBPFP2PBP@PIPJ%G3ROD6RPPBPFP2PBP@PIPJg015GRQD6RRPBPFP2PBP@PIPJ%F6RSD6RTPBP@p,8raw_freeRUP0C<RVPBP@PUP8C<RWg00hjRX9AB2V1RY57BV1RZ97BVV1R[97BVV1R\57BX8FR]D4X<FR^D4X9FR_D4X;FR`P`PGP0O1V2R`183KPBPBPCPDPEPFP2PNPPPPPGP@PLP@12@3RPP6D1RNO1RKX1FP_P_PGP6O1V218MOPBPBPCPDPEPFP2PKPRPRPGP@PLP@PP12@0RR=0@5D1RKO1ROX1FP^P^PGP5O1V218NQPBPBPCPDPEPFP2POPTPTPGP@PLP@PP12@6=0@7RT90@RD1O1ROX1FP]P]PGP7O1V218KSPBPBPCPDPEPOPGP@PLP@PPPTD1RTO1PVPVP\P\PGP8O1V2PBPBPCPDPEP1PGA0@RTO1POPVPVPGP@PPP@PR12@5RO=0@8R\D1O1RLV11:T0g00DiRTPGP@POP@12@7R7P@12@8ROP@12@9RKP;D1D1P6P0P3P4O5p,5HpermRSP@P7P@PO12@:R]=0@<RN90@KRQD1P@P7P@POPND1R^90@KP5P6P0P3P@A0@7ORMPKPNC@A0@MQP@PKP@PMPND153@PAA0@OKRN12@;RM=0@=RQ90@]R_50@A0@K]12@<Ra=0@>R>50@Rb90@M93@4X:AP4P@POP@PKP_D1RcP@POPKP_C>E=P@P]P@PNPQD193@cPAPbP@P]P@PMP@PaP@12@=P?D1D1A0@a453@X:AP4P@PKP@P]P>D1RAP@PKP]P>C>E=P@PKP@P]A0@M>D1A0@MA53@P4b2b2b2P4O8W7X3TX5BW4X6BM=;PBPBPCPDPEPLPGA0@P\R\O1PVPVP[P[PGP9O1V2PBPBPCPDPEP1PGA0@R\O1PLPVPVPGA0@79R790@RO1RRV11:\0PGP^P6P0P3P4O5PSP@POP@PKPQD1P@PKP@POPQD1P5P6P0P3P@POPKPQC@P4O8W7X3TX5BX4TX6BM=;PBPBPCPDPEPRPGP7O1PVPVPZPZPGP:O1RZV21:70PBPBPCPDPEPGA0@O:O1PZPWPWPYPYPGP;O1R;V21::8PBPBPCPDPEP2P;PXPGP<O1V2PGP?P6P0P3P4O5P4W=X3TX5BX4TX6BM:EX01M>5X01M>5X01M>5X01M>5X8FM@9X<FM@9X9FM@9X;FM@9PBPBPCPDPEP2PHPBP@PIPUPJP4ECR4P4P`M:BeW?W>o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_sim : forall X n payload rc,
  fsimeq (RX X) (run_calls (fuzz_one raw_malloc raw_free new_handler) emit n payload rc)
               (run_calls (fuzz_one raw_malloc raw_free new_handler) emit n payload rc) (fun _ => RX X).
Proof.
  intros X n. induction n as [|n IH]; intros payload rc; cbn [run_calls].
  - ret_same.
  - eapply fsimeq_seq; [apply fuzz_one_sim|]. intros rc'.
    eapply fsimeq_seq; [apply Hemit|]. intros _. apply IH.
Qed.

Theorem target_run_sim : forall X cfg payload,
  fsimeq (RX X) (target_run raw_malloc raw_free (fuzz_one raw_malloc raw_free new_handler) emit cfg payload)
               (target_run raw_malloc raw_free (fuzz_one raw_malloc raw_free new_handler) emit cfg payload) (fun _ => RX X).
Proof using Hm Hf Hperm Hleak Hnh Hemit.   (* [comment removed for export] *)
  intros X cfg payload. unfold target_run.
  eapply fsimeq_bind with (Q1 := fun a => match a with
                                         | None => RX X
                                         | Some None => RX X
                                         | Some (Some p) => RX (p :: X)
                                         end).
  { apply fsimeq_if; intros _; [ret_same|].
    eapply fsimeq_bind; [apply Hm; unfold zlength; lia|]. intros [p|]; apply fsimeq_ret; cbn; [intros ? ? ? ? [H _]; exact H| intros ? ? ? ? H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply fsimeq_seq; [apply run_calls_sim|]. intros rc. eapply fsimeq_seq; [apply Hf|]. intros _. ret_same.
  - eapply fsimeq_seq; [apply run_calls_sim|]. intros rc. eapply fsimeq_seq; [ret_same|]. intros _. ret_same.
  - ret_same.
Qed.

End TargetSim.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DriverSim.
Context {St ptr : Type}.
Variables (debtG debtC : St -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Variables (ioG ioC : IOStyle St).
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variables (rsG rsC : Z).   (* [comment removed for export] *)
Variable alloc_init : Z -> M St unit.
Variables (runG runC : Z -> list Z -> M St Z).
Variable alloc_count : M St Z.
(* [comment removed for export] *)
Variables (R0 R1 : list ptr -> rel St St).
Local Notation fsimeq := (fsimeq debtG debtC stepG).
Local Notation fsim := (fsim debtG debtC stepG).

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

(* [comment removed for export] *)
Definition rd_rel (X : list ptr) (st : @rd_st ptr) : rel St St := fun sG moG sC moC =>
  R0 (rd_buf st :: X) sG moG sC moC /\ zlength (rd_content st) <= rd_cap st /\ 0 < rd_cap st <= 2 * MAX_INPUT.

Lemma zlength_app' {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_u8s' : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.

Local Ltac ret_same := apply fsimeq_ret; intros ? ? ? ? HH; exact HH.

Lemma read_loop_body_sim : forall X fd path st, zlength path <= PIECE_MAX ->
  fsimeq (rd_rel X st) (read_loop_body ioG drv_malloc drv_free rsG fd path st) (read_loop_body ioC drv_malloc drv_free rsC fd path st)
         (fun r => match r with
                   | inl st' => rd_rel X st'
                   | inr RdExit => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                   | inr (RdDone buf content) => R0 (buf :: X)
                   end).
Proof.
  intros X fd path st Hpath. unfold read_loop_body.
  eapply fsimeq_bind with
    (Q1 := fun g => match g with
                    | None => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                    | Some st1 => fun sG moG sC moC => rd_rel X st1 sG moG sC moC /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                    end).
  { apply fsimeq_pointwise. intros sG0 moG0 sC0 moC0 (Ho0 & Hlen & Hcap).
    destruct (Z.eqb_spec (zlength (rd_content st)) (rd_cap st)) as [Heq|Hne].
    - destruct (Z.leb_spec MAX_INPUT (rd_cap st)) as [Hbig|Hsmall].
      + eapply fsimeq_seq; [eapply fsimeq_pre; [apply Hdiag0; exact I| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]|].
        intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists (rd_buf st :: X). exact Ho.
      + eapply fsimeq_bind. { eapply fsimeq_pre; [apply Hdm0; lia| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]. }
        intros [nb|]; cbn beta iota.
        * eapply fsimeq_seq.
          { eapply fsimeq_pre; [apply (Hdf0 (nb :: X) (rd_buf st))|]. intros sG moG sC moC [Ho _]. eapply Hperm0; [apply perm_swap| exact Ho]. }
          intros _. apply fsimeq_ret. intros sG moG sC moC Ho. cbn. unfold rd_rel. cbn. unfold MAX_INPUT in *. splits; auto; lia.
        * eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists (rd_buf st :: X). exact Ho.
    - apply fsimeq_ret. intros sG moG sC moC (-> & -> & -> & ->). unfold rd_rel. splits; auto; lia. }
  intros [st1|]; cbn beta iota.
  2:{ ret_same. }
  (* [comment removed for export] *)
  apply fsimeq_pointwise. intros sG1 moG1 sC1 moC1 ((Ho & Hlen & Hcap) & Hct & Hlt).
  set (want0 := rd_cap st1 - zlength (rd_content st)).
  set (want := if 65536 <? want0 then 65536 else want0).
  assert (Hwant : 0 <= want <= want0 /\ want < 2^64). { subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); unfold MAX_INPUT in *; lia. }
  eapply fsimeq_bind.
  { eapply fsimeq_pre; [apply (Hread (rd_buf st1 :: X) fd _ _ want); lia|].
    intros ? ? ? ? (-> & -> & -> & ->). exact Ho. }
  intros [e|bs]; cbn beta iota.
  - eapply fsimeq_seq; [apply Hdiag0; exact Hpath|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho'. exists (rd_buf st1 :: X). exact Ho'.
  - destruct (length bs =? 0)%nat eqn:C.
    + apply fsimeq_ret. intros sG moG sC moC [Ho' _]. exact Ho'.
    + apply fsimeq_ret. intros sG moG sC moC [Ho' Hbs]. unfold rd_rel. cbn. rewrite zlength_app', zlength_u8s', Hct. splits; auto; lia.
Qed.

Lemma read_all_sim : forall X path, zlength path <= PIECE_MAX ->
  fsimeq (R0 X) (read_all ioG drv_malloc drv_free rsG path) (read_all ioC drv_malloc drv_free rsC path)
         (fun r => match r with
                   | RdExit => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                   | RdDone buf content => R0 (buf :: X)
                   end).
Proof.
  intros X path Hpath. unfold read_all.
  eapply fsimeq_bind; [apply Hopen|]. intros [e|fd]; cbn beta iota.
  - eapply fsimeq_seq; [apply Hdiag0; exact Hpath|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. exact Ho.
  - eapply fsimeq_bind; [apply Hdm0; lia|]. intros [buf|]; cbn beta iota.
    2:{ eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. exact Ho. }
    eapply fsimeq_bind.
    + eapply fsimeq_pre.
      * apply (fsimeq_loop debtG debtC stepG (rd_rel X)
                 (fun r => match r with RdExit => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                                        | RdDone buf content => R0 (buf :: X) end)).
        intros st0. eapply fsimeq_post; [apply read_loop_body_sim; exact Hpath|]. intros [st'|[|b c]] sG moG sC moC H; exact H.
      * intros sG moG sC moC [Ho _]. unfold rd_rel. cbn. split; [exact Ho|]. unfold zlength, MAX_INPUT; cbn. lia.
    + intros [|buf' content]; cbn beta iota; [ret_same|].
      eapply fsimeq_seq; [apply Hclose|]. intros _. ret_same.
Qed.

Lemma main_model_sim : forall X argv, Forall (fun a => zlength a <= PIECE_MAX) argv ->
  fsimeq (R0 X) (main_model ioG drv_malloc drv_free rsG alloc_init runG alloc_count argv)
               (main_model ioC drv_malloc drv_free rsC alloc_init runC alloc_count argv)
         (fun _ sG moG sC moC => exists X', R1 X' sG moG sC moC).
Proof.
  intros X argv Hargv. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) <= PIECE_MAX).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) Hargv _ Hin)| unfold zlength, PIECE_MAX; cbn; lia]. }
  apply fsimeq_if; intros C.
  { eapply fsimeq_seq; [apply Hdiag0; cbn; apply Hnth|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. apply H01. exact Ho. }
  eapply fsimeq_bind; [apply read_all_sim; apply Hnth|]. intros [|buf content]; cbn beta iota.
  { apply fsimeq_ret. intros sG moG sC moC [X' Ho]. exists X'. apply H01. exact Ho. }
  apply fsimeq_if; intros C1.
  { eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. eapply fsimeq_seq; [apply Hdf0|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. apply H01. exact Ho. }
  apply fsimeq_if; intros C2.
  { eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. eapply fsimeq_seq; [apply Hdf0|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. apply H01. exact Ho. }
  eapply fsimeq_seq; [apply Hinit|]. intros _.
  eapply fsimeq_seq; [eapply fsimeq_pre; [apply (Hrun (buf :: X))| intros; apply H01; assumption]|]. intros status.
  eapply fsimeq_bind with (Q1 := fun _ => R1 (buf :: X)).
  { destruct (Z.testbit _ 15).
    - eapply fsimeq_seq; [apply Hcount|]. intros n. apply fsimeq_ret. auto.
    - apply fsimeq_ret. auto. }
  intros status'. eapply fsimeq_seq; [apply Hdf1|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. exact Ho.
Qed.
End DriverSim.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_self : forall mo, with_fds (m_fds mo) mo = mo.
Proof. intros [[t p] ? ? ? ? ? ?]. reflexivity. Qed.

(* [comment removed for export] *)
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
  destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id wr|dnr dnw| |sid sd sst|ectx|fam|aid af]|].
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
  - destruct H.   (* FdStream: nstep's NRead arm answers Some _ with False *)
  - destruct H.   (* FdEventfd *)
  - destruct H.   (* FdDgram *)
  - destruct H.   (* FdAnon *)
  - destruct H as [-> ->]. exists (efferr EBADF). rewrite (with_fds_self moG), Ef, with_fds_self. repeat split; reflexivity.
Qed.

Section FdNodes.
Context {St : Type} (debtG debtC : St -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Hypothesis stepG_sub : forall n mo r mo' e, ~ nf_node n -> stepG n mo r mo' e -> nstep n mo r mo' e.   (* [comment removed for export] *)
Variable R : rel St St.
Local Notation fsimeq := (fsimeq debtG debtC stepG).
Local Notation fsim := (fsim debtG debtC stepG).
Hypothesis Rmodels : forall sG moG sC moC, R sG moG sC moC ->
  minv moG /\ minv moC /\ m_halted moG = None /\ m_halted moC = None /\ m_fds moG = m_fds moC /\ m_fs moG = m_fs moC.
Hypothesis Rtables : forall sG moG sC moC moG' moC', R sG moG sC moC ->
  m_vmmaps moG' = m_vmmaps moG -> m_vmmaps moC' = m_vmmaps moC ->
  minv moG' -> minv moC' -> m_halted moG' = None -> m_halted moC' = None ->
  m_fds moG' = m_fds moC' -> m_fs moG' = m_fs moC' -> R sG moG' sC moC'.

Lemma R_fds : forall sG moG sC moC moG', R sG moG sC moC ->
  moG' = with_fds (m_fds moG') moG -> minv moG' -> minv (with_fds (m_fds moG') moC) ->
  m_halted moG' = None -> m_halted (with_fds (m_fds moG') moC) = None ->
  R sG moG' sC (with_fds (m_fds moG') moC).
Proof.
  intros sG moG sC moC moG' HR E MG MC HG HC. pose proof (Rmodels _ _ _ _ HR) as (_ & _ & _ & _ & Hfds & Hfs).
  eapply Rtables; [exact HR| rewrite E; apply m_vmmaps_with_fds| apply m_vmmaps_with_fds| exact MG| exact MC| exact HG| exact HC| rewrite m_fds_with_fds; reflexivity| rewrite E, !m_fs_with_fds; exact Hfs].
Qed.

Lemma open_sim : forall path,
  fsimeq R (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => R).
Proof.
  intros path. unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. split; [left; exact (proj1 Hst)|].
    destruct (nstep_open_xfer _ _ _ _ _ moC Hst Hfds Hfs) as [HstC E].
    pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    exists rspG, (with_fds (m_fds moG') moC), a. split; [exact HstC|]. split; [exact Hd|]. split; [reflexivity|]. eapply R_fds; eauto.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.

Lemma close_sim : forall fd,
  fsimeq R (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => R).
Proof.
  intros fd. unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. split; [left; exact (proj1 Hst)|].
    destruct (nstep_close_xfer _ _ _ _ _ moC Hst Hfds) as [HstC E].
    pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    exists rspG, (with_fds (m_fds moG') moC), a. split; [exact HstC|]. split; [exact Hd|]. split; [reflexivity|]. eapply R_fds; eauto.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.

Lemma read_sim : forall fd bufG bufC cnt, 0 <= cnt < 2^64 ->
  fsimeq R (msys (NRead fd bufG cnt) (dec_read bufG cnt)) (msys (NRead fd bufC cnt) (dec_read bufC cnt))
         (fun a => match a with RdData bs => fun sG moG sC moC => R sG moG sC moC /\ zlength bs <= cnt | RdErr _ => R end).
Proof.
  intros fd bufG bufC cnt Hcnt. unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. split; [left; exact (proj1 Hst)|].
    destruct (nstep_read_xfer fd bufG bufC cnt _ _ _ _ moC Hst Hfds Hfs) as (rspC & HstC & E & HdC).
    pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    exists rspC, (with_fds (m_fds moG') moC), a. split; [exact HstC|]. split; [rewrite HdC; exact Hd|]. split; [reflexivity|].
    pose proof (R_fds sG moG sC moC moG' HR E HmG HmC HhG' HhC') as HR'.
    destruct a as [e|bs]; [exact HR'|]. split; [exact HR'|].
    pose proof (nstep_dec_read fd bufG cnt _ _ _ _ Hcnt Hst) as (_ & a' & Hd' & Ha'). rewrite Hd in Hd'. injection Hd' as <-.
    destruct Ha' as (p & off & data & _ & _ & -> & _). unfold zlength.
    pose proof (length_file_read_le_count data off cnt Hcnt). lia.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma settid_sim :
  fsim R (msys NSetTid dec_set_tid) (msys NSetTid dec_set_tid) (fun _ _ => R).
Proof.
  apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    destruct Hst as (-> & t & -> & Ht). split; [left; reflexivity|].
    set (tC := match m_tid moC with Some t0 => t0 | None => Z_to_bv 64 1 end).
    set (moC' := match m_tid moC with Some _ => moC | None => with_tid tC moC end).
    assert (HstC : nstep NSetTid moC (eff0 tC) moC' []).
    { cbn [nstep]. split; [reflexivity|]. exists tC. split; [reflexivity|]. subst tC moC'. destruct (m_tid moC); [auto|].
      rewrite unsigned_lit by lia. unfold Fork.PID_MAX_ENVELOPE. split; [lia| reflexivity]. }
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    pose proof (nstep_dec_set_tid moC _ _ _ MiC HstC) as (_ & tz & HdC & _ & _).
    exists (eff0 tC), moC', tz. split; [exact HstC|]. split; [exact HdC|].
    assert (EG : m_vmmaps moG' = m_vmmaps moG /\ m_fds moG' = m_fds moG /\ m_fs moG' = m_fs moG).
    { destruct (m_tid moG); [destruct Ht as [_ ->]| destruct Ht as [_ ->]]; [auto|]. rewrite m_vmmaps_with_tid, m_fds_with_tid, m_fs_with_tid. auto. }
    assert (EC : m_vmmaps moC' = m_vmmaps moC /\ m_fds moC' = m_fds moC /\ m_fs moC' = m_fs moC).
    { subst moC'. destruct (m_tid moC); [auto|]. rewrite m_vmmaps_with_tid, m_fds_with_tid, m_fs_with_tid. auto. }
    destruct EG as (EG1 & EG2 & EG3). destruct EC as (EC1 & EC2 & EC3).
    eapply Rtables; eauto; congruence.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.
End FdNodes.
