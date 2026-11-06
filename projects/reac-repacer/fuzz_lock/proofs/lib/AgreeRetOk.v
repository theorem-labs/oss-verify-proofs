(* Modified by Theorem Labs: the twin of lib/AgreeFrame.v ubsan_agrees_of_slots (no licence line) for a return value of the fuzz target of 0 or -1 *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/AgreeFrame.v and lib/AgreeTop.v
   (ubsan_agrees_of_cut_free) at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.AgreeRetOk.
   Both builds walk the same trace, SPECX_q ret (AgreeRetD1.v, U/Prog/AgreeRetD2.v): on a payload where ret is 0 the
   kit's leaf, run by the kit's arms; where ret is -1 Prog/FrameRetD2.v leaf_shapeX_r, run by the plain -1 arms
   Prog/FrameRetA10.v ... FrameRetA19.v and the UBSan cut-free -1 arms AgreeRetA10.v ... AgreeRetA19.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_lock Require Statements Images.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import FrameRet.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require FrameRetOk.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import AgreeRet AgreeRetD1 AgreeRetD4.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require
  AgreeRetA10 AgreeRetA11 AgreeRetA12 AgreeRetA13 AgreeRetA14 AgreeRetA15 AgreeRetA16 AgreeRetA17 AgreeRetA18 AgreeRetA19.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require AgreeZlib.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require AgreeRet AgreeRetD2 AgreeRetD4.
Import ListNotations.
Open Scope Z_scope.

(* the ten UBSan cut-free -1 arms *)
Lemma arms_m1_cf_proved : U.Prog.AgreeRetD2.arms_m1_cf.
Proof.
  exact (conj AgreeRetA10.src0_runX_0E1_m1_cf_ok (conj AgreeRetA11.src0_runX_0M1_m1_cf_ok
    (conj AgreeRetA12.src0_runX_1E1_m1_cf_ok (conj AgreeRetA13.src0_runX_1E2_m1_cf_ok
    (conj AgreeRetA14.src0_runX_1E3_m1_cf_ok (conj AgreeRetA15.src0_runX_1E4_m1_cf_ok
    (conj AgreeRetA16.src0_runX_1M1_m1_cf_ok (conj AgreeRetA17.src0_runX_1M2_m1_cf_ok
    (conj AgreeRetA18.src0_runX_1M3_m1_cf_ok AgreeRetA19.src0_runX_1M4_m1_cf_ok))))))))).
Qed.

(* the two builds' traces are the same: AgreeRetD1.v SPECX_q and U/Prog/AgreeRetD2.v SPECX_q have the same text over
   the shared trace spec; compared branch by branch, so that no conversion unfolds the driver tree *)
Lemma SPECX_q_teq : forall (LS : lib_shape) (ret : list byte -> Z) (inp : ProcInput),
  t_eq (SPECX_q (LS:=LS) ret inp) (U.Prog.AgreeRetD2.SPECX_q (LS:=LS) ret inp).
Proof.
  intros LS ret inp.
  unfold SPECX_q, U.Prog.AgreeRetD2.SPECX_q, SPECX_args_q, U.Prog.AgreeRetD2.SPECX_args_q.
  destruct (in_argv inp) as [|a [|p [|b rest]]]; cbv beta iota; [apply t_eq_refl | apply t_eq_refl | | apply t_eq_refl].
  destruct (classify_open p (in_fs inp)) as [| |data]; cbv beta iota; [apply t_eq_refl | apply t_eq_refl |].
  apply t_alt2_congr; [apply t_eq_refl|].
  unfold SPECX_loaded_q, U.Prog.AgreeRetD2.SPECX_loaded_q.
  intros tr; split; apply tset_mono; intros r tr' Hr; exact Hr.
Qed.

Theorem agree_ret_ok : agree_ret_hyp.
Proof.
  intros ret HR01 LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu.
  assert (HROOMp : forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) by exact HROOM.
  unfold Statements.ubsan_agrees, agrees_in. intros en_p en_s inp Hep Hes Hinput Hbud.
  destruct (U.Prog.AgreeRetD4.ubsan_crealizes_of_cgr LS ret Gu GIu HR01 arms_m1_cf_proved HROOM HGu GILu GI0u Hu
    en_s inp Budgets.Standard.lim_target Hes Hinput ltac:(apply Z.leb_le; vm_compute; reflexivity)) as [HUr HUc].
  exact (agree_frame Images.plain Budgets.Standard.lim_source en_p Images.ubsan Budgets.Standard.lim_target en_s inp
    (SPECX_q (LS:=LS) ret inp) (U.Prog.AgreeRetD2.SPECX_q (LS:=LS) ret inp)
    (plain_rz_of_gr LS ret G GI HR01 FrameRetOk.arms_m1_proved HROOMp HG GIL GI0 Hp en_p inp Hep Hinput)
    HUr (SPECX_q_teq LS ret inp)
    (cf_run_of_budget Images.plain Budgets.Standard.lim_source en_p inp Hbud) HUc).
Qed.
