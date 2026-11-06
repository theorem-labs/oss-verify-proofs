(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import PrimaryShadow0.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section C.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
Let L := mkALayout (LV V) w U.
#[using="rc HP HU"] Lemma top_eq : al_top L = 32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat.
Proof.
pf V HP (PVar 344 0 1) P344. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 0 4294901760 4294967295) P0.
pf V HP (PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095) R.
unfold two64 in R.
assert (R' : 0 <= 16 * V 6%nat + -4096 * V 344%nat + 3935 <= 4095).
{ destruct (Z.lt_ge_cases (16 * V 6%nat + -4096 * V 344%nat + 3935) 0) as [NEG|NN].
- exfalso. Local Ltac2 Set LiaHints.tbl := fun () => "0040>11607912823.1717063382042.1759314873579.178931307546.17 00000400C00Q00aS2HUS2HU4P3442P62NNS2HU4P3442P61RS2HU4P3442P63NEG".
rewrite <- (Z.mod_add _ 1) in R by lia. rewrite Z.mod_small in R by lia. lia.
- rewrite Z.mod_small in R by lia. exact R. }
unfold al_top, L. rewrite LV_sp0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma t_eq : al_t L = 4096 * V 227%nat. Proof. reflexivity. Qed.
#[using="rc HM HU"] Lemma t_zero : forall i, 80 <= i < 3168 -> m (wa (al_t L + i)) = Some (Z_to_bv 8 0).
Proof.
intros i Hi. mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088) ZR.
rewrite t_eq. Local Ltac2 Set LiaHints.tbl := fun () => "0020>3067982142.14 59958708187.1400000400;S2HUS2HU2Hi".
replace (4096 * V 227%nat + i) with (4096 * V 227%nat + 80 + (i - 80)) by lia. apply ZR. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HM"] Lemma t_wr : wr_at bsegs m (al_t L) 4096.
Proof. mwr V m HM (ZMul (ZLit 4096) (ZV 227)) 4096 W. rewrite t_eq. exact W. Qed.
#[using="HP HU HAT"] Lemma t_pos : 4096 <= al_t L /\ al_t L + 4096 <= ATOP.
Proof. pose proof (ao_t _ (alayout_ok_init V w U HP HU HAT)) as (_ & A & B & _). exact (conj A B). Qed.
#[using="rc HM HP HU HAT"] Theorem athread_init : athread L (ST0 V) X0 m.
Proof.
pose proof t_pos as [T1 T2]. atop_facts.
unfold athread. split.
{ mf V m HM (MCell (ZMul (ZLit 4096) (ZV 227)) 8 (ZMul (ZLit 4096) (ZV 228))) F0.
mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 8)) 8 (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344))))) F8.
mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 16)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))) (ZLit (-8388608)))) F16.
unfold al_bot. rewrite top_eq, t_eq.
Local Ltac2 Set LiaHints.tbl := fun () => "00F0>16121160013.1519198062803.1319819548393.1521274561666.1621514330849.1525267373863.1526304161875.1330093703635.1536449610433.1342995851260.1543781106499.1545118065815.1547804946784.1352426852231.1752913580274.1654965641940.1656863591420.1560524765377.1362241004874.1763844481747.1366711736103.159816467911.17 00000700>00H00L00V00]00a00h00l01301:01A01E01L01P01T01[01_01i02002702>S2HU2HcS2HU2T1S2HU2T12HcS2HUS2HU2T12HcS2HU2HiS2HUS2HU2HcS2HUS2HU2HiS2HU2HcS2HU2HcS2HUS2HU2HiS2HUS2HUS2HU2HiS2HUS2HU2Hc2HiS2HU2T1S2HU2HiS2HU2Hi".
replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat)) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat) in F8 by lia.
replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) + -8388608) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat - 8388608) in F16 by lia.
apply rw_cells_cons; [exact F0|]. apply rw_cells_cons; [exact F8|].
replace (4096 * V 227%nat + Z.of_nat (csize (C8 (Z_to_bv 64 (al_ctx L)))) + Z.of_nat (csize (C8 (Z_to_bv 64 (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat)))))
with (4096 * V 227%nat + 16) by (cbn; lia).
exact F16. }
split.
{ mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 40)) 1 (ZLit 0)) F40. rewrite t_eq. exact F40. }
split.
{ intros c Hc. unfold acache_cells, acache_addr. rewrite get_cls_ST0, max_count_ST0. cbn [c_count aclass0 a_cinit ST0 ainit x_cls X0 xc_cache app length map].
exists (repeat (Z_to_bv 64 0) 16). unfold K_NUM_CLASSES in Hc.
split; [| split; [| rewrite repeat_length; reflexivity]].
- apply zcells; [reflexivity| |].
+ cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 208 + c * 80 + i) with (al_t L + (208 + c * 80 + i)) by lia. apply t_zero. lia.
+ eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
- apply u32arr_zero.
+ intros i Hi. cbn in Hi. replace (al_t L + 208 + c * 80 + 16 + i) with (al_t L + (224 + c * 80 + i)) by lia. apply t_zero. lia.
+ eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
split.
{ exists (repeat (Z_to_bv 8 0) 32). apply zcells; [reflexivity| |].
+ cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 2768 + i) with (al_t L + (2768 + i)) by lia. apply t_zero. lia.
+ eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
split.
{ exists (repeat (Z_to_bv 64 0) 46). split; [| rewrite repeat_length; reflexivity]. apply u64arr_zero.
+ intros i Hi. cbn in Hi. replace (al_t L + 2800 + i) with (al_t L + (2800 + i)) by lia. apply t_zero. lia.
+ eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)) F3168. rewrite t_eq. exact F3168.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HM HP HU HAT"] Theorem aqcache_loc_init : aqcache L m (aq_tcache L) [] [] 0.
Proof.
pose proof t_pos as [T1 T2]. atop_facts.
unfold aqcache, aq_tcache. split; [| exact I].
apply zcells; [reflexivity| |].
- cbn [cells_size csize Nat.add]. intros i Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0050>30225361107.1342398046118.1346067765031.1551504603841.1367285729276.1500000700;00B00F00MS2HU2T1S2HUS2HU2HiS2HUS2HU2Hi".
replace (al_t L + 80 + i) with (al_t L + (80 + i)) by lia. apply t_zero. lia.
- eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End C.
End CANSEC1.
