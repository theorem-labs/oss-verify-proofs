(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import PrimaryShadow0.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ABytes ALayout ARep ARepFrame AHeapP APoisonR_iface ASec ARepInit_kit ARepInit_A ARepInit_D.
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
Section S.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
Hypothesis SH0 : bshadow0 V m.
Let L := mkALayout (LV V) w U.
#[using="rc HM HU"] Lemma asec_inst_init : asec_inst L m.
Proof.
unfold asec_inst.
mf V m HM (MCell (ZLit 651048) 8 (ZMul (ZLit 4096) (ZV 226))) F1.
Local Ltac2 Set LiaHints.tbl := fun () => "0080>10404803990.1416382764429.131878909846.15 22871950861.1425165678102.1856962179469.187220276237.15 8274901526.13 00000400800<00@00D00H00L00PS2HUS2HUS2HUS2HUS2HUS2HUS2HUS2HU".
aimg V m HM 0x9ef58 [C1 (Z_to_bv 8 0)] I2.
aimg V m HM 0x9ef60 [CB 32 (repeat (Z_to_bv 8 0) 32)] I3.
aimg V m HM 0x9ef80 [CB 512 (repeat (Z_to_bv 8 0) 512)] I4.
mf V m HM (MZeroC (ZLit 651649) 3) F5.
assert (F5' : rw_cells bsegs m 651649 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F5.
aimg V m HM 0x9f198 [CB 16 (repeat (Z_to_bv 8 0) 16)] I6.
split; [exact F1|]. split; [exists (Z_to_bv 8 0); exact I2|]. split; [exists (repeat (Z_to_bv 8 0) 32); exact I3|].
split; [exists (repeat (Z_to_bv 8 0) 512); exact I4|]. split; [exact F5'|]. exists (repeat (Z_to_bv 8 0) 16); exact I6.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HU HAT"] Lemma asec_arr_init : asec_arr L (ST0 V) [] m.
Proof.
pose proof (ao_ptr _ (alayout_ok_init V w U HP HU HAT)) as (_ & P1 & P2). atop_facts. change (mkALayout (LV V) w U) with L in P1, P2.
exists []. split; [apply Permutation_refl|]. cbn [map a_nsec a_nres ST0 ainit].
Local Ltac2 Set LiaHints.tbl := fun () => "0020>54969794426.1465664001211.1400000700@S2HU2P1S2HU2P21H".
split; [apply u64arr_nil; lia|]. split; [| intros i ch Hi; destruct i; discriminate].
exists []. rewrite Z.add_0_r. change (Z.to_nat (8 * (0 - 0))) with 0%nat. apply rw_cells_CB0; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HP HU HAT"] Lemma asec_wf_init : asec_wf L (ST0 V) [].
Proof.
unfold asec_wf. split; [exact (alayout_ok_init V w U HP HU HAT)|]. cbn. split; [reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "0020>16396675123.127386141759.12 000004008S2HUS2HU".
split; [split; [reflexivity| lia]|]. split; [reflexivity|]. split; [lia|].
split; [constructor| exact sec_disjoint_nil].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HU SH0"] Lemma aprim0_init : aprim0 L m.
Proof.
unfold aprim0. destruct (primary_shadow0 V m SH0 HP) as [Z0 W0]. rewrite (sb_eq' V w U HU) in Z0, W0. change (mkALayout (LV V) w U) with L in Z0, W0.
unfold K_REGION. rewrite ARepFrame.shlen_div. change (2 ^ 32 / 8) with 536870912. change (2^34) with 17179869184 in Z0, W0.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>62043009391.1662043009391.187549844562.16 00000700>00ES2HU2HiS2HU2HiS2HU2W2".
split; [intros i Hi; apply Z0; lia|].
destruct W0 as (W1 & W2 & W3). split; [exact W1|]. split; [lia|]. intros i Hi. apply W3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HM HP HU HAT SH0"] Lemma ashz_init : ashz L [] m.
Proof.
intros x Hx HF _. pose proof SH0 as SZ. unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.
pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 6 0 255) P6.
unfold astartup_hulls in HF. cbv [al_V L LV Nat.eqb] in HF.
unfold al_store, al_nodes, al_fake, al_dtls, al_ctx, al_t, al_res, al_ptr_array in HF. cbv [al_V L LV Nat.eqb] in HF.
repeat lazymatch type of HF with
| Forall _ (_ :: _) => let H1 := fresh "NH" in pose proof (Forall_inv HF) as H1; cbn [fst snd] in H1; apply Forall_inv_tail in HF
| _ => clear HF
end.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>29782367974.3342960166045.1655301970421.2 59310676311.3367324380744.1700000400@00A01[022S2HUS2Hx1H2H02H1SS2NH2Hr1H2H02H42H52H93H103NH13NH23NH33NH43NH53NH63NH74P2084P2093NH83NH94NH102Hx2P03P103LOWS3HAT2Hx2P63WIN1H2H02H1".
assert (SX : shad x = ASHOFF + x / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity). unfold ASHOFF in SX.
destruct (Z.lt_ge_cases x (32768 * V 0%nat + 4096 * V 10%nat - 8388608)) as [LOW|WIN].
- apply SZ.
+ unfold bshadow. rewrite SX. clear -Hx HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
+ intros (bn & Hin & Hr). rewrite SX in Hr. unfold ASHOFF in Hr. unfold both_vis_app in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ cbn [fst snd zv] in Hr;
first [ match reverse goal with NHk : ~ _ |- _ => solve [clear -Hr NHk P208 P209 P0 P10 Hx LOW; Z.div_mod_to_equations; lia] end
| solve [clear -Hr P208 P209 P0 P10 Hx LOW; Z.div_mod_to_equations; lia] ]
| try (match reverse goal with NHk : ~ _ |- _ => clear NHk end) ]).
exact Hin.
- mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
(ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
rewrite SX.
replace (2147450880 + x / 8) with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (x / 8 - 4096 * V 0%nat - 512 * V 10%nat + 1048576))
by (clear; lia).
apply ZW. clear -Hx WIN HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HM HP HU HAT SH0"] Theorem ASECc_init : ASECc [] L (ST0 V) X0 m.
Proof.
split; [exact asec_wf_init|]. split; [exact asec_arr_init|]. split; [exact asec_inst_init|]. split; [exact aprim0_init| exact ashz_init].
Qed.
#[using="Type"] Lemma sec_chunks_of_ST0 : sec_chunks_of (ST0 V) = [].
Proof. unfold sec_chunks_of, achunks, ST0, ainit. cbn. rewrite ?map_to_list_empty. reflexivity. Qed.
#[using="HM HP HU HAT SH0"] Theorem ASEC_of_init : ASEC_of L (ST0 V) X0 m.
Proof. unfold ASEC_of. rewrite sec_chunks_of_ST0. exact ASECc_init. Qed.
End S.
End CANSEC1.
