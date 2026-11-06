(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe Stdio Malloc Adapter Driver PState Prog KInv KStep StepB EquivK_iface
MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Init LB_Alloc LB_PCaps LB_Hist LB_PAmb LB_PStdio LB_PTarget Gap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import ImgFacts.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Lemma OK_firstQ : malokA [] 65536.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=48758803375.060190386007.0000001002SS".
refine (malokA_amb0 65536 [] AMBZ_nil ltac:(cbn; lia) _). lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma OK_growQ : forall b k, (k <= 9)%nat -> malokA [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
intros b k Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0080=21043279776.528200658343.53047227532.5 41415984013.441415986323.34361585318.4 49158302072.35926763833.5 00000:00>00H00L00P00T00X00\S2Hk2Hq2HpS2HkS2Hk2Hq2HpS2HkS2HkS2HkS2HkS2Hk".
pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as Hq.
assert (Hp : 2 ^ Z.of_nat k <= 512). { change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia. }
refine (malokA_amb0 _ [(b, 65536 * 2 ^ Z.of_nat k)] _ _ _); [| cbn; lia| lia].
apply AMBZ_cons; [apply AMBZ_nil| cbn; lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma prog_with_Q : forall rs argv, mspecL LBUDGET (Qamb []) (prog_with rs argv) (fun _ _ _ => False).
Proof.
intros rs argv. unfold prog_with.
eapply mspecL_seq; [apply (startup_L LBUDGET (Qamb [])); [apply Qamb_minv| apply Qamb_fds| apply Qamb_live]|]. intros _.
eapply mspecL_bind.
- apply (main_model_L LBUDGET io raw_malloc raw_free rs alloc_init run alloc_count Qamb Qrun Qamb_Qrun malokA).
+ intros X n Hn. apply malloc_Qamb. exact Hn.
+ intros X p n. apply free_Qamb.
+ intros X p n. apply free_Qrun.
+ intros X Y s mo HP. apply Qamb_perm. exact HP.
+ intros X d. cbn [io io_diag io_S]. apply (s_diag_L LBUDGET (Qamb X) (Qamb_live X)).
+ intros X bm. unfold alloc_init, target_alloc_init. apply mspecL_ret. intros s mo H; exact H.
+ intros X. unfold alloc_count, target_alloc_count. apply mspecL_ret. intros s mo H; exact H.
+ exact run_Q.
+ intros X s mo H. exact (Qamb_minv _ _ _ H).
+ intros X s mo mo' H. exact (Qamb_fds _ _ _ _ H).
+ intros X s mo H. exact (Qamb_live _ _ _ H).
+ exact OK_firstQ.
+ exact OK_growQ.
- intros code. cbn beta. apply (exit_model_L' LBUDGET io Qrun).
intros X. cbn [io io_exit io_S]. apply (stdout_exit_flush_L LBUDGET (Qrun X) (Qrun_live X) (Qrun_so X)).
Qed.
Theorem live_bound_nf : forall segs rs pc ph lim en inp,
0 < reserved_top (segments_reserved segs) ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
tlive LBND (Prog.prog segs rs inp en) (mo0 segs lim en inp) /\ tnf (Prog.prog segs rs inp en) (mo0 segs lim en inp).
Proof.
intros segs rs pc ph lim [sp brk0 mbase dr] inp Hpos Hceil Hfloor Hresv Hlim Hve Hvi.
rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hvi) in Hve. destruct Hve as ((HspL & HspH & _) & Hbrk & _ & _).
unfold prog, prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp].
change LBND with LBUDGET.
apply (mspecL_program LBUDGET (Qamb []) (prog_with rs (argv_Z (in_argv inp))) (fun _ _ _ => False)).
- apply prog_with_Q.
- unfold Qamb. apply QI_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil| exact Hfloor| exact Hresv| exact Hlim| exact Pamb_nonneg| exact Pamb_ok| exact PHI_Pamb].
- intros [].
Qed.
Theorem never_forced : forall segs rs pc ph lim en inp,
0 < reserved_top (segments_reserved segs) ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
tnf (Prog.prog segs rs inp en) (mo0 segs lim en inp).
Proof. intros. eapply live_bound_nf; eauto. Qed.
Theorem never_forced_p_L : forall L rs en inp, 2^31 <= L ->
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
tnf (Prog.prog psegs rs inp en) (mo0 psegs L en inp).
Proof. intros L rs en inp HL He Hi. apply (never_forced psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| exact HL| exact He| exact Hi]. Qed.
