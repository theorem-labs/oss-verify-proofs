(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1d.v, with its module paths changed; its addresses are still cgif_file_fuzzer.asan's. *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 (cold/h-hpreset-7-r1-memnorm bad7e00334f, 'the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob 49d6c2c40197); a re-relocation of this file from cgif must be checked against that edit. *)
(* Modified by Theorem Labs, 2026-10: for the world field w_H8 (YA0n), W1 takes the proof H1_H8 of the image-A twin lib/A/PWorldH8.v (fm's form, origin/cold/port-fm-rtprintf-param 3e35620c52e lib/A/AD1d.v:16, :230-231, :235); W0 and tfib_AI pass it as H1H8. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD1d.v, with its module paths and module names changed; 45 of its 82 lines of code are new or changed and 275 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: new file, the fuzz_reply.asan-ubsan instance of the stack-presence fact, the B twin
   of lib/A/AStkPres.v section 4 (RelocA-2, a working branch bc0fb577043): tfib_handoff_stk_pres
   discharges Reusable/YStkPres.v's stk_pres at each of fuzz_reply.asan-ubsan's 50 hand-off states (B/YB01.v), for W1's
   hidden set B/YD2i.v H1 (:507), over [usp - stack_max_size, usp): B/YD2i.v:79 KWR_STACK is known in every hand-off
   state (kwr_stack_all, vm_compute), and H1 is false from TOP up (H1_false_high). The generic construction is
   Reusable/YStkPres.v (carried by path from the same ref), re-exported here.
   Not covered, as on A: [usp, ly_top), the entry image above the entry sp (at most 3935 bytes, B/YD1g.v:989 uTopRel):
   the hand-off certificate states only its argH0 part. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP0m YP09 YP0l YP08 YP03 YN3q YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK1b YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Export YStkPres.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01 YD2j YD2i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YD1h.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* ---- 4. fuzz_reply.asan-ubsan's hand-off states ---- *)
Lemma kwr_stack_all : forallb (kn_mem KWR_STACK) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma kwr_stack_hs : forall h ch, HS_tfib h = Some ch -> kn_mem KWR_STACK ch = true.
Proof. intros h ch Hh. exact (proj1 (forallb_forall _ _) kwr_stack_all ch (HS_tfib_In h ch Hh)). Qed.
Lemma tfib_seg_none_high : forall a, KHI <= a < 2 ^ 64 -> find_segment TSEGS a 1 = None.
Proof.
intros a Ha. unfold KHI in Ha. pose proof (tfib_in_hull (Z_to_bv 64 a)) as X. rewrite u64_lit in X by lia. apply X.
unfold APSG.in_hull. cbn [img_lo img_hi TFIB]. unfold KHI. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Section t. Context {fx : YK11.FPState}.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
Hypothesis HC : cs_ok TSEGS TFIB YA02.LIMIT TOP SINV argH (in_fs inp) E ch R FULL model.
#[local] Notation usp := (bv_unsigned sp).
Lemma tfib_uS0 : uE E eSp0 = usp.
Proof.
pose proof (YA02.SINV0_sp0 TSEGS TPH sp rdraw brk argv envp uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as X.
rewrite eSp0_e_sp0. unfold YA02.TOP in X. lia.
Qed.
Lemma H1_false_high : forall w : word, TOP <= bv_unsigned w -> YD2i.H1 sp rdraw inp ch E model w = false.
Proof.
intros w Hw. unfold YD2i.H1. destruct (argH E w) eqn:HaH.
- cbn [negb]. rewrite andb_false_r. reflexivity.
- assert (Hh : hid TFIB TOP argH E ch model w = false).
  { unfold hid. rewrite HaH. cbn [orb]. unfold vis. rewrite (proj2 (Z.leb_le _ _) Hw). rewrite orb_true_r. reflexivity. }
  rewrite Hh. reflexivity.
Qed.
Theorem tfib_handoff_stk_pres : stk_pres (usp - stack_max_size) usp (YD2i.H1 sp rdraw inp ch E model) FULL.
Proof.
pose proof tfib_uS0 as U. pose proof Hsp as (L & Hh & _). unfold sp_window_lo in L. unfold sp_window_hi in Hh.
change stack_max_size with 8388608. replace (usp - 8388608) with TOP by (unfold YA02.TOP; lia). rewrite <- U.
apply (handoff_stk_pres TSEGS TFIB YA02.LIMIT TOP SINV argH (in_fs inp) E ch R FULL model HC eSp0 (kwr_stack_hs h ch Hch)).
- unfold YA02.TOP. lia.
- unfold YA02.TOP. lia.
- intros a Ha. apply tfib_seg_none_high. unfold YA02.TOP in Ha. unfold KHI. lia.
- exact H1_false_high.
Qed.
(* the wider range [usp - stack_max_size, hi) for any hi, given the start-up kit's fact that the hand-off memory holds
   every byte of the entry image [usp, hi) above the entry sp (as lib/A/AStkPres.v, RelocA-2 cc22b97d81f). The hidden
   set is false there already (H1_false_high). *)
Theorem tfib_handoff_stk_pres_to : forall hi, hi <= 2 ^ 64 ->
  (forall a, usp <= a < hi -> FULL (Z_to_bv 64 a) <> None) ->
  stk_pres (usp - stack_max_size) hi (YD2i.H1 sp rdraw inp ch E model) FULL.
Proof.
intros hi Hhi HK. apply (stk_pres_extend _ usp hi _ _ tfib_handoff_stk_pres).
intros a Ha. split; [| exact (HK a Ha)].
pose proof Hsp as (L & Hh & _). unfold sp_window_lo in L. unfold sp_window_hi in Hh.
apply H1_false_high. rewrite u64_lit by lia. unfold YA02.TOP. lia.
Qed.
End t.
