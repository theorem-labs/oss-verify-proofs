(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1f.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 ('the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob ede269051fa1); a re-relocation of this file from cgif must be checked against that edit. *)
(* Modified by Theorem Labs, 2026-10: for the world field w_H8 (YA0n), W0 and tfib_AR_init pass W1 the proof H1_H8 of the image-A twin lib/A/PWorldH8.v; tfib_AR_init names its Hve / Hfit / Hch / HC premises to state it (fm's form, lib/A/AD1f.v:17, :95-96, :257-272). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD1f.v, with its module paths and module names changed; 33 of its 89 lines of code are new or changed and 220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack; the start-up certificate per CONFIG_RSEQ flag with states computed in the build). *)
(* Image B (fuzz_reply.asan-ubsan) twin of lib/A/AStkUp.v, the same text with the B module names (YD1g, YD2i, YB01r,
   YB1v, YF0m, YB12, YB1h, YB13; images AsanUbsan).  The entry image above the entry sp is readable at main's hand-off, for the cf driver's readable-stack conjunct
   (W8's STKR, CfDriver's HSTKUP): tfib_handoff_stk_up, for every a with usp <= a < ly_top ly0, the hand-off view of
   the hidden set YD2i.H1 (W1's, B/YD2i.v) at FULL is defined.  Three facts: ly_top ly0 = uE E eTop is page-aligned and
   at most usp + 3935 (B/YD1g.v uTop, uTopRel), so it is at most the entry page top, which at LPS 727298f3 is the stack
   VMA's end ed_top (Run.v entry_page_top), page-aligned (Run.valid_stack_top_va) and above usp (YP08.head_fits); H1 is
   false from TOP up (no stack byte is hidden); and FULL is defined on [usp, entry_page_top), HCOV (B/YStkCov.v
   entry_stk_cov).
   LPS 727298f3: the Section is the start of B/YD1q.v's drv_mainX_stmt (the hand-off state of the run's own CONFIG_RSEQ
   flag, the invariant abstract with SINV_sp0, the mmap base and the launch premises), as A/AD1pcf.v's handoff_cov, in
   the order of B/YD1pcf.v's inst; the method of curl/fuzz_bufq's lib/R/A/AStkUp.v (ztop_facts, ly_top_le_top). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD1g YD2i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YP08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
Variable SINV : env -> (word -> option byte) -> Prop.
#[local] Notation argH := (YA02.argH0 sp rdraw argv envp
  (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis SINV_sp0 : forall E' M, SINV E' M -> uE E' e_sp0 = TOP + 8388608.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk argv envp
  (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n.
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation ly0 := (YD1g.ly0 ch E model).
#[local] Notation H1 := (YD2i.H1 sp rdraw inp ch E model).
Ltac inst H := try specialize (H fx); try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw);
try specialize (H brk); try specialize (H mbase); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit);
try specialize (H Hvl); try specialize (H Hlau);
try specialize (H h); try specialize (H ch); try specialize (H E); try specialize (H R); try specialize (H FULL);
try specialize (H model); try specialize (H Hch); try specialize (H SINV); try specialize (H SINV_sp0);
try specialize (H HC); try specialize (H HE); try specialize (H rc); try specialize (H Hceil).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
#[local] Definition uTop := ltac:(get @YD1g.uTop).
#[local] Definition uTopRel := ltac:(get @YD1g.uTopRel).
(* the covered-range fact of StartupTrace's step (2), in its conclusion form: the entry image runs from sp to the
   stack VMA's end ed_top = entry_page_top rdraw (B/YStkCov.v entry_stk_cov proves it) *)
Hypothesis HCOV : forall a, usp <= a < entry_page_top rdraw -> FULL (Z_to_bv 64 a) <> None.
(* ed_top is page-aligned (Run.valid_stack_top_va) and above the entry block (YP08.head_fits) *)
Lemma ztop_facts : bv_unsigned (ed_top rdraw) mod 4096 = 0 /\ usp < bv_unsigned (ed_top rdraw).
Proof.
pose proof Hlau as H. cbn [entry_launch_ok_va] in H. destruct H as ((Ha & _ & _) & _).
unfold page_size in Ha. split; [exact Ha|].
pose proof (YP08.head_fits TSEGS TPH inp mbase AsanUbsan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as HF.
lia.
Qed.
Lemma ly_top_le_page_top : ly_top ly0 <= entry_page_top rdraw.
Proof.
unfold entry_page_top.
cbn [ly_top YD1g.ly0]. pose proof uTop as (_ & _ & T2 & T4). pose proof uTopRel as [[T0 T1] _].
pose proof ztop_facts as [Z1 Z2].
set (t := uE E YD1g.eTop) in *. set (z := bv_unsigned (ed_top rdraw)) in *.
pose proof (Z.div_mod t 4096 ltac:(lia)) as Dt. rewrite T4, Z.add_0_r in Dt.
pose proof (Z.div_mod z 4096 ltac:(lia)) as Dz. rewrite Z1, Z.add_0_r in Dz.
lia.
Qed.
Lemma H1_false_high : forall w : word, TOP <= bv_unsigned w -> H1 w = false.
Proof.
intros w Hw. unfold YD2i.H1. destruct (argH E w) eqn:HaH.
- cbn [negb]. rewrite andb_false_r. reflexivity.
- assert (Hh : hid TFIB TOP argH E ch model w = false).
  { unfold hid. rewrite HaH. cbn [orb]. unfold vis. rewrite (proj2 (Z.leb_le _ _) Hw). rewrite orb_true_r. reflexivity. }
  rewrite Hh. reflexivity.
Qed.
(* W1's hidden set is H1 (B/YD2i.v W1 := mkW TSEGS H1 ...): stated over H1, so the driver's W1 (B/YD1pcf.v W1h, with
   its own w_H8 proof) is met by conversion *)
Theorem tfib_handoff_stk_up : forall a, usp <= a < ly_top ly0 -> aview tfibsegs H1 FULL a <> None.
Proof.
intros a Ha. pose proof ly_top_le_page_top as LT. pose proof Hsp as (L & Hh & _). unfold sp_window_lo in L. unfold sp_window_hi in Hh.
pose proof uTop as (_ & _ & T2 & _).
assert (Ha64 : 0 <= a < 2 ^ 64) by (cbn [ly_top YD1g.ly0] in Ha; lia).
pose proof (HCOV a ltac:(lia)) as HF.
assert (HH : H1 (Z_to_bv 64 a) = false).
{ apply H1_false_high. rewrite u64_lit by lia. unfold YA02.TOP. lia. }
unfold aview, mbyte, mrestrict. rewrite HH.
destruct (FULL (Z_to_bv 64 a)) as [b|]; [discriminate | exfalso; exact (HF eq_refl)].
Qed.
End d.
End c.
