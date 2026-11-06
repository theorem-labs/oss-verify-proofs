(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1f.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 (cold/h-hpreset-7-r1-memnorm bad7e00334f, 'the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob ede269051fa1); a re-relocation of this file from cgif must be checked against that edit. *)
(* Modified by Theorem Labs, 2026-10: for the world field w_H8 (YA0n), W0 and tfib_AR_init pass W1 the proof H1_H8 of the image-A twin lib/A/PWorldH8.v; tfib_AR_init names its Hve / Hfit / Hch / HC premises to state it (fm's form, origin/cold/port-fm-rtprintf-param 3e35620c52e lib/A/AD1f.v:17, :95-96, :257-272). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD1f.v, with its module paths changed; 33 of its 89 lines of code are new or changed and 220 lines of the source are left out. *)
(* The entry image above the entry sp is readable at main's hand-off, for the cf driver's readable-stack conjunct
   (W8's STKR, CfDriver's HSTKUP): tfib_handoff_stk_up, for every a with usp <= a < ly_top ly0, the hand-off view of W1
   (AD2i.W1 = AD1d.W0, hidden set AD2i.H1) at FULL is defined.  Three facts: ly_top ly0 = uE E eTop is page-aligned and
   at most usp + 3935 (AD1g.v:434 uTop, :988 uTopRel), so it is at most entry_page_top sp bsb, which is page-aligned and
   above usp; H1 is false from TOP up (no stack byte is hidden); and FULL is defined on [usp, entry_page_top), HCOV.
   HCOV is the covered-range fact of StartupTrace's step (2) (a Theorem Labs lane's file, the six-range tiling of the entry image
   from the hand-off's kn rows and argH0's pristine clause with AEntryRead), stated here in that lemma's conclusion form
   as a named Section hypothesis until it lands. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AD1g AD2i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyWorldH8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
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
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation bsb := (build_stack_bytes TPH sp argv envp uid hw rdraw).
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk argv envp uid hw) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a.
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation ly0 := (AD1g.ly0 ch E model).
#[local] Notation H1 := (AD2i.H1 sp rdraw inp ch E model).
Ltac inst H := try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
(* W1 carries the world field w_H8 (Reusable/YA0n.v); its proof at this hand-off state is lib/A/ReplyWorldH8.v's H1_H8. *)
#[local] Definition H1H8 := ltac:(get @ReplyWorldH8.H1_H8).
#[local] Notation W1 := (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1H8).
#[local] Definition uTop := ltac:(get @AD1g.uTop).
#[local] Definition uTopRel := ltac:(get @AD1g.uTopRel).
(* the covered-range fact of StartupTrace's step (2), in its conclusion form *)
Hypothesis HCOV : forall a, usp <= a < entry_page_top sp bsb -> FULL (Z_to_bv 64 a) <> None.
Lemma ly_top_le_page_top : ly_top ly0 <= entry_page_top sp bsb.
Proof.
cbn [ly_top AD1g.ly0]. pose proof uTop as (_ & _ & T2 & T4). pose proof uTopRel as [[T0 T1] _].
pose proof (YP08.length_bsb TPH sp argv envp uid hw rdraw) as LB.
unfold entry_page_top, page_round_up_Z, entry_block_top, page_size.
set (t := uE E AD1g.eTop) in *. set (n := Z.of_nat (length bsb)).
assert (Hn : 1 <= n) by (unfold n; lia).
pose proof (Z.div_mod t 4096 ltac:(lia)) as Dt. rewrite T4, Z.add_0_r in Dt.
pose proof (Z.mul_div_le (usp + n + 4096 - 1) 4096 ltac:(lia)) as M1.
pose proof (Z.div_mod (usp + n + 4096 - 1) 4096 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound (usp + n + 4096 - 1) 4096 ltac:(lia)) as Bm.
nia.
Qed.
Lemma H1_false_high : forall w : word, TOP <= bv_unsigned w -> H1 w = false.
Proof.
intros w Hw. unfold AD2i.H1. destruct (argH E w) eqn:HaH.
- cbn [negb]. rewrite andb_false_r. reflexivity.
- assert (Hh : hid TFIB TOP argH E ch model w = false).
  { unfold hid. rewrite HaH. cbn [orb]. unfold vis. rewrite (proj2 (Z.leb_le _ _) Hw). rewrite orb_true_r. reflexivity. }
  rewrite Hh. reflexivity.
Qed.
Theorem tfib_handoff_stk_up : forall a, usp <= a < ly_top ly0 -> aview tfibsegs (w_H W1) FULL a <> None.
Proof.
intros a Ha. pose proof ly_top_le_page_top as LT. pose proof Hsp as (L & Hh & _). unfold sp_window_lo in L. unfold sp_window_hi in Hh.
pose proof uTop as (_ & _ & T2 & _).
assert (Ha64 : 0 <= a < 2 ^ 64) by (cbn [ly_top AD1g.ly0] in Ha; lia).
pose proof (HCOV a ltac:(lia)) as HF.
assert (HH : w_H W1 (Z_to_bv 64 a) = false).
{ cbn [w_H AD2i.W1]. apply H1_false_high. rewrite u64_lit by lia. unfold YA02.TOP. lia. }
unfold aview, mbyte, mrestrict. rewrite HH.
destruct (FULL (Z_to_bv 64 a)) as [b|]; [discriminate | exfalso; exact (HF eq_refl)].
Qed.
End d.
End c.
